From Utils Require Import Defns Smallstep Behaviours.
From RTLT  Require Import Language Policy.
                   Import ListNotations.
Set Implicit Arguments.
Local Open Scope type_scope.

Module Functor (Import Tags  : TagDomain.MiddleEnd)
               (Import Rules : RTLT.Policy.Sig Tags)
               (Import Lang  : RTLT.Language.Sig Tags).

Create HintDb rtlDB.

Definition atom := val * ValTag.
Definition toAtom : lit -> atom := id.
Hint Unfold toAtom : rtlDB.
Definition defAtom : atom := toAtom defLit.

Definition regbank := Regmap.t atom.
Definition genv := PTree.t function.

Inductive stack : Type :=
  | SretTR :
      forall (cees_en_pct : PCTag),
      stack -> stack
  | Stackframe:
      forall (dest_in_caller     : reg)
             (caller             : function)
             (pc_after_callsite  : node)
             (callers_rb         : regbank)
             (stk                : stack),
      stack
  | Stknil : stack.

Inductive state : Type :=
  | State : forall
        (curr_fn  : function)
        (curr_pc  : node    )
        (curr_pct : PCTag   )
        (B        : regbank )
        (cs       : stack   ),
      state
  | Callstate : forall
        (cee      : function )
        (args     : list atom)
        (curr_pct : PCTag    )
        (cs       : stack    ),
      state
  | Returnstate : forall
        (ret_atm : atom )
        (ret_pct : PCTag)
        (cs      : stack),
      state
  | Errorstate : TagErr -> state.


Fixpoint init_regs (al: list atom) (rs: list reg) {struct rs} : regbank :=
  match rs, al with
  | r :: rs, a :: al => Regmap.set r a (init_regs al rs)
  | _, _ => Regmap.init defAtom
  end.

Definition getTag (B:regbank) (r:reg) : ValTag :=
  match B # r with
  | (_, t) => t
  end.

Fixpoint getTags (B:regbank) (rs:list reg) : list ValTag :=
  match rs with
  | hd :: tl => match B # hd with
                | (_, t) => t :: getTags B tl
                end
  | []       => []
  end.


Section RELSEM.
(* Local Notation "B ^  r"  := (getTag B r). *)
Local Notation "B ^^ rs" := (getTags B rs) (at level 3).
Variable ge: genv.
Inductive step: state -> state -> Prop :=

  | exec_Inop : forall f pc p B cs pc' p' itag,
      f.(body)!pc = Some(Inop pc',itag) ->
      InopTR itag p = inl p' ->
      step (State f pc  p  B cs)
           (State f pc' p' B cs)

  | exec_Inop_err : forall f pc p cs B pc' itag err,
      f.(body)!pc = Some(Inop pc',itag) ->
      InopTR itag p = inr err ->
      step (State f pc  p  B cs)
           (Errorstate err)


  | exec_Imov : forall f pc p cs B pc' p' rd vs
                       pv' rs itag vps xx vpd,
      f.(body)!pc = Some(Imov rs rd pc', itag) ->
      B#rs = (vs, vps) ->
      B#rd = (xx, vpd) ->
      ImovTR itag p vps vpd = inl (p', pv') ->
      step (State f pc  p   B                  cs)
           (State f pc' p' (B#rd <- (vs, pv')) cs)

  | exec_Imov_err : forall f pc p cs B err rs rd
                           pc' itag vs vps xx vpd,
      f.(body)!pc = Some(Imov rs rd pc', itag) ->
      B#rs = (vs, vps) ->
      B#rd = (xx, vpd) ->
      ImovTR itag p vps vpd = inr err ->
      step (State f pc  p   B                  cs)
           (Errorstate err)


  | exec_Imovi : forall f pc p cs B pc' p'
                        rd v t' l t itag,
      f.(body)!pc = Some (Imovi l rd pc', itag) ->
      toAtom l = (v, t) ->
      ImoviTR itag p t = inl (p', t') ->
      step (State f pc  p   B                cs)
           (State f pc' p' (B#rd <- (v, t')) cs)

  | exec_Imovi_err : forall f pc p cs B err
                            pc' rd v l t itag,
      f.(body)!pc = Some (Imovi l rd pc', itag) ->
      toAtom l = (v, t) ->
      ImoviTR itag p t = inr err ->
      step (State f pc  p   B                cs)
           (Errorstate err)


  | exec_Iop : forall f pc p B cs pc' p' rd v t'
                      op r1 r2 itag v1 t1 v2 t2,
      f.(body)!pc = Some(Iop op r1 r2 rd pc', itag) ->
      B#r1 = (v1, t1) ->
      B#r2 = (v2, t2) ->
      IopTR itag p op t1 t2 = inl (p', t') ->
      v = eval_op op v1 v2 ->
      step (State f pc  p   B                cs)
           (State f pc' p' (B#rd <- (v, t')) cs)

  | exec_Iop_err : forall f pc p cs B err op r1 r2
                          rd pc' itag v1 t1 v2 t2,
      f.(body)!pc = Some(Iop op r1 r2 rd pc', itag) ->
      B#r1 = (v1, t1) ->
      B#r2 = (v2, t2) ->
      IopTR itag p op t1 t2 = inr err ->
      step (State f pc  p  B                 cs)
           (Errorstate err)


  | exec_Icond : forall f pc p cs B pc' p' c r1 r2
                        nt nf itag v1 t1 v2 t2 b,
      f.(body)!pc = Some(Icond c r1 r2 nt nf, itag) ->
      B#r1 = (v1, t1) ->
      B#r2 = (v2, t2) ->
      eval_comp c v1 v2 = b ->
      IcondTR itag p c t1 t2 = inl p' ->
      pc' = (if b then nt else nf) ->
      step (State f pc  p  B cs)
           (State f pc' p' B cs)

  | exec_Icond_err : forall f pc p cs B err c r1 r2
                            nt nf itag v1 t1 v2 t2 b,
      f.(body)!pc = Some(Icond c r1 r2 nt nf, itag) ->
      B#r1 = (v1, t1) ->
      B#r2 = (v2, t2) ->
      eval_comp c v1 v2 = b ->
      IcondTR itag p c t1 t2 = inr err ->
      step (State f pc  p  B cs)
           (Errorstate err)


  | exec_Icall : forall p_en_cee cer pc p cs B cee
                        args rx pc' cee_id itag ts,
      cer.(body)!pc = Some(Icall cee_id args rx pc', itag) ->
      ge ! cee_id = Some cee ->
      cee.(arity) = length args ->
      B^^args =  ts ->
      IcallTR itag p cee.(fntag) ts = inl p_en_cee ->
      step (State cer pc p B cs)
           (Callstate cee (B##args) p_en_cee
                      (SretTR p_en_cee (Stackframe rx cer pc' B cs)))

  | exec_Icall_err : forall cer pc p cs B err cee_id
                            args rx pc' itag cee ts,
      cer.(body)!pc = Some(Icall cee_id args rx pc', itag) ->
      ge ! cee_id = Some cee ->
      cee.(arity) = length args ->
      B^^args = ts ->
      IcallTR itag p cee.(fntag) ts = inr err ->
      step (State cer pc p B cs)
           (Errorstate err)



  | exec_pass_control:
      forall cee args p_en cs,
      step (Callstate cee args p_en cs)
           (State cee
                  cee.(entrypoint)
                  p_en
                  (init_regs args cee.(params))
                  cs
           )



  | exec_Ireturn : forall f pc p p_en cs B
                          atm p' r itag v t,
      f.(body)!pc = Some(Ireturn r, itag) ->
      B#r = atm ->
      atm = (v,t) ->
      IreturnTR itag p p_en t = inl p' ->
      step (State f pc p B (SretTR p_en cs))
           (Returnstate atm p' cs)

  | exec_Ireturn_err : forall f pc p cs B err r
                              itag atm v t p_en,
      f.(body)!pc = Some(Ireturn r, itag) ->
      B#r = atm ->
      atm = (v,t) ->
      IreturnTR itag p p_en t = inr err ->
      step (State f pc p B (SretTR p_en cs))
           (Errorstate err)

(** [exec_return] then pops a stack frame from the call stack, which contains
    the following pieces of information:
-   The (previously) caller, that we are now returning to
-   The return address, i.e. the PC we need to jump to
-   The destination register

    [exec_return] then (re)starts executing the caller from the return address
    while updating the destination register to have the return value. *)



  | exec_return_control : forall atm p rx f
                                 B pc cs v t,
      atm = (v,t) ->
      step (Returnstate atm p (Stackframe rx f pc B cs))
           (State f pc p (B#rx <- atm) cs).



End RELSEM. 

(** We define states that programs can start and end with. *)
(** Programs can only start in a [Callstate] where: The program has a
    main function (recall, this must be the first function in the program)
    that takes no arguments and where the callstack is empty. *)


Inductive initial_state (p : program) : state -> Prop :=
  | initial_state_intro : forall id f,
      List.hd_error p = Some (id,f) ->
      initial_state p (Callstate f [] initPCT Stknil).

(** Programs can only legally terminate in a [Returnstate] with an "empty" callstack. *)

Inductive final_state: state -> atom -> Prop :=
  | final_state_intro: forall a rpct,
      final_state (Returnstate a rpct Stknil) a.

Inductive error_state: state -> TagErr -> Prop :=
  | error_state_intro: forall e,
      error_state (Errorstate e) e.

Fixpoint mkge (prog:program) : genv :=
  match prog with
  | (i,f) :: p => PTree.set i f (mkge p)
  | []         => PTree.empty function
  end.


Remark RTLT_semantics (p: program) : semantics.
Proof.
  refine (@Semantics_gen
    state
    genv
    atom
    TagErr
    step
    (initial_state p)
    final_state
    error_state
    ltac:(intros [] * [X Y]; solve [inv X|inv Y])
    (mkge p)).
Defined.

Section Determinacy.

Ltac lookup_same :=
  match goal with
  | A: ?x = ?y,
    B: ?x = ?z
    |- _ => rewrite A in B; (try solve [inversion B]);
            injection B; clear A B; intros **; subst;
            (try solve [auto]); lookup_same
  | _ => auto
  end.

Remark deterministic : forall p,
  determinate (RTLT_semantics p).
Proof with solve [eauto | lookup_same].
  intros p. refine (@Determinate _ _ _ _ _ _ _).
  - (* sd_determ *)
    induction 1; intros STEP2; inv STEP2...
  - (* sd_initial_determ *)
    do 2 inversion 1...
  - (* sd_final_nostep *)
    intros * [] ? ?. inv H.
  - (* sd_final_determ *)
    do 2 inversion 1...
  - (* sd_error_nostep *)
    intros * A s' B. inv A. inv B.
  - (* sd_error_determ *)
    do 2 inversion 1...
Qed.

End Determinacy.

End Functor.


Module Type Sig (Import Tags  : TagDomain.MiddleEnd)
                (Import Rules : RTLT.Policy.Sig Tags)
                (Import Lang  : RTLT.Language.Sig Tags).
Include Functor Tags Rules Lang.
End Sig.

Local Close Scope type_scope.