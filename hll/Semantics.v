From Utils  Require Import Defns Smallstep Behaviours.
From HLL    Require Import Language Policy.
                    Import ListNotations.
Set Implicit Arguments.
Local Open Scope type_scope.

Module Functor (Import Tags  : TagDomain.FrontEnd)
               (Import Rules : HLL.Policy.Sig Tags)
               (Import Lang  : HLL.Language.Sig Tags).

Create HintDb whilefDB.

Definition atom := val * ValTag.
Definition toAtom : lit -> atom := id.
Hint Unfold toAtom : whilefDB.
Definition defAtom : atom := toAtom defLit.


Definition env  := PTree.t atom.       (* for locals and variables *)
Definition genv := PTree.t function.   (* for functions *)

Inductive local_cont: Type :=
  | Kseq: stmt -> local_cont -> local_cont       (**r execute stmt, then cont *)
  | Kjoin : (forall (ex en: PCTag), M PCTag) -> PCTag -> local_cont -> local_cont
  | Kemp : local_cont.

(* call stacks *)
Inductive call_cont : Type :=
  | Kstop: call_cont (* empty stack *)
  | KreturnTo :
      forall (caller_dest_var : ident     )
             (caller          : function  )
             (callers_env     : env       )
             (lk              : local_cont)
             (callsite        : call_cont ),
      call_cont
  | KretTR: PCTag -> call_cont -> call_cont.


Inductive state: Type :=
  | State :
      forall (curr_fn   : function  )
             (curr_stmt : stmt      )
             (lk        : local_cont)
             (curr_pct  : PCTag     )
             (E         : env       )
             (callstack : call_cont ),
      state
  | Callstate :
      forall (callee      : function )
             (args_to_cee : list atom)
             (cee_init    : PCTag    )
             (ck          : call_cont),
      state
  | Returnstate :
      forall (ret_atm : atom     )
             (ret_pct : PCTag    )
             (ck      : call_cont),
      state
  | Errorstate: TagErr -> state.



Section EVAL_EXPR.
Variable (E: env) (p: PCTag).

Definition embed (v: val) (m: M ValTag) : M atom :=
  bind m (fun vt => ret (v,vt)).

Inductive eval_expr : expr ->
                      M atom -> Prop :=
  | eval_Elit: forall l v vt,
      toAtom l = (v, vt) ->
      eval_expr (Elit l)   (embed v (constTR p vt))

  | eval_Evar: forall id v vt,
      E ! id = Some (v,vt) ->
      eval_expr (Evar id)   (embed v (varTR p vt))

  | eval_Eop : forall op e1 e2 v1 v2 vt1 vt2,
      eval_expr e1   (ret (v1,vt1)) ->
      eval_expr e2   (ret (v2,vt2)) ->
      eval_expr (Eop op e1 e2)   (embed (eval_op op  v1  v2)
                                        (opTR op p  vt1 vt2))

  | eval_Eop_errl : forall op e1 e2 err,
      eval_expr         e1       (fstop err) ->
      eval_expr (Eop op e1 e2)   (fstop err)

  | eval_Eop_errr : forall op e1 e2 v1 vt1 err,
      eval_expr         e1       (ret (v1,vt1)) ->
      eval_expr            e2    (fstop err) ->
      eval_expr (Eop op e1 e2)   (fstop err).

Inductive eval_exprlist : list expr ->
                          M (list atom) -> Prop :=
  | eval_EList_nil : eval_exprlist []   (inl [])
  | eval_EList_cons : forall e es v t ts,
      eval_expr      e        (ret (v,t)) ->
      eval_exprlist     es    (ret    ts) ->
      eval_exprlist (e::es)   (ret ((v,t) :: ts))
  | eval_EList_cons_errh : forall e es err,
      eval_expr      e        (fstop err) ->
      eval_exprlist (e::es)   (fstop err)
  | eval_EList_cons_errt : forall e es err atm,
      eval_expr      e        (ret atm) ->
      eval_exprlist     es    (fstop err) ->
      eval_exprlist (e::es)   (fstop err).

End EVAL_EXPR.

Fixpoint set_params (params: list ident) (vargs: list atom) : env :=
  match params, vargs with
  | i :: is, v :: vs => PTree.set i v (set_params is vs)
  | _, _             => @PTree.empty atom
  end.

Fixpoint set_locals (locals: list ident) (E: env) : env :=
  match locals with
  | x :: xs => PTree.set x defAtom (set_locals xs E)
  | _       => E
  end.

Definition getTag (E:env) (x:ident) : option ValTag :=
  match E ! x with
  | Some (_,t) => Some t
  | None       => None
  end.

Section SmStep.
Local Notation "E ^ x" := (getTag E x).


Variable ge: genv.
Inductive step : state -> state -> Prop :=

  (* Sequencing steps *)
  | step_seq : forall f s1 s2 p lk ck E,
      step (State f (Sseq s1 s2) lk p E ck)
           (State f s1 (Kseq s2 lk) p E ck)


  | step_skip_seq : forall f p s lk ck E,
      step (State f Sskip (Kseq s lk) p E ck)
           (State f s lk p E ck)



  (* Join point steps (local) *)
  | step_skip_join : forall f p rule lk ck E ps p',
      rule p ps = ret p' ->
      step (State f Sskip (Kjoin rule ps lk) p  E ck)
           (State f Sskip                lk  p' E ck)

  | step_skip_join_err : forall f p rule lk ck E err ps,
      rule p ps = fstop err ->
      step (State f Sskip (Kjoin rule ps lk) p  E ck)
           (Errorstate err)



  (* Assignment steps *)
  | step_assign : forall f x a p lk ck E p' v t' tx t,
      eval_expr E p a   (ret (v,t)) ->
      E ^ x = Some tx ->
      assignTR p tx t = ret (p', t') ->
      step (State f (Sassign x a) lk p   E                ck)
           (State f  Sskip        lk p' (E ! x <- (v,t')) ck)

  | step_assign_expr_err : forall f x a p lk ck E err,
      eval_expr E p a   (fstop err) ->
      step (State f (Sassign x a) lk p   E                ck)
           (Errorstate err)

  | step_assign_rule_err : forall f x a p lk ck E err v t tx,
      eval_expr E p a   (ret (v,t)) ->
      E ^ x = Some tx ->
      assignTR p tx t = inr err ->
      step (State f (Sassign x a) lk p   E                 ck)
           (Errorstate err)



  (* Conditional steps *)
  | step_ifthenelse : forall f c a1 a2 s1 s2 p lk
                             ck E b p' v1 t1 v2 t2,
      eval_expr E p a1   (ret (v1,t1)) ->
      eval_expr E p a2   (ret (v2,t2)) ->
      eval_comp c v1 v2 = b ->
      ifSTR p c t1 t2 = ret p' ->
      step (State f (Sifthenelse c a1 a2 s1 s2)                 lk  p  E ck)
           (State f (if b then s1 else s2)       (Kjoin ifJTR p lk) p' E ck)

  | step_ifthenelse_errl : forall f c a1 a2 s1 s2
                                  p lk ck E err,
      eval_expr E p a1   (fstop err) ->
      step (State f (Sifthenelse c a1 a2 s1 s2)                 lk  p  E ck)
           (Errorstate err)

  | step_ifthenelse_errr : forall f c a1 a2 s1 s2 p
                                  lk ck E err v1 vt1,
      eval_expr E p a1   (ret (v1,vt1)) ->
      eval_expr E p a2   (fstop  err) ->
      step (State f (Sifthenelse c a1 a2 s1 s2)                 lk  p  E ck)
           (Errorstate err)

  | step_ifthenelse_rule_err : forall f c a1 a2 s1 s2 p lk
                                      ck E err v1 t1 v2 t2 b,
      eval_expr E p a1   (ret (v1,t1)) ->
      eval_expr E p a2   (ret (v2,t2)) ->
      eval_comp c v1 v2 = b ->
      ifSTR p c t1 t2 = fstop err ->
      step (State f (Sifthenelse c a1 a2 s1 s2)                 lk  p  E ck)
           (Errorstate err)



  (* While steps *)
  | step_while_true  : forall f c a1 a2 body p lk
                              ck E p' v1 vt1 v2 vt2,
      eval_expr E p a1   (ret (v1,vt1)) ->
      eval_expr E p a2   (ret (v2,vt2)) ->
      eval_comp c v1 v2 = true ->
      wNTR p c vt1 vt2 = ret p' ->
      step (State f (Swhile c a1 a2 body) lk p E ck)
           (State f body (Kjoin wLTR p
                         (Kseq (Swhile c a1 a2 body) lk)) p' E ck)

  | step_while_false : forall f c a1 a2 body p lk
                              ck E p1 p' v1 t1 v2 t2,
      eval_expr E p a1   (ret (v1,t1)) ->
      eval_expr E p a2   (ret (v2,t2)) ->
      eval_comp c v1 v2 = false ->
      wNTR p c t1 t2 = ret p1 ->
      wXTR p1 p = ret p' ->
      step (State f (Swhile c a1 a2 body) lk p  E ck)
           (State f  Sskip                lk p' E ck)

  | step_while_expr_errl : forall f c a1 a2 body
                                  p lk ck E err,
      eval_expr E p a1   (fstop err ) ->
      step (State f (Swhile c a1 a2 body) lk p  E ck)
           (Errorstate err)

  | step_while_expr_errr : forall f c a1 a2 body p
                                  lk ck E err v1 vt1,
      eval_expr E p a1   (ret (v1,vt1)) ->
      eval_expr E p a2   (fstop err) ->
      step (State f (Swhile c a1 a2 body) lk p  E ck)
           (Errorstate err)

  | step_while_rule_err : forall f c a1 a2 body p lk ck
                                 E err b v1 vt1 v2 vt2,
      eval_expr E p a1   (ret (v1,vt1)) ->
      eval_expr E p a2   (ret (v2,vt2)) ->
      eval_comp c v1 v2 = b ->
      wNTR p c vt1 vt2 = fstop err ->
      step (State f (Swhile c a1 a2 body) lk p  E ck)
           (Errorstate err)

  | step_while_false_err : forall f c a1 a2 body p lk
                              ck E err p1 v1 vt1 v2 vt2,
      eval_expr E p a1   (ret (v1,vt1)) ->
      eval_expr E p a2   (ret (v2,vt2)) ->
      eval_comp c v1 v2 = false ->
      wNTR p c vt1 vt2 = ret p1 ->
      wXTR p1 p = fstop err ->
      step (State f (Swhile c a1 a2 body) lk p  E ck)
           (Errorstate err)



  (* Call steps *)

  (* ge lookup & eval of params : state -> callstate *)
  | step_call : forall cer var_id cee_id bl p lk ck
                       E args cee p_en vals tags,
      eval_exprlist E p bl   (ret args)->
      ge ! cee_id = Some cee ->
      cee.(arity) = length args ->
      split args = (vals,tags) ->
      callTR p cee.(fntag) tags = ret p_en ->
      step (State cer (Scall var_id cee_id bl) lk p E ck)
           (Callstate cee args p_en
                      (KretTR p_en
                      (KreturnTo var_id cer E lk ck)))

  | step_call_args_err : forall cer var_id cee_id
                                bl p lk ck E err ,
      eval_exprlist E p bl   (fstop err)->
      step (State cer (Scall var_id cee_id bl) lk p E ck)
           (Errorstate err)

  | step_call_rule_err : forall cer var_id cee_id bl p lk
                                ck E err args cee vals tags,
      eval_exprlist E p bl   (inl args)->
      ge ! cee_id = Some cee ->
      cee.(arity) = length args ->
      split args = (vals,tags) ->
      callTR p cee.(fntag) tags = inr err ->
      step (State cer (Scall var_id cee_id bl) lk p E ck)
           (Errorstate err)


  (* initial environment : callstate -> state *)
  | step_pass_control: forall f atms p_en ck E,
      set_locals f.(locals) (set_params f.(params) atms) = E ->
      step (Callstate f atms p_en ck)
           (State f f.(body) Kemp p_en E ck)





  (* Return steps *)

  (* fall through *)
  | step_skip_return : forall f p_ex p_en ck E atm p',
      retTR p_ex p_en defVT = ret p' ->
      atm = defAtom ->
      step (State f Sskip Kemp p_ex E (KretTR p_en ck))
           (Returnstate atm p' ck)

  | step_skip_return_err : forall f p_ex p_en ck E err,
      retTR p_ex p_en defVT = fstop err ->
      step (State f Sskip Kemp p_ex E (KretTR p_en ck))
           (Errorstate err)


  (* early return *)
  | step_return : forall f a p_ex lk p_en ck E atm p' v vt,
      eval_expr E p_ex a   (ret atm) ->
      atm = (v,vt) ->
      retTR p_ex p_en vt = ret p' ->
      step (State f (Sreturn a) lk p_ex E (KretTR p_en ck))
           (Returnstate atm p' ck)

  | step_return_expr_err : forall f a p_ex lk p_en ck E err,
      eval_expr E p_ex a   (fstop err) ->
      step (State f (Sreturn a) lk p_ex E (KretTR p_en ck))
           (Errorstate err)

  | step_return_rule_err : forall f a p_ex lk p_en ck E err atm v vt,
      eval_expr E p_ex a   (ret atm) ->
      atm = (v,vt) ->
      retTR p_ex p_en vt = fstop err ->
      step (State f (Sreturn a) lk p_ex E (KretTR p_en ck))
           (Errorstate err)



  | step_return_control : forall atm p x f E lk ck v vt,
      atm = (v,vt) ->
      step (Returnstate atm p (KreturnTo x f E lk ck))
           (State f Sskip lk p (E ! x <- atm) ck).

End SmStep.


Fixpoint mkge (prog:program) : genv := 
  match prog with
  | (fid,f) :: p => PTree.set fid f (mkge p)
  | []           => PTree.empty function
  end.

Inductive initial_state (p : program) : state -> Prop :=
  | initial_state_intro : forall main_id main,
      List.hd_error p = Some (main_id,main) ->
      initial_state p (Callstate main [] initPCT Kstop).


Inductive final_state : state -> atom -> Prop :=
  | final_state_intro : forall a p,
      final_state (Returnstate a p Kstop) a.

Inductive error_state : state -> TagErr -> Prop :=
  | error_state_intro : forall e,
      error_state (Errorstate e) e.



Remark HLL_semantics (p: program) : semantics.
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
    ltac:(intros [] * [A B]; solve [inv A|inv B])
    (mkge p)).
Defined.





Section Determinacy.

Lemma eval_expr_det:
  forall {e pct a Mat Mat'},
  eval_expr e pct a   Mat  ->
  eval_expr e pct a   Mat' ->
    Mat = Mat'.
Proof with auto.
  intros * A. revert Mat'. induction A;
  intros Mat' B; inversion B; subst...
  - rewrite H in H1. inv H1...
  - rewrite H in H1. inv H1...
  - injection (IHA1 _ H3) as <- <-.
    injection (IHA2 _ H4) as <- <-...
  - now (pose proof (IHA1 _ H3)).
  - now (pose proof (IHA2 _ H4)).
  - now (pose proof (IHA  _ H3)).
  - now (pose proof (IHA  _ H3)).
  - now (pose proof (IHA2 _ H4)).
  - now (pose proof (IHA1 _ H3)).
Qed. (* Hint Resolve eval_expr_det : srcDet. *)

Lemma eval_exprlist_det:
  forall e pct al Mats Mats',
  eval_exprlist e pct al   Mats ->
  eval_exprlist e pct al   Mats' ->
    Mats = Mats'.
Proof with auto; try congruence.
  intros * A. revert Mats'.
  induction A as
  [|he te hv ht atms H T IH|he te err H|].
  - inversion 1...
  - intros. inv H0. unfold ret in *.
    + f_equal. injection (IH _ H5) as <-.
      injection (eval_expr_det H H3) as <- <-...
    + pose proof (eval_expr_det H H4). inv H0.
    + pose proof (IH _ H5). inv H0.
  - inversion 1; subst.
    + pose proof (eval_expr_det H H3). inv H1.
    + pose proof (eval_expr_det H H4). inv H1...
    + pose proof (eval_expr_det H H3). inv H1.
  - inversion 1; subst...
    + pose proof (IHA _ H5). inv H1.
    + pose proof (eval_expr_det H H4). inv H1.
Qed. (* Hint Resolve eval_exprlist_det : srcDet. *)

Ltac lookup_same :=
  match goal with
  | A: ?x = ?y,
    B: ?x = ?z
    |- _ => rewrite A in B; (try solve [inversion B]);
            injection B; clear A B; intros **; subst;
            (try solve [auto]); lookup_same

  | A: eval_expr ?e ?pct ?a   ?y,
    B: eval_expr ?e ?pct ?a   ?z
    |- _ => pose proof (eval_expr_det A B) as X;
            (try solve [inversion X]); injection X;
            clear A B X;
            intros **; subst; (try solve [auto]);
            lookup_same

  | A: eval_exprlist ?e ?pct ?bl   ?y,
    B: eval_exprlist ?e ?pct ?bl   ?z
    |- _ => pose proof (eval_exprlist_det A B) as X;
            (try solve [inversion X]); injection X;
            clear A B X;
            intros **; subst; (try solve [auto]);
            lookup_same

  | _ => idtac
  end.


Remark deterministic : forall p,
  determinate (HLL_semantics p).
Proof with try solve [eauto | lookup_same].
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


Module Type Sig (Import Tags  : TagDomain.FrontEnd)
                (Import Rules : HLL.Policy.Sig Tags)
                (Import Lang  : HLL.Language.Sig Tags).
Include Functor Tags Rules Lang.
End Sig.


Local Close Scope type_scope.