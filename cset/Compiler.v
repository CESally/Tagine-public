From Utils    Require Import Defns.
From CompCert Require Import Coqlib Maps Lattice Kildall Errors.
From PIPE     Require Import TagDomain.
From RTLT     Require Import Language Semantics Policy.
From RTLgenT  Require Import Inj.
From RGTpf  Require Import Inj.
From CSET     Require Import CSETdomain.

Import ListNotations.

Module Functor (Export FE_tags: TagDomain.FrontEnd)
               (Export HLL_rules: HLL.Policy.Sig FE_tags)
               (Export HLL_flags: HLL.Policy.Props FE_tags HLL_rules)
               (Export Tags  : MiddleEnd_tagine FE_tags)
               (Export Rules : RTLT_Policy_Tgn FE_tags Tags HLL_rules HLL_flags)
               (Export Lang  : RTLT.Language.Sig Tags)
               (Import Sem   : RTLT.Semantics.Sig Tags Rules Lang)
               (Import Flags : RTLT_Policy_Props_Tgn FE_tags Tags HLL_rules Lang HLL_flags Rules).

Module Export CSETDom := CSETdomain.Functor Tags Rules Lang Sem.


Definition valnum_reg (n: numbering) (r: reg) : numbering * valnum :=
  match PTree.get r n.(num_reg) with
  | Some v => (n, v)
  | None =>
      let v := n.(num_next) in
      ( {| num_next := Pos.succ v;
           num_eqs := n.(num_eqs);
           num_reg := PTree.set r v n.(num_reg);
           num_val := PMap.set v (r :: nil) n.(num_val) |},
       v)
  end.

Fixpoint valnum_regs (n: numbering) (rl: list reg)
                     {struct rl} : numbering * list valnum :=
  match rl with
  | nil =>
      (n, nil)
  | r1 :: rs =>
      let (n1, v1) := valnum_reg n r1 in
      let (ns, vs) := valnum_regs n1 rs in
      (ns, v1 :: vs)
  end.

Fixpoint find_valnum_rhs (r: rhs) (eqs: list equation)
                         {struct eqs} : option valnum :=
  match eqs with
  | nil => None
  | Eq v r' :: eqs1 =>
      if  eq_rhs r r' then Some v else find_valnum_rhs r eqs1
  end.

Fixpoint find_valnum_rhs' (r: rhs) (eqs: list equation)
                          {struct eqs} : option valnum :=
  match eqs with
  | nil => None
  | Eq v r' :: eqs1 =>
      if eq_rhs r r' then Some v else find_valnum_rhs' r eqs1
  end.


Fixpoint find_valnum_num (v: valnum) (eqs: list equation)
                         {struct eqs} : option rhs :=
  match eqs with
  | nil => None
  | Eq v' r' :: eqs1 =>
      if peq v v' then Some r' else find_valnum_num v eqs1
  end.

Definition reg_valnum (n: numbering) (vn: valnum) : option reg :=
  match PMap.get vn n.(num_val) with
  | nil => None
  | r :: rs => Some r
  end.

Fixpoint regs_valnums (n: numbering) (vl: list valnum) : option (list reg) :=
  match vl with
  | nil => Some nil
  | v1 :: vs =>
      match reg_valnum n v1, regs_valnums n vs with
      | Some r1, Some rs => Some (r1 :: rs)
      | _, _ => None
      end
  end.

Definition find_rhs (n: numbering) (rh: rhs) : option reg :=
  match find_valnum_rhs' rh n.(num_eqs) with
  | None => None
  | Some vres => reg_valnum n vres
  end.

Definition forget_reg (n: numbering) (rd: reg) : PMap.t (list reg) :=
  match PTree.get rd n.(num_reg) with
  | None => n.(num_val)
  | Some v => PMap.set v (List.remove peq rd (PMap.get v n.(num_val))) n.(num_val)
  end.

Definition update_reg (n: numbering) (rd: reg) (vn: valnum) : PMap.t (list reg) :=
  let nv := forget_reg n rd in PMap.set vn (rd :: PMap.get vn nv) nv.

Fixpoint kill_eqs (pred: rhs -> bool) (eqs: list equation) : list equation :=
  match eqs with
  | nil => nil
  | (Eq l r) as eq :: rem =>
      if pred r then kill_eqs pred rem else eq :: kill_eqs pred rem
  end.

Definition kill_equations (pred: rhs -> bool) (n: numbering) : numbering :=
  {| num_next := n.(num_next);
     num_eqs := kill_eqs pred n.(num_eqs);
     num_reg := n.(num_reg);
     num_val := n.(num_val) |}.



Definition clear_pcp_only_eqns : numbering -> numbering := kill_equations (fun x =>
  match x with
  | Op b _ _ _ => b
  end).

Definition add_rhs (n: numbering) (rd: reg) (rh: rhs) : numbering :=
  match find_valnum_rhs rh n.(num_eqs) with
  | Some vres =>
      {| num_next := n.(num_next);
         num_eqs := n.(num_eqs);
         num_reg := PTree.set rd vres n.(num_reg);
         num_val := update_reg n rd vres |}
  | None =>
      {| num_next := Pos.succ n.(num_next);
         num_eqs := Eq n.(num_next)  rh :: n.(num_eqs);
         num_reg := PTree.set rd n.(num_next) n.(num_reg);
         num_val := update_reg n rd n.(num_next) |}
  end.

Definition add_mov (n: numbering) (rs rd: reg) :=

      let (n1, v) := valnum_reg n rs in
      {| num_next := n1.(num_next);
         num_eqs := n1.(num_eqs);
         num_reg := PTree.set rd v n1.(num_reg);
         num_val := update_reg n1 rd v |}.

Definition add_movi (n: numbering) (rd: reg) :=
      let v := n.(num_next) in
      {| num_next := Pos.succ v;
         num_eqs := n.(num_eqs);
         num_reg := PTree.set rd v n.(num_reg);
         num_val := update_reg n rd v |}.

Definition add_op (n: numbering) (b: bool) (op: operation) (r1 r2 rd: reg) :=
  let (n1, v1) := valnum_reg n r1 in
  let (n2, v2) := valnum_reg n1 r2 in
  add_rhs n2 rd (Op b op v1 v2).


Definition set_unknown (n: numbering) (rd: reg) :=
  {| num_next := n.(num_next);
     num_eqs := n.(num_eqs);
     num_reg := PTree.remove rd n.(num_reg);
     num_val := forget_reg n rd |}.






Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable n: numbering.

Fixpoint reduce_rec (niter: nat) (op: A) (args: list valnum) : option(A * list reg) :=
  match niter with
  | O => None
  | Datatypes.S niter' =>
      match f (fun v => find_valnum_num v n.(num_eqs)) op args with
      | None => None
      | Some(op', args') =>
          match reduce_rec niter' op' args' with
          | None =>
              match regs_valnums n args' with Some rl => Some(op', rl) | None => None end
          | Some _ as res =>
              res
          end
      end
  end.

Definition reduce (op: A) (rl: list reg) (vl: list valnum) : A * list reg :=
  match reduce_rec 4%nat op vl with
  | None => (op, rl)
  | Some res => res
  end.

End REDUCE.


Module Numbering.
  Definition t := numbering.
  Definition ge (n1 n2: numbering) : Prop :=
    forall valu rs,
    numbering_holds valu rs n2 ->
    numbering_holds valu rs n1.
  Definition top := empty_numbering.
  Lemma top_ge: forall x, ge top x.
Proof.
  intros; red; intros. unfold top.
  apply empty_numbering_holds.
Qed.

Lemma refl_ge: forall x, ge x x.
Proof.
  intros; red; auto.
Qed.
End Numbering.

Module Solver := BBlock_solver(Numbering).


Definition transfer (f: function) (pc: node) (before: numbering) :=
  match f.(body)!pc with None => before | Some ti =>
      match ti with
      | (Imov rs      rd ns, itag) => if lpcp ti
                                      then add_mov before rs rd
                                      else clear_pcp_only_eqns before
      | (Iop op r1 r2 rd ns, itag) => if lpcp ti
                                      then add_op before (wpci ti) op r1 r2 rd
                                      else clear_pcp_only_eqns before
      | (Imovi l      rd ns, itag) => if lpcp ti
                                      then add_movi before rd
                                      else clear_pcp_only_eqns before

      | (Icall _ _ _ _, itag) => empty_numbering

      | (Inop _         , itag)
      | (Icond _ _ _ _ _, itag)
      | (Ireturn _      , itag) => if lpcp ti
                                   then before
                                   else clear_pcp_only_eqns before
      end
  end.

Definition analyze (f: function) : option (PMap.t numbering) :=
  Solver.fixpoint f.(body) successors_tinst (transfer f) f.(entrypoint).

Definition transl_instr (n: numbering) (ti: tinst) :=
  match ti with
  | (Iop op r1 r2 rd ns, itag) =>
        let (n1, v1) := valnum_reg n r1 in
        let (n2, v2) := valnum_reg n1 r2 in
        match find_rhs n2 (Op true op v1 v2) with (* the [true] doesn't matter *)
        | Some r => (Imov r rd ns, itag)
        | None => ti
        end
  | _ => ti
  end.

Definition transl_code (approxs: PMap.t numbering) (instrs: code) : code :=
  PTree.map (fun pc instr => transl_instr approxs!!pc instr) instrs.

Definition transl_function (f: function) : res function :=
  match analyze f with
  | None => Error (msg "CSE failure")
  | Some approxs =>
      OK(mkfunction
           f.(arity)
           f.(params)
           (transl_code approxs f.(body))
           f.(entrypoint)
           f.(fntag))
  end.

(* Definition transl_function (f: function) : res function :=
  match analyze f with
  | Some an =>
      OK {| arity := f.(arity);
            params := f.(params);
            body := PTree.map (transl_instr an ) f.(body);
            entrypoint := f.(entrypoint);
            fntag := f.(fntag) |}
  | None => Error [MSG "analysis failed"]
  end. *)

Local Open Scope error_monad_scope.
Fixpoint transl_program (p: program) : res program :=
  match p with
  | (i,f) :: tl => do tf <- transl_function f;
                   do tp <- transl_program tl;
                     OK ((i,tf) :: tp)
  | []          => OK []
  end.
Local Close Scope error_monad_scope.


(* Some utility facts about translation *)

Lemma tr_function_preserves : forall {f tf},
  transl_function f = OK tf ->
  tf.(fntag) = f.(fntag) /\
  tf.(arity) = f.(arity) /\
  tf.(entrypoint) = f.(entrypoint) /\
  tf.(params) = f.(params).
Proof.
  intros. unfold transl_function in H.
  destruct (analyze f); inv H; auto.
Qed.

Lemma tr_function_fntag:
  forall {f tf},
  transl_function f = OK tf ->
  tf.(fntag) = f.(fntag).
Proof with auto.
  intros. destruct (tr_function_preserves H)...
Qed.

Lemma tr_function_sig:
  forall {f tf},
  transl_function f = OK tf ->
  tf.(arity) = f.(arity).
Proof with auto.
  intros. destruct (tr_function_preserves H)
as [_[? _]]...
Qed.

Lemma tr_function_entry:
  forall {f tf},
  transl_function f = OK tf ->
  tf.(entrypoint) = f.(entrypoint).
Proof with auto.
  intros * H. unfold transl_function in H.
  destruct (analyze f); inv H; simpl...
Qed.

Lemma tr_function_params:
  forall {f tf},
  transl_function f = OK tf ->
  tf.(params) = f.(params).
Proof with auto.
  intros * H. unfold transl_function in H.
  destruct (analyze f); inv H; simpl...
Qed.

End Functor.