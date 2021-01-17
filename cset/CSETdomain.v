              Require Import List.
From Utils    Require Import Defns.
From CompCert Require Import Coqlib Maps Lattice Kildall Errors.
From PIPE     Require Import TagDomain.
From RTLT     Require Import Language Semantics.
Import ListNotations.

Create HintDb csedomDB.

(* Adapted from CompCert's CSEdomain.v *)

Module Functor (Import Tags  : TagDomain.MiddleEnd)
               (Import Rules : RTLT.Policy.Sig Tags)
               (Import Lang  : RTLT.Language.Sig Tags)
               (Import Sem   : RTLT.Semantics.Sig Tags Rules Lang).


Definition valnum := positive.

Inductive rhs : Type :=
  | Op: bool (* -> bool -> PCTag *) -> operation -> valnum -> valnum -> rhs.

Inductive equation : Type :=
  | Eq (v: valnum) (r: rhs).

Definition eq_valnum: forall (x y: valnum), {x=y}+{x<>y} := peq.

Definition eq_list_valnum: forall (x y: list valnum), {x=y}+{x<>y} := list_eq_dec peq.

Definition eq_rhs (x y: rhs) : {x=y}+{x<>y}.
Proof.
  assert (forall o1 o2:operation, {o1 = o2} + {o1 <> o2}) by
    (intros [] []; auto; right; inversion 1).
  generalize bool_dec eq_valnum eq_list_valnum (* pt_eq_dec *).
  decide equality.
Defined.


Record numbering : Type := mknumbering {
  num_next: valnum; (**r first unused value number *)
  num_eqs: list equation; (**r valid equations *)
  num_reg: PTree.t valnum; (**r mapping register to valnum *)
  num_val: PMap.t (list reg) (**r reverse mapping valnum to regs containing it *)
}.

Definition empty_numbering :=
  {| num_next := 1%positive;
     num_eqs := nil;
     num_reg := PTree.empty _;
     num_val := PMap.init nil |}.

Definition valnums_rhs (r: rhs): list valnum :=
  match r with
  | Op b op v1 v2 => [v1;v2]
  end.

Definition wf_rhs (next: valnum) (r: rhs) : Prop :=
forall v, In v (valnums_rhs r) -> Plt v next.

Definition wf_equation (next: valnum) (e: equation) : Prop :=
  match e with Eq l r => Plt l next /\ wf_rhs next r end.

Record wf_numbering (n: numbering) : Prop := {
  wf_num_eqs: forall e,
      In e n.(num_eqs) -> wf_equation n.(num_next) e;
  wf_num_reg: forall r v,
      PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next);
  wf_num_val: forall r v,
      In r (PMap.get v n.(num_val)) -> PTree.get r n.(num_reg) = Some v
}.

Hint Resolve wf_num_eqs wf_num_reg wf_num_val: csedomDB.


Definition valuation := valnum -> atom.
(* Definition valuation := valnum -> val. *)

Inductive rhs_eval_to (valu: valuation) : rhs -> atom -> Prop :=
  | op_eval_to: forall b (* pcp wpci *) op v t vn1 vn2 p a t1 t2 p' v1 v2 itag,
      (valu vn1) = (v1,t1) ->
      (valu vn2) = (v2,t2) ->
      IopTR itag p op t1 t2 = ret (p', t) ->
      eval_op op v1 v2 = v ->
      a = (v,t) ->
      rhs_eval_to valu (Op b op vn1 vn2) a.

Inductive equation_holds (valu: valuation) : equation -> Prop :=
  | eq_holds: forall l r,
      rhs_eval_to valu r (valu l) ->
      equation_holds valu (Eq l r).

Record numbering_holds (valu: valuation)
                       (rs: regbank) (n: numbering) : Prop := {
  num_holds_wf:
     wf_numbering n;
  num_holds_eq: forall eq,
     In eq n.(num_eqs) -> equation_holds valu eq;
  num_holds_reg: forall r v,
     n.(num_reg)!r = Some v -> rs#r = valu v
}.

Hint Resolve num_holds_wf num_holds_eq num_holds_reg: csedomDB.

Lemma empty_numbering_holds:
  forall valu rs,
  numbering_holds valu rs empty_numbering.
Proof.
  intros; split; simpl; intros.
  - split; simpl; intros.
    + contradiction.
    + rewrite PTree.gempty in H; discriminate.
    + rewrite PMap.gi in H; contradiction.
  - contradiction.
  - rewrite PTree.gempty in H; discriminate.
Qed.



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

End Functor.