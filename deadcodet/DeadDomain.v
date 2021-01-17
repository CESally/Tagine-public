From Utils    Require Import Defns.
From CompCert Require Import Lattice.
From PIPE     Require Import TagDomain.
From RTLT     Require Import Language Policy Semantics.

Create HintDb deaddomDB.

(* Adapted from Leroy's NeedDomain.v *)

Module Functor (Import Tags  : TagDomain.MiddleEnd)
               (Import Rules : RTLT.Policy.Sig Tags)
               (Import Lang  : RTLT.Language.Sig Tags)
               (Import Sem   : RTLT.Semantics.Sig Tags Rules Lang).

Inductive nval : Type :=
  | Dead
  | Live.

Definition eq_nval (x y: nval) : {x = y} + {x <> y}.
Proof. decide equality. Defined.


(* agreement between two values relative to a need *)
Fixpoint vagree (v w: atom) (x: nval) {struct x}: Prop :=
  match x with
  | Dead => True
  | Live => v = w
  end.

Lemma vagree_same: forall v x, vagree v v x.
Proof. intros v []; red; auto. Qed.
Hint Resolve vagree_same : deaddomDB.

Inductive nge: nval -> nval -> Prop :=
  | nge_dead : forall x, nge Live x
  | nge_Live : forall x, nge x Dead.

Lemma nge_refl: forall x, nge x x.
Proof.
  intros []; constructor.
Qed.

Hint Constructors nge: deaddomDB.
Hint Resolve nge_refl: deaddomDB.

Lemma nge_trans: forall x y, nge x y -> forall z, nge y z -> nge x z.
Proof with auto with deaddomDB.
  intros [] [] **... inversion H.
Qed.

Lemma nge_agree: forall v w x y,
  nge x y -> vagree v w x -> vagree v w y.
Proof.
  induction 1; simpl;
  [ intros <-; destruct x; simpl
  | ]; auto.
Qed.

Definition nlub (x y: nval) : nval :=
  match x, y with
  | Dead, _ => y
  | _, Dead => x
  | _, _    => Live
  end.

Lemma nge_lub_l:
  forall x y, nge (nlub x y) x.
Proof with auto with deaddomDB.
  intros [] []...
Qed.

Lemma nge_lub_r:
  forall x y, nge (nlub x y) y.
Proof with auto with deaddomDB.
  intros [] []...
Qed.



(* Properties of agreement between integers *)


(* The default abstraction: if the result is unused, the arguments are unused; otherwise, the arguments are needed in full. *)
Definition default (x: nval) :=
  match x with
  | Dead => Dead
  | _ => Live
  end.

Module NVal <: SEMILATTICE.

  Definition t := nval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z :=
    (@eq_trans t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_nval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    intros [] [].
    - unfold eq. auto.
    - unfold beq. simpl. inversion 1.
    - unfold beq. simpl. inversion 1.
    - unfold eq. auto.
  Qed.
  Definition ge := nge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; intros * <-.
    apply nge_refl.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; intros.
    eapply nge_trans; eauto.
  Qed.
  Definition bot : t := Dead.
  Lemma ge_bot: forall x, ge x bot.
  Proof. constructor. Qed.
  Definition lub := nlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof nge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof nge_lub_r.
End NVal.

Module NB <: SEMILATTICE := LPMap1(NVal).

Definition nbank := NB.t.
Definition nreg (nB: nbank) (r: reg) := NB.get r nB.
Hint Unfold nreg : deaddomDB.

Module NA <: SEMILATTICE := NB.

End Functor.
