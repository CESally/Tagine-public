From PIPE     Require Import TagDomain.
From HLL      Require Import Language.
From RTLT     Require Import Language.
From Utils    Require Import Defns.
From RTLgenT  Require Import Inj.


Module Type CEnvSig (Import STags : TagDomain.FrontEnd)
                    (Import Source: HLL.Language.Sig STags)
                    (Import TTags : TagDomain_MiddleTgn STags)
                    (Import Target: RTLT.Language.Sig TTags).

  Create HintDb cocpitDB.

  Declare Scope rtlgent_scope.
  Delimit Scope rtlgent_scope with rtlgent.

  Notation "'SM'"      := STags.M (at level 50) : rtlgent_scope.
  Notation "'TM'"      := TTags.M (at level 50) : rtlgent_scope.
  Notation "'SValTag'" := STags.ValTag          : rtlgent_scope.
  Notation "'TValTag'" := TTags.ValTag          : rtlgent_scope.
  Notation "'SPCTag'"  := STags.PCTag           : rtlgent_scope.
  Notation "'TPCTag'"  := TTags.PCTag           : rtlgent_scope.
  Notation "'STagErr'" := STags.TagErr          : rtlgent_scope.
  Notation "'TTagErr'" := TTags.TagErr          : rtlgent_scope.
  Notation "'Slit'"    := Source.lit            : rtlgent_scope.
  Notation "'Tlit'"    := Target.lit            : rtlgent_scope.



  Local Open Scope rtlgent_scope.

  Instance injectLit : Inj Slit Tlit := {
    inject := fun xy =>
                match xy with
                | (x,y) => (x, inl y)
                end
  }.

  Theorem injectLit_inj: forall (a b: Slit),
    $ a = $ b -> a = b.
  Proof with auto.
    intros [v1 t1] [v2 t2]. inversion 1...
  Qed.

  Instance injectVT : Inj SValTag TValTag := {
    inject := inl
  }.

  Theorem injectVT_inj: forall (a b: SValTag),
    $ a = $ b -> a = b.
  Proof. inversion 1; auto. Qed.

  Instance injectVTs : Inj (list SValTag) (list ValTag) := {
    inject := map inl
  }.

  Theorem injectVTs_inj: forall (xs ys: list SValTag),
    $ xs = $ ys -> xs = ys.
  Proof with auto.
    induction xs as [|x xs IH], ys as [|y ys];
    try inversion 1...
    - erewrite IH...
  Qed.

  Instance injectErr : Inj STagErr TTagErr := {
    inject := id
  }.

  Theorem injectErr_inj: forall (a b: STagErr),
    $ a = $ b -> a = b.
  Proof. inversion 1; auto. Qed.
  Local Close Scope rtlgent_scope.




  Definition PIsave    r n      : tinst := (Imov r r n, ITsavePC).
  Definition PIrecover r n itag : tinst := (Imov r r n, itag).
  Hint Unfold PIsave PIrecover : cocpitDB.


  Definition                mapping := PTree.t reg.
  Definition init_mapping : mapping := PTree.empty reg.


End CEnvSig.

Module Type Functor (Import STags : TagDomain.FrontEnd)
                    (Import Source: HLL.Language.Sig STags)
                    (Import TTags : TagDomain_MiddleTgn STags)
                    (Import Target: RTLT.Language.Sig TTags)
    <: CEnvSig STags Source TTags Target.
  Include CEnvSig STags Source TTags Target.
End Functor.
  