From Utils  Require Import Defns.
From PIPE   Require Import TagDomain.

Module TagInjection (FTags : TagDomain.FrontEnd) <: TagDomain.MiddleEnd.
Local Open Scope type_scope.

  Definition PCTag  := FTags.PCTag.
  Definition ValTag := FTags.ValTag + FTags.PCTag.
  Definition TagErr := FTags.TagErr.


  Definition defVT   : ValTag := inl FTags.defVT.
  Definition initPCT : PCTag  :=     FTags.initPCT.
  Definition defER   : TagErr :=     FTags.defER.

  Inductive ITag_ : Type := 
    | ITnone : ITag_

    | ITconst : ITag_
    | ITvar : ITag_
    | ITplus : ITag_
    | ITmonus : ITag_

    | ITassign : ITag_

    | ITifS : ITag_
    | ITifJ : ITag_

    | ITwN : ITag_
    | ITwL : ITag_
    | ITwX : ITag_

    | ITcall : ITag_
    | ITret : ITag_


    | ITsavePC : ITag_
    | ITusePC : ITag_

    | ITparam : operation -> ValTag -> ValTag -> ITag_.
  Definition ITag := ITag_.

  Definition defIT := ITnone.

  Definition ITop (op: operation) :=
    match op with
    | Oadd => ITplus 
    | Osub => ITmonus
    end.



  Definition M (X:Type) := X + TagErr.

  Definition ret {X:Type} : X -> M X := inl.
  Definition fstop (e: TagErr) {X:Type} : M X := inr e.


  Definition lift {X:Type} (x: FTags.M X) : M X :=
    match x return M X with
    | inl tags => ret tags
    | inr Serr => fstop Serr
    end.


  Definition bind {X Y: Type} (x: M X) (f: X -> M Y) : M Y :=
    match x with
    | inl y => f y
    | inr e => fstop e
    end.

  Definition splice {X Y Z:Type} (f: X -> M Y) (g: Y -> M Z) : X -> M Z := fun x =>
    match f x with
    | inl tag => g tag
    | inr err => fstop err
    end.


  Definition fstop_def {X:Type} : M X := fstop defER.

  Local Close Scope type_scope.


  Theorem vt_eq_dec: forall x y: ValTag, {x = y} + {x <> y}.
  Proof with auto.
    intros [vx | px] [vy | py];
    [ destruct (FTags.vt_eq_dec vx vy) as [->|];
      [left|right;inversion 1; subst]
    | right; inversion 1
    | right; inversion 1
    | destruct (FTags.pt_eq_dec px py) as [->|];
      [left|right;inversion 1; subst] ]...
  Qed.

  Theorem pt_eq_dec: forall x y: PCTag, {x = y} + {x <> y}.
  Proof FTags.pt_eq_dec.

  Theorem te_eq_dec: forall x y: TagErr, {x = y} + {x <> y}.
  Proof FTags.te_eq_dec.

  Theorem it_eq_dec : forall x y: ITag, {x = y} + {x <> y}.
  Proof.
    destruct x, y;
    try solve [right;inversion 1|left;apply eq_refl].
    destruct o, o0,
             (vt_eq_dec v  v1) as [->|],
             (vt_eq_dec v0 v2) as [->|];
    solve [right; inversion 1; contradiction|left; apply eq_refl].
  Qed.

End TagInjection.

Module Type TagDomain_MiddleTgn (FTags : TagDomain.FrontEnd) <: TagDomain.MiddleEnd.
Include TagInjection FTags.
End TagDomain_MiddleTgn.