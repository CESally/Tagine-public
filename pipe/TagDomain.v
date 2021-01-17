Module Type FrontEnd.

  Parameter PCTag ValTag TagErr : Type.

  Parameter defVT : ValTag.
  Parameter initPCT : PCTag.
  Parameter defER : TagErr.

  Local Open Scope type_scope.

  Definition M (X:Type) := X + TagErr.

  Definition ret {X:Type}:  X -> M X := inl.
  Definition fstop (e: TagErr) {X:Type}: M X := inr e.

  Definition bind {X Y:Type} (m: M X) (f: X -> M Y) : M Y :=
    match m with
    | inl x => f x
    | inr e => fstop e
    end.



  Parameter splice : forall {X Y Z:Type}, (X -> M Y) -> (Y -> M Z) -> X -> M Z.


  (* This is useful to know for things like value analysis in RTL
     And it should not be hard to justify that we expect these equalities
     to be decidable. *)
  Parameter vt_eq_dec: forall x y: ValTag, {x = y} + {x <> y}.
  Parameter pt_eq_dec: forall x y: PCTag , {x = y} + {x <> y}.
  Parameter te_eq_dec: forall x y: TagErr, {x = y} + {x <> y}.

  Local Close Scope type_scope.

End FrontEnd.



Module Type MiddleEnd.
Include FrontEnd.

Local Open Scope type_scope.

  Parameter ITag : Type.
  Parameter defIT : ITag.

  Parameter it_eq_dec: forall x y: ITag, {x = y} + {x <> y}.

Local Close Scope type_scope.
End MiddleEnd.
