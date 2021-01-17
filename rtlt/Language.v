From Utils Require Import Defns.
From PIPE  Require Import TagDomain.
Set Implicit Arguments.



(* We make the Module Type include the functor to illustrate that the
   Module Type is something of a fiction. We only want the definition
   of RTL but need the Sig because the architecture of Tajine is heavily
   parameterized. *)
Module Type Sig (Import Tags : TagDomain.MiddleEnd).
Local Open Scope type_scope.

Definition lit := val * ValTag.
Definition defLit : lit := (O, defVT).

Inductive instr : Type :=
  | Inop : node -> instr
  | Imov : reg -> reg -> node -> instr  (**r [Imov src dst] *)
  | Imovi: lit -> reg -> node -> instr
  | Iop  : operation -> reg -> reg -> reg -> node -> instr
  | Icond: comparison -> reg -> reg -> node -> node -> instr
                  (**r [Icond cond a1 a2 ifso ifnot]
                   branches to [ifso] if [cond a1 a2] evalues to true,
                   otherwise it branches to [ifnot] *)
  | Icall: ident -> list reg -> reg -> node -> instr
                  (**r [Icall callee args dst succ]
                   branches to the cfg of the function [callee], while
                   passing the arguments [args].   It stores the result of
                   this call in the register [dst] and branches to [succ]. *)
  | Ireturn: reg -> instr.

Definition tinst : Type := instr * ITag.

Definition noop (ns: node) : tinst := (Inop ns, defIT).

Definition code: Type := PTree.t tinst.

Record function: Type := mkfunction {
  arity: signature;
  params: list reg;
  body: code;
  entrypoint: node;
  fntag  : PCTag
}.

Definition program := list (ident * function).


Local Close Scope type_scope.
(* Some Utility functions *)




Definition successors_tinst (i: tinst) : list node :=
  match i with
  | (Inop s       , _)
  | (Imov _ _ s   , _)
  | (Imovi _ _ s  , _)
  | (Iop _ _ _ _ s, _)
  | (Icall _ _ _ s, _) => s :: nil
  | (Icond _ _ _ ifso ifnot, _) => ifso :: ifnot :: nil
  | (Ireturn _, _) => nil
  end.

End Sig.

Module Imp (Tags : TagDomain.MiddleEnd) <: Sig Tags.
  Include Sig(Tags).
End Imp.
