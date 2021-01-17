From Utils Require Import Defns.
From PIPE  Require Import TagDomain.
Set Implicit Arguments.

Module Type Sig (Import Tags: TagDomain.FrontEnd).
Local Open Scope type_scope.

Definition lit := val * ValTag.
Definition defLit : lit := (O, defVT).

Inductive expr : Type :=
  | Elit : lit -> expr
  | Evar : ident -> expr
  | Eop : operation -> expr -> expr -> expr.

Inductive stmt : Type :=
  | Sseq : stmt -> stmt -> stmt
  | Sskip : stmt
  | Sassign : ident -> expr -> stmt
  | Sifthenelse : comparison -> expr -> expr -> stmt -> stmt -> stmt (**r The
      first and second [stmt] arguments to [Sifthenelse] represent the "then" and
      "else" blocks respectively.    [Sifthenelse comp a1 a2 ifso ifnot] jumps to
      [ifso] if [comp a1 a2] evaluates to true, otherwise it jumps to [ifnot] *)
  | Swhile : comparison -> expr -> expr -> stmt -> stmt
(*   | Sloop  : stmt -> stmt
  | Sblock : stmt -> stmt
  | Sexit  : nat -> stmt *)
  | Scall : ident -> ident -> list expr -> stmt (**r The first and second [ident]
      arguments to [Scall] represent, 1) the variable the result of the call is
      assigned to, 2) and the name of the callee function, respectively.
      [Scall x foo args] assigns to [x] the result of [foo] applied to [args].*)
  | Sreturn : expr -> stmt.

Record function : Type := mkfunction
  { arity  : signature
  ; params : list ident
  ; locals : list ident
  ; body   : stmt
  ; fntag  : PCTag }.

Definition program := list (ident * function).

Local Close Scope type_scope.
End Sig.




Module Imp (Import Tags : TagDomain.FrontEnd).
  Include Sig Tags.
End Imp.
