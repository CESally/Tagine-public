From CompCert Require Export Maps Coqlib.
Set Implicit Arguments.
(** * Declaration of some basic utility types and libraries *)

(** This file contains some support code for the rest of the development,
    most importantly the importing of the CompCert Maps module. *)

(** We use finite map libraries from CompCert's Maps module. We use these maps
    for various kinds of environments/mappings throughout the development. Most
    of the libraries' functions (e.g. empty, set, get) have their
    standard/typical meaning. *)
(** There are simple map notations readers should be aware of:
-     [!] & [#] notate a get:  [<map> ! <key>] means "get the value
      of [<ele>] in the [<map>]".
-     [_ ! _ <- _]  & [_ # _ <- _] notate a set:   Note that [!]/[#]
      are overloaded here, but surely only in the best way of the
      tradition of overloading. [<map> ! <key> <- <new_val>] means "in
      [<map>], set the value of [<key>] to [<new_val>]". *)
(** Lastly, [PTree] is a finite #<i>#partial#</i># maps library (returning
    [option]s of their values) while [PMap] is a finite #<i>#total#</i># maps
    library, returning default values for keys that are not in the map. *)


(** We want a unified notion of value, since we're operating under the notion 
    a C-like toolchain *)

Definition val : Type := nat.
Inductive operation : Type :=
  | Oadd
  | Osub.
Parameter eval_op : operation -> val -> val -> val.

(** ** Abstract sets/collections *)

(** Most of the abstract sets in this development are implemented as Coq
    [positive]s *)

Definition ident := positive.
Definition node  := positive.
Definition reg   := positive.

(** Since source and target programs only have 1 numeric type,
    naturals, signatures are just the arity of a function *)

Definition signature := nat.

(** [comparisons] (used for/in boolean operators/expressions) *)

(* Inductive operation {X:Type} : Type :=
| Oadd   : X -> X -> operation
| Omonus : X -> X -> operation.

Inductive eval_operation {X:Type} (op: @operation X): X.
  match  with
  end. *)

Inductive comparison : Set :=  (** The standard set of comparisons *)
    Ceq : comparison           (** == equality                     *)
  | Cne : comparison           (** != inequality                   *)
  | Clt : comparison           (** <  less than                    *)
  | Cle : comparison           (** <= less than equals             *)
  | Cgt : comparison           (** >  greater than                 *)
  | Cge : comparison.          (** >= greater than equals          *)


(** [eval_comp] "casts" the abstract object level of comparisons into
    Coq [bool]s *)
Local Open Scope nat_scope.
Definition eval_comp (comp : comparison) (n m : nat) :=
  match comp with
    | Ceq => n =? m%nat
    | Cne => negb (n =? m)
    | Clt => n <? m
    | Cle => n <=? m
    | Cgt => negb (n <=? m)
    | Cge => negb (n <? m)
  end.
Local Close Scope nat_scope.
(** ** Register banks via finite partial maps *)
(** Mappings from registers to some type. [PMap] is a finite partial maps
    (with default values for unmapped keys) library from the CompCert Maps
    module. *)

Module Regmap := PMap.
(* Definition regset := Regmap.t val. *)
Notation "a # b" := (Regmap.get b a) (at level 1).
Notation "a ## b" := (List.map (fun r => Regmap.get r a) b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

(** Another notation *)

Notation "a ! b <- c" := (PTree.set b c a) (at level 1, b at next level).



Class Inj A B : Type := {
  inject : A -> B
}.
Notation "$" := inject.




Inductive MProp (P: Prop) : Type := Know: P -> MProp P | DKnow: MProp P.
Arguments Know  [_] _.
Arguments DKnow {_}  .
Extract Inductive MProp => "bool" [ "true" "false" ].

Definition andPF {P Q:Prop} (x : MProp P) (y : MProp Q) : MProp (P /\ Q) :=
  match x, y with
  | Know Ppf, Know Qpf => Know (conj Ppf Qpf)
  | _        , _       => DKnow
  end.
Definition andPFb {P:Prop} (x: MProp P) (b: bool) : bool :=
  if x then b else false.

Notation "P '&p'  Q" := (andPF P Q)  (at level 90).
Notation "P '&&p' b" := (andPFb P b) (at level 90).

Definition MProp__bool {P:Prop} (x: MProp P) : bool :=
  if x then true else false.

Coercion MProp__bool : MProp >-> bool.

