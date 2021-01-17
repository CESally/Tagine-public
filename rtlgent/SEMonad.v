              Require Export Coq.Strings.String.
From HLL      Require Import Language.
From RTLT     Require Import Language.
From RTLgenT  Require Import Env.
From Utils    Require Export Defns.
From RTLgenT  Require Import Inj.


Module Functor (Import STags : TagDomain.FrontEnd)
               (Import Source: HLL.Language.Sig STags)
               (Import TTags : TagDomain_MiddleTgn STags)
               (Import Target: RTLT.Language.Sig TTags)
               (Import CompEnv : Env.CEnvSig STags Source TTags Target).
Import ListNotations.


Record state : Type := mkstate {
  st_nextreg  : reg;
  st_nextnode : node;
  st_code     : code;
  st_wf       : forall (pc : positive), Plt pc st_nextnode \/ st_code!pc = None
}.

Inductive state_earlier : state -> state -> Prop :=
  state_earlier_intro:
    forall (s1 s2 : state),
    Ple s1.(st_nextnode) s2.(st_nextnode) ->
    Ple s1.(st_nextreg) s2.(st_nextreg) ->
    (forall pc,
      s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_earlier s1 s2.

Lemma state_earlier_refl:
  forall s, state_earlier s s.
Proof.
  constructor.
  - apply Ple_refl.
  - apply Ple_refl.
  - intros; auto.
Qed.

Lemma state_earlier_trans : forall s1 s2 s3,
  state_earlier s1 s2 -> state_earlier s2 s3 -> state_earlier s1 s3.
Proof with auto.
  inversion 1; subst.
  inversion 1; subst.
  constructor.
  - apply Ple_trans with (st_nextnode s2)...
  - apply Ple_trans with (st_nextreg s2)...
  - intros. generalize (H2 pc) (H6 pc).
    intuition congruence.
Qed.

Inductive res (A: Type) (s: state): Type :=
  | Error: string -> res A s
  | OK: A -> forall (s': state), state_earlier s s' -> res A s.


Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: state) => OK x s (state_earlier_refl s).

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (state_earlier_trans s s' s'' i i')
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Definition bind3 {A B C D: Type} (f: mon (A * B * C)) (g: A -> B -> C -> mon D)
  : mon D :=
bind f (fun xyz => match xyz with (x,y,z) => g x y z end).

Definition error {A: Type} (msg: string) : mon A := fun (s: state) => Error msg.

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s: state) =>
    match f s with
    | OK a s' i => OK a s' i
    | Error _ => g s
    end.

(* Notations for bind, to make writing Monadic computations slightly more pleasant. *)

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200) : rtlgent_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200) : rtlgent_scope.
Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200) : rtlgent_scope.

Open Scope positive.
Remark init_state_wf : forall pc,
  Plt pc 1 \/ (PTree.empty tinst)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : state :=
  mkstate 1 1 (PTree.empty tinst) init_state_wf.
Close Scope positive.

(** It may seem slightly backwards to prove that a particular state is well
    formed, before declaring the state, but Coq's typechecker will ensure that
    [init_state_wf] really is a proof that [init_state] is well formed. *)

(** (Recall [st_wf: forall (pc : positive), Plt pc st_nextnode \/ st_code!pc = None]) *)

(** More accurately, [init_state_wf] proves a theorem that has the shape of
    [st_wf] but with specific values for [st_nextnode] & [st_code]. Or put
    another way, [init_state_wf] is a proof of the well-formed-ness of
    #<i>#any#</i># state with 
-   [st_nextnode] := [1]
-   [st_code]     := [PTree.empty instr]

    The fact that the typechecker accepts this as the argument to [mkstate] in
    [init_state] shows that it really is a proof that [init_state] is well formed.
    #</br>#
    This is idiom, of proving that a state with particular values is well
    formed, then passing that proof as an argument to [mkstate] is one that we
    will repeat below. *)

Remark add_instr_wf : forall s (ti: tinst) pc,
  let n := s.(st_nextnode) in
  Plt pc (Pos.succ n) \/ (PTree.set n ti s.(st_code))!pc = None.
Proof with auto.
  intros. destruct (peq pc n) as [<- | neq_pcn];
  [ left; apply Plt_succ
  | rewrite PTree.gso]...
  destruct (st_wf s pc);
  [ left; apply Plt_trans_succ
  | right]...
Qed.

Remark add_instr_earlier:
  forall s ti,
  let n := s.(st_nextnode) in
  state_earlier s (mkstate s.(st_nextreg)
                         (Pos.succ n)
                         (PTree.set n ti s.(st_code))
                         (add_instr_wf s ti)).
Proof with auto.
  constructor; simpl.
  - apply Ple_succ.
  - apply Ple_refl.
  - intros. destruct (st_wf s pc)...
    right. apply PTree.gso. intros ->.
    exact (Plt_strict _ H).
Qed.

Definition add_instr (i: instr) (it: ITag) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    OK n
       (mkstate   s.(st_nextreg)
                  (Pos.succ n)
                  (PTree.set n (i,it) s.(st_code))
                  (add_instr_wf s (i,it))
       )
       (add_instr_earlier s (i,it)).

Definition add_tinst (iit : tinst) : mon node :=
  let (i, it) := iit in
  add_instr i it.
(* Hint Unfold add_tinst. *)

Remark reserve_instr_wf:
  forall s pc,
  Plt pc (Pos.succ s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof with auto.
  intros. destruct (st_wf s pc);
  [ left; apply Plt_trans_succ
  | right]...
Qed.

Remark reserve_instr_earlier: (**r for the Mad *)
  forall s,
  let n := s.(st_nextnode) in
  state_earlier s (mkstate s.(st_nextreg)
               (Pos.succ n)
               s.(st_code)
               (reserve_instr_wf s)).
Proof.
  constructor; simpl;
  [ apply Ple_succ
  | apply Ple_refl
  | auto].
Qed.

Definition reserve_instr: mon node :=
  fun (s: state) =>
  let n := s.(st_nextnode) in
  OK n
     (mkstate   s.(st_nextreg)
                (Pos.succ n)
                s.(st_code)
                (reserve_instr_wf s)
     )
     (reserve_instr_earlier s).

Remark update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode) ->
  forall pc,
  Plt pc s.(st_nextnode) \/ (PTree.set n i s.(st_code))!pc = None.
Proof with auto.
  intros. destruct (peq pc n) as [<- | ?];
  [ left
  | rewrite PTree.gso;
    [ apply st_wf
    | ]]...
Qed.

Remark update_instr_earlier:
  forall s n i (LT: Plt n s.(st_nextnode)),
  s.(st_code)!n = None ->
  state_earlier s
             (mkstate s.(st_nextreg)
                      s.(st_nextnode)
                      (PTree.set n i s.(st_code))
                      (update_instr_wf s n i LT)).
Proof with auto.
  constructor; simpl; intros;
  [ apply Ple_refl
  | apply Ple_refl
  | rewrite PTree.gsspec;
    destruct (peq pc n) as [<- | ?];
    [ left
    | right]]...
Qed.

Definition check_empty_node:
  forall (s: state) (n: node), { s.(st_code)!n = None } + { True }.
Proof.
  intros. destruct (s.(st_code)!n);
  [ right
  | left]; auto.
Defined.

Definition update_instr (n: node) (i: instr) (it: ITag) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode), check_empty_node s n with
    | left LT, left EMPTY =>
        OK tt
           (mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set n (i,it) s.(st_code))
                    (update_instr_wf s n (i,it) LT))
           (update_instr_earlier s n (i,it) LT EMPTY)
    | _, _ =>
        Error "COCPIT.update_instr"
    end.

Definition update_tinst (n: node) (iit: tinst) : mon unit :=
  let (i, it) := iit in
  update_instr n i it.
(* Hint Unfold update_tinst. *)

End Functor.