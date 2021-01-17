From Utils     Require Import Defns.
From CompCert  Require Import Coqlib Maps Lattice Kildall Errors.
From PIPE      Require Import TagDomain.
From RTLT      Require Import Language Semantics Policy.
From DeadcodeT Require Import DeadDomain.
Import ListNotations.

Module Functor (Export Tags  : TagDomain.MiddleEnd)
               (Export Rules : RTLT.Policy.Sig Tags)
               (Export Lang  : RTLT.Language.Sig Tags)
               (Import Sem   : RTLT.Semantics.Sig Tags Rules Lang)
               (Import Flags : RTLT.Policy.Props Tags Lang Rules).

Module Export DDomain := DeadDomain.Functor Tags Rules Lang Sem.

Definition add_need_all (r: reg) (ne: nbank) : nbank :=
  NB.set r Live ne.

Fixpoint add_needs_all (rl: list reg) (ne: nbank) : nbank :=
  match rl with
  | nil => ne
  | r1 :: rs => add_need_all r1 (add_needs_all rs ne)
  end.

Definition kill (r: reg) (ne: nbank) : nbank := NB.set r Dead ne.

Definition is_dead_atm (v: nval) : bool :=
  match v with Dead => true | _ => false end.

Definition is_dead_rule (ti: tinst) :=
  (dfs ti) &p (lpcp ti).


Definition transfer (f: function) (pc: node) (after: NA.t) : NA.t :=
    match f.(body) ! pc with None => NA.bot | Some ti =>
  match ti with 
  | (Inop _, _) => after
  | (Imov rs rd _, itag) =>
      let nrd := nreg after rd in
      if (is_dead_rule ti) &&p (is_dead_atm nrd) then after
      else add_need_all rs (if (dnd_ImovTR itag)
                             then (        kill rd after)
                             else (add_need_all rd after))
  | (Imovi _ rd _, _) =>
      let nrd := nreg after rd in
      if (is_dead_rule ti) &&p (is_dead_atm nrd) then after
      else kill rd after
  | (Iop _ r1 r2 rd _, _) =>
      let nrd := nreg after rd in
      if (is_dead_rule ti) &&p (is_dead_atm nrd) then after
      else add_needs_all [r1; r2] (kill rd after)
  | (Icond cond r1 r2 s1 s2, _) =>
      if (is_dead_rule ti) &&p (peq s1 s2) then after else
        add_needs_all [r1; r2] after
  | (Icall callee_id args rd _, _) =>
      add_needs_all args (kill rd after)
  | (Ireturn r, _) =>
      add_need_all r after
  end end.


Module DS := Backward_Dataflow_Solver(NA)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t NA.t) :=
  DS.fixpoint f.(body) successors_tinst (transfer f).

Definition transl_instr (an: PMap.t NA.t) (pc: node) (ti: tinst) :=
  match ti with
  | (Imov  _   rd ns, _)
  | (Imovi _   rd ns, _)
  | (Iop _ _ _ rd ns, _) =>
      let nrd := nreg (an !! pc) rd in
      if (is_dead_rule ti) &&p (is_dead_atm nrd)
      then noop ns else ti
  | (Icond _ r1 r2 s1 s2, _) =>
      if (is_dead_rule ti) &&p (peq s1 s2)
      then noop s1 else ti
  | _ => ti
  end.

Definition transl_function (f: function) : res function :=
  match analyze f with
  | Some an =>
      OK {| arity := f.(arity);
            params := f.(params);
            body := PTree.map (transl_instr an ) f.(body);
            entrypoint := f.(entrypoint);
            fntag := f.(fntag) |}
  | None => Error [MSG "analysis failed"]
  end.

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

(* 

port/adapt CC RTL printer / extraction


writeup should be
  organized by optimization - as the major axis
  then talk about rule constraints - which may show up under multiple optimizations
  talk about dead code, CSE, const prop, but some of them will be "hypothetical"
  ?function inlining










 *)
