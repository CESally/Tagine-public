           Require Import Wellfounded.
From Utils Require Import Defns Smallstep.
From RGTpf Require Export Matching.


Module Functor (Export STags  : TagDomain.FrontEnd)
               (Import Source : HLL.Language.Sig STags)
               (Import TTags  : TagDomain_MiddleTgn STags)
               (Import Target : RTLT.Language.Sig TTags)
               (Export CompEnv: CEnvSig STags Source TTags Target)
               (Export SRules : HLL.Policy.Sig STags)
               (Export SFlags : HLL.Policy.Props STags SRules)
               (Export TRules : RTLT_Policy_Tgn STags TTags SRules SFlags)
               (Export TFlags : RTLT_Policy_PropT
                                  STags SRules SFlags TTags TRules Target)
               (Export SSem   : HLL.Semantics.Sig STags SRules Source)
               (Export TSem   : RTLT.Semantics.Sig TTags TRules Target).

Module Export Spec := RGTpf.Matching.Functor
                        STags Source
                        TTags Target
                        CompEnv
                        SRules SFlags
                        TRules TFlags
                        SSem
                        TSem.


Local Open Scope rtlgent_scope.
Section CORRECTNESS.

Variable  prog: Source.program.
Variable tprog: Target.program.
Hypothesis TRANSL: match_prog prog tprog.

Let  ge : SSem.genv := SSem.mkge  prog.
Let tge : TSem.genv := TSem.mkge tprog.



Section CORRECTNESS_EXPR.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
              I /\ P
    e, a ----------------- State cs code ne rb
     ||                          |
     ||                          |*
     ||                          |
     \/                          v
    e, v ----------------- State cs code ns rb'
              I /\ Q
>>
  where [tr_expr code map pr a ne ns rd] is assumed to hold.   The left vertical
  (doubled "||") arrow represents an evaluation of the expression [a].   The
  right vertical (single "|") arrow represents the execution of zero, one or
  several instructions in the generated #<b><tt>#target#</tt></b># CFG ([code]).

  The correspondance between these two arrows is that they should be performing
  the same compuation, one in the source, one in the target.
  The invariant [I] is the agreement between #<b><tt>#source#</tt></b>#
  environments and #<b><tt>#target#</tt></b># register environment, as captured
  by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register bank [rb'], register
  [rd] contains value [v], and the registers in the set of preserved registers
  [pr] are unchanged, as are the registers in the codomain of [map].

  We formalize this simulation property by the following predicate parameterized
  by the #<b><tt>#source#</tt></b># evaluation (left arrow). *)


(*     Local Coercion VT_unlift  : TTags.ValTag >-> STags.ValTag.
    Local Coercion V2P_unlift : TTags.ValTag >-> STags.PCTag. *)


Variable (E: env) (p: PCTag).

Definition transl_expr_prop (e: expr) (vat: SM Satom) : Prop :=
forall f ne ns cs B map rd mdfy
  (MIJ: map_inj map)                          (**r P *)
  (ME : match_env map E B)                    (**r I *)
  (TE : tr_expr f.(body) map mdfy e rd   ne ns),
match vat with
| inl atm => exists B',
      plus step tge (State f ne p B cs) (State f ns p B' cs)
   /\ match_env map E B'                    (**r I *)
   /\ B'#rd = $ atm                         (**r Q *)
   /\ (forall r, ~mdfy r -> B'#r = B#r)     (**r Q *)
| inr err =>
      plus step tge (State f ne p B cs) (Errorstate ($ err))
end.


Definition transl_exprlist_prop (es: list expr)
                                (vats: SM (list Satom)) : Prop :=
forall f ne ns cs B map rl mdfy
  (MIJ: map_inj map)
  (ME : match_env map E B)
  (TE : tr_exprlist f.(body) map mdfy es rl   ne ns),
match vats with
| inl atms => exists B',
      star step tge (State f ne p B cs) (State f ns p B' cs)
   /\ match_env map E B'
   /\ B'##rl = $ atms
   /\ (forall r, ~mdfy r -> B'#r = B#r)
| inr err =>
      plus step tge (State f ne p B cs) (Errorstate ($ err))
end.
Hint Unfold transl_exprlist_prop : cocpitDB.

(** The correctness of the translation is a huge induction over the
    #<b><tt>#source#</tt></b># evaluation derivation for the source program.   To
    keep the proof manageable, we put each case of the proof in a separate lemma.
    There is one lemma for each #<b><tt>#source#</tt></b># evaluation rule.   It
    takes as hypotheses the premises of the #<b><tt>#source#</tt></b># evaluation
    rule, plus the induction hypotheses, that is, the [transl_expr_prop], etc,
    corresponding to the evaluations of sub-expressions or sub-statements. *)


Theorem transl_expr_Elit_correct : forall l v t
  (slta: SSem.toAtom l = (v, t)),
transl_expr_prop (Elit l) (embed v (constTR p t)).
Proof with eauto.
  red. intros **. inv TE.
  generalize (eq_refl (ImoviTR ITconst p (inl t))).
  unfold ImoviTR at 2, lift_v, VT_unlift. intro DIT.
  destruct (toAtom ($ l))      as [tv vp] eqn:tlta,
           (toAtoms slta tlta) as [<- [tt [-> <-]]],
           (constTR p t)       as [t'|serr]; simpl.
  - exists (B # rd <- (v,inl t')). repeat split.
    + apply plus_one. eapply exec_Imovi...
    + apply match_env_update_temp...
    + rewrite Regmap.gss...
    + intros; destruct (Pos.eqb_spec r rd) as [<- |?];
      [ exfalso
      | rewrite Regmap.gso]...
  - apply plus_one. unfold toAtom, id in tlta.
    eapply exec_Imovi_err...
Qed.


Theorem transl_expr_Evar_correct : forall x v t
  (EID: E ! x = Some (v, t)),
transl_expr_prop (Evar x) (embed v (varTR p t)).
Proof with eauto.
  red. intros **. inv TE.
  generalize (eq_refl (ImovTR ITvar p (inl t) (B ^ rd))).
  unfold ImovTR at 2, lift_v, VT_unlift. intro DIT.
  destruct (B#rs) as [tv vp_s] eqn:BRS,
           (B#rd) as [xx vp_d] eqn:BRD.
  exploit match_env_atoms_eq... intros [<- [tt [-> <-]]].
  destruct (varTR p t) as [t'|serr]; simpl.
  - exists (B # rd <- (v,inl t')). repeat split.
    + apply plus_one. eapply exec_Imov...
    + apply match_env_update_temp...
    + rewrite Regmap.gss...
    + intros; destruct (Pos.eqb_spec r rd) as [<- |?];
      [ exfalso
      | rewrite Regmap.gso]...
  - apply plus_one. eapply exec_Imov_err...
Qed.


Theorem op_rules: forall {op t1 t2 m},
  opTR op p t1 t2 = m ->
  IopTR (ITop op) p op (inl t1) (inl t2) = lift_v p m.
Proof with auto.
  intros ? ? ? [vt'|serr]; destruct op;
  unfold IopTR, ITop, opTR, lift, VT_unlift;
  intros ->...
Qed.

Theorem op_rule_inl: forall op t1 t2 t',
opTR op p t1 t2 = inl t' ->
IopTR (ITop op) p op (inl t1) (inl t2) = inl (p, inl t').
Proof. intros *. refine op_rules. Qed.

Theorem op_rule_inr: forall op t1 t2 err,
opTR op p t1 t2 = inr err ->
IopTR (ITop op) p op (inl t1) (inl t2) = fstop err.
Proof. intros *. refine op_rules. Qed.
Hint Resolve op_rule_inl op_rule_inr : cocpitDB.


Theorem transl_expr_Eop_correct : forall op e1 e2 v1 v2 t1 t2
  (Leval: eval_expr E p   e1 (inl (v1, t1)))
  (Lrec: transl_expr_prop e1 (inl (v1, t1)))
  (Reval: eval_expr E p   e2 (inl (v2, t2)))
  (Rrec: transl_expr_prop e2 (inl (v2, t2))),
transl_expr_prop (Eop op e1 e2)
                 (embed (eval_op op v1 v2)
                        (opTR op p t1 t2)).
Proof with eauto with cocpitDB.
  red. intros **. inv TE.
  exploit Lrec... intros [rb1 [EX1 [ME1 [RR1 RO1]]]].
  exploit Rrec... intros [rb2 [EX2 [ME2 [RR2 RO2]]]].
  simpl in *. remember (eval_op op v1 v2) as v.
  destruct (opTR op p t1 t2) as [t'|serr] eqn:TR; simpl.
  - exists (rb2 # rd <- (v, inl t')). repeat split.
    + eapply plus_trans;[exact EX1|].
      eapply plus_one_plus;[exact EX2|].
      eapply exec_Iop...
      * rewrite RO2...
    + apply match_env_update_temp...
    + rewrite Regmap.gss...
    + intros; destruct (Pos.eqb_spec r rd) as [<- |?];
      [ exfalso
      | rewrite Regmap.gso]... rewrite RO2, RO1...
  - eapply plus_trans;[exact EX1|].
    eapply plus_one_plus;[exact EX2|].
    eapply exec_Iop_err...
    * rewrite RO2...
Qed.


Theorem transl_expr_Eop_errl_correct : forall op e1 e2 err
  (Leval: eval_expr E p e1 (inr err))
  (Lrec: transl_expr_prop e1 (inr err)),
transl_expr_prop (Eop op e1 e2) (inr err).
Proof with eauto.
  red. intros **. inv TE.
  exploit Lrec...
Qed.

Theorem transl_expr_Eop_errr_correct : forall op e1 e2 v1 t1 err
  (Leval: eval_expr E p   e1   (inl (v1, t1)))
  (Lrec: transl_expr_prop e1   (inl (v1, t1)))
  (Reval: eval_expr E p   e2   (inr err))
  (Rrec: transl_expr_prop e2   (inr err)),
transl_expr_prop (Eop op e1 e2) (inr err).
Proof with eauto.
  red. intros **. inv TE. exploit Lrec...
  intros [B1 [EX1 [ME1 [RR1 RO1]]]].
  eapply plus_trans...
Qed.


Theorem transl_expr_correct:
  forall e Mat,
  eval_expr E p    e   Mat->
  transl_expr_prop e   Mat.
Proof (eval_expr_ind _ 
  transl_expr_Elit_correct
  transl_expr_Evar_correct
  transl_expr_Eop_correct
  transl_expr_Eop_errl_correct
  transl_expr_Eop_errr_correct
).


Lemma transl_exprlist_nil_correct :
  transl_exprlist_prop nil (inl nil).
Proof.
  red; intros. inv TE.
  exists B; repeat split.
  - apply star_refl.
  - assumption.
Qed.


Lemma transl_exprlist_cons_correct : forall e es v t ts
  (Heval: eval_expr E p       e    (inl (v, t)))
  (Teval: eval_exprlist E p   es   (inl ts))
  (Trec: transl_exprlist_prop es   (inl ts)),
transl_exprlist_prop (e :: es)     (inl ((v, t) :: ts)).
Proof with eauto .
  red; intros; inv TE.
  specialize (transl_expr_correct  _ _ Heval) as Hrec.
  exploit Hrec... intros [B1 [EX1 [ME1 [RES1 PRE1]]]].
  exploit Trec... intros [B2 [EX2 [ME2 [RES2 PRE2]]]].
  exists B2; repeat split...
  - eapply plus_star_star...
  - simpl. f_equal... rewrite PRE2...
  - intros. rewrite PRE2, PRE1...
Qed.

Lemma transl_exprlist_cons_head_err : forall e es err
  (Heval: eval_expr E p e        (inr err)),
transl_exprlist_prop (e :: es)   (inr err).
Proof with eauto.
  red; intros; inv TE. exploit transl_expr_correct...
  simpl; intros EX. exact EX.
Qed.

Lemma transl_exprlist_cons_tail_err : forall e es err atm
  (Heval: eval_expr E p       e    (inl atm))
  (Teval: eval_exprlist E p   es   (inr err))
  (Trec: transl_exprlist_prop es   (inr err)),
transl_exprlist_prop (e :: es)     (inr err).
Proof with eauto.
  red; intros; inv TE.
  specialize (transl_expr_correct  _ _ Heval) as Hrec.
  exploit Hrec... intros [B1 [EX1 [ME1 [RES1 PRE1]]]].
  exploit Trec... intros EX_err.
  eapply plus_trans...
Qed.

Theorem transl_exprlist_correct:
  forall es Mats,
  eval_exprlist E p    es   Mats ->
  transl_exprlist_prop es   Mats.
Proof (eval_exprlist_ind _
  transl_exprlist_nil_correct
  transl_exprlist_cons_correct
  transl_exprlist_cons_head_err
  transl_exprlist_cons_tail_err
).


End CORRECTNESS_EXPR.

(** ** Termination measure over #<b><tt>#source#</tt></b># [state]s *)
Local Open Scope nat_scope.
Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sifthenelse c e1 e2 s1 s2 => 1 + size_stmt s1 + size_stmt s2
  | Sseq s1 s2                => 1 + size_stmt s1 + size_stmt s2
  | Sskip                     => 0
  | _                         => 1
  end.

Fixpoint size_cont (k: local_cont) : nat :=
  match k with
  | Kseq s k'    => 1 + size_cont k' + size_stmt s
  | Kjoin _ _ k' => 1 + size_cont k'
  | Kemp         => 0
  end.

(** Since we will be stepping into and out-of function simultaeneously in the
    source and target semantics, we only need the termination measure over
    [State]s as that is then the only time stuttering can occur. *)

Definition measure_state (S: SSem.state) :=
  match S with
  | SSem.State _ s lk _ _ _ => (size_stmt s + size_cont lk, size_stmt s)
  | _                       => (0, 0)
  end.

Definition lt_state (S1 S2: SSem.state) :=
  lex_ord lt lt (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
  forall f1 s1 p1 k1 ck1 E1 f2 s2 p2 k2 ck2 E2,
      size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (SSem.State f1 s1 k1 p1 ck1 E1)
           (SSem.State f2 s2 k2 p2 ck2 E2).
Proof with auto.
  intros. unfold lt_state. simpl.
  destruct H as [?| [-> ?]];
  [ left
  | right ]...
Qed.

Ltac Lt_state := apply lt_state_intro; simpl; try omega.

Lemma lt_state_trans:
 forall a b c,
  lt_state a b -> lt_state b c -> lt_state a c.
Proof.
  unfold lt_state. intros a b c.
  generalize
    (measure_state a)
    (measure_state b)
    (measure_state c).
  apply transitive_lex_ord;
  unfold Relation_Definitions.transitive;
  apply Nat.lt_trans.
Qed.

Lemma lt_state_irrefl: forall a,
  ~ lt_state a a.
Proof.
  inversion 1; eapply Nat.lt_irrefl; eauto.
Qed.

Lemma lt_state_wf : well_founded lt_state.
Proof.
  unfold lt_state. apply wf_inverse_image with (f := measure_state).
  apply wf_lex_ord; apply lt_wf.
Qed.
Local Close Scope nat_scope.


(** ** Semantic preservation for the translation of statements *)

(** The simulation diagram for the translation of statements
    and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
    where [I] is the [match_states] predicate defined below.  It includes:
-     Agreement between the #<b><tt>#source#</tt></b># statement under
      consideration and the current program point in the
      #<b><tt>#target#</tt></b># CFG, as captured by the [tr_stmt] predicate.
-     Agreement between the #<b><tt>#source#</tt></b># continuation and the
      #<b><tt>#target#</tt></b># CFG and call stack, as captured by the
      [tr_cont] predicate below.
-     Agreement between #<b><tt>#source#</tt></b># environments and
      #<b><tt>#target#</tt></b># register environments, as captured by
      [match_envs]. *)


(** ** The Translation Lemma *)

(** [transl_step_correct] is the lemma showing that "execution" through the
    programs match.   It formalizes the earlier statement simulation diagram;
    since function call and return steps appear in the same patterns in both
    #<b><tt>#source#</tt></b># and #<b><tt>#target#</tt></b># semantics, they
    correspond exactly, and are easily incorporated into the scheme.
    i.e., when the source semantics makes [step_call] step, the target semantics
    makes a [exec_Icall] step. Similarly for [step_function] and [exec_function].
    
 *)
(** The proof proceeds on an induction over steps in the source semantics. *)

(** We abstract the proof scripts for stuttering cases into this tactic, [Stutter]. *)

Ltac Stutter := econstructor; split;
                [ right; split; [apply star_refl | Lt_state]
                | repeat (econstructor; eauto)].

Ltac Error := first
  [   intros ?EX_err; eexists; split;
      [
      | econstructor; eauto with cocpitDB];
        try (left; exact EX_err)
  |   eexists; split;
      [ left
      | econstructor; eauto with cocpitDB]
  ].

Ltac Exec_real_nop := eapply exec_Inop;[eauto|apply real_nopTR].


Theorem transl_step_correct:
  forall S1 S2, SSem.step ge S1 S2 ->
  forall R1,    match_states S1 R1 ->
  exists R2,
  (plus TSem.step tge R1 R2 \/ 
   star TSem.step tge R1 R2 /\ lt_state S2 S1)
  /\ match_states S2 R2.
Proof with eauto with cocpitDB.
  induction 1; intros R1 MSTATE; inv MSTATE.


    (* sequencing steps *)

  - (* step_seq *)
    inv TS. Stutter.

  - (* step_skip_seq *)
    inv TS. inv TK. Stutter.



    (* join point steps (local) *)

    (* step_skip_rule *) - {
    inv TS. inv TK.

  - (* step_skip_rule *)
    eexists. split.
    + left. apply plus_one.
      eapply exec_Imov...
      now rewrite H9, H.
    + econstructor...
      * econstructor...
      * eapply tr_cont_rb...
        intros **. rewrite Regmap.gso...
        intros ->...


  - (* step_skip_rule no saves *)
    eexists. split.
    + left. apply plus_one.
      eapply exec_Inop...
      rewrite H7. apply H.
    + econstructor...
      * econstructor...

  - (* step_skip_rule no joins *)
    Stutter. }

    (* step_skip_rule_err *) - {
    inv TS. inv TK.

  - (* step_skip_rule_err *)
    Error.
    + apply plus_one.
      eapply exec_Imov_err...
      now rewrite H9, H.

  - (* step_skip_rule_err no joins *)
    Error.
    + apply plus_one.
      eapply exec_Inop_err...
      rewrite H7...

  - (* step_skip_rule_err no joins *)
    exfalso. eapply H9... }

  - (* step_assign *)
    inv TS. exploit transl_expr_correct...
    simpl in *. intros [rb' [EX [ME' [RBRD MR]]]].
    exploit match_env_tags... simpl. unfold getTag.
    destruct (rb'#rx) as [xx [tt'|]] eqn:RBMR;
    [ injection 1 as ->
    | inversion 1].
    econstructor; split.
    + left. eapply plus_one_plus...
      eapply exec_Imov... simpl.
      rewrite H1. destruct dnd_assignTR;
      [ erewrite e, H1
      | ]; try now simpl.
    + econstructor...
      * constructor.
      * eapply tr_cont_rb... intros.
        rewrite Regmap.gso, MR...
        intros <-. eapply tr_cont_dstk_map_disjoint...
        unfold reg_in_map. eexists...
      * eapply match_env_update_var...

  - (* step_assign_expr_err *)
    inv TS. exploit transl_expr_correct... Error.

  - (* step_assign_rule_err *)
    inv TS. exploit transl_expr_correct...
    intros [rb' [EX [ME' [RR _]]]]. simpl in *.
    exploit match_env_tags... simpl. unfold getTag.
    destruct (rb'#rx) as [xx [tt'|]] eqn:RBMR;
    [ injection 1 as ->
    | inversion 1].
    Error.
    + eapply plus_one_plus...
      eapply exec_Imov_err...
      simpl; rewrite H1.
      destruct dnd_assignTR as [prop|];
      [ erewrite prop, H1
      | ]...

    (* step_ifthenelse *) - {
    inv TS.

  - (* step_ifthenelse *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov; [apply H7| | |reflexivity|]...
    intros EX_Dsave.
    assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
      assert (RB2RP: B2 # rj = (v, inr p)). {
        rewrite RR2, RR1, Regmap.gss... }
      assert (TK': tr_cont (body tf) map ndef nret rret dstk B2
                       lk   n1 (* ns *)). {
        eapply tr_cont_rb... intros * A. destruct (H23 _ A).
        rewrite RR2, RR1, Regmap.gso... intros <-... }
    assert (
      plus step tge
        (State tf ne p B cs)
        (State tf (if eval_comp c v1 v2 then ntrue else nfalse) p' B2 cs))
    as EX. {
      eapply one_plus_plus ; [ apply EX_Dsave|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2|apply BR2| | |]...
    }
    destruct (eval_comp c v1 v2);
    [ exists (State tf ntrue  p' B2 cs)
    | exists (State tf nfalse p' B2 cs)];
   (split;
    [ left; exact EX
    | repeat (econstructor; eauto)] ).


  - (* step_ifthenelse no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    assert (TK': tr_cont (body tf) map ndef nret rret dstk B2 lk   n1 (* ns *)). {
      eapply tr_cont_rb... intros * A. destruct (H19 _ A).
      rewrite RR2, RR1... }
    assert (
      plus step tge
        (State tf ne p B cs)
        (State tf (if eval_comp c v1 v2 then ntrue else nfalse) p' B2 cs))
    as EX. {
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2|apply BR2| | |]...
    }
    destruct (eval_comp c v1 v2);
    [ exists (State tf ntrue  p' B2 cs)
    | exists (State tf nfalse p' B2 cs)];
   (split;
    [ left; exact EX
    | econstructor; eauto; econstructor 3; eauto]).
    + intros *. destruct (H1 p0 initPCT p)...
    + intros *. destruct (H1 p0 initPCT p)...

  - (* step_ifthenelse no joins *)
    destruct H1 as [X [Y ?]].
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    assert (TK': tr_cont (body tf) map ndef nret rret dstk B2 lk   n1 (* ns *)). {
      eapply tr_cont_rb... intros * A. destruct (H18 _ A).
      rewrite RR2, RR1... }
    assert (
      plus step tge
        (State tf ne p B cs)
        (State tf (if eval_comp c v1 v2 then ntrue else nfalse) p' B2 cs))
    as EX. {
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2|apply BR2| | |]...
    }
    destruct (eval_comp c v1 v2);
    [ exists (State tf ntrue  p' B2 cs)
    | exists (State tf nfalse p' B2 cs)];
   (split;
    [ left; exact EX
    | econstructor; eauto; econstructor 4; eauto]). }

    (* step_ifthenelse_errl *) - {
    inv TS.

  - (* step_ifthenelse_errl *)
    destruct (B#rj) as [v tp] eqn:RBJ.
    exploit exec_Imov;[apply H5| | |reflexivity|]...
    intros EX_Dsave.
    assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    specialize (transl_expr_correct _ _ _ _ H)...
    unfold transl_expr_prop; simpl.
    intros EX_err. Error.
    + eapply one_plus_plus...

  - (* step_ifthenelse_errl no saves *)
    specialize (transl_expr_correct _ _ _ _ H)...
    unfold transl_expr_prop; simpl.
    intros EX_err. Error...

  - (* step_ifthenelse_errl no joins *)
    specialize (transl_expr_correct _ _ _ _ H)...
    unfold transl_expr_prop; simpl.
    intros EX_err. Error... }

    (* step_ifthenelse_errr *) - {
    inv TS.

  - (* step_ifthenelse_errr *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H6| | |reflexivity|]...
    intros EX_Dsave.
    assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros EX_err. simpl in *. Error.
    + eapply one_plus_plus; [ apply EX_Dsave|].
      eapply plus_trans...

  - (* step_ifthenelse_errr no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros EX_err. simpl in *. Error.
    + eapply plus_trans...

  - (* step_ifthenelse_errr no joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros EX_err. simpl in *. Error.
    + eapply plus_trans... }

    (* step_ifthenelse_rule_err *) - {
    inv TS.

  - (* step_ifthenelse_rule_err  *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H7| | |reflexivity|]...
    intros EX_Dsave.
    assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]].
    simpl in *. Error.
    + eapply one_plus_plus ; [ apply EX_Dsave|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond_err...
      * rewrite RR2...
      * simpl. now rewrite H2.

  - (* step_ifthenelse_rule_err no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]].
    simpl in *. Error.
    + eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond_err...
      * rewrite RR2...
      * simpl. now rewrite H2.

  - (* step_ifthenelse_rule_err no joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]].
    simpl in *. Error.
    + eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond_err...
      * rewrite RR2...
      * simpl. now rewrite H2. }

    (* step_while_true *) - {
    inversion TS; subst.

  - (* step_while_true *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H7| | |reflexivity|]...
    intros EX_Dsave.
    assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [RBR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [RBR2 RR2]]]]. simpl in *.
    eexists. split.
    + left.
      eapply one_plus_plus ; [ apply EX_Dsave|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2| | | |]...
    + econstructor; eauto. econstructor 2...
      * erewrite RR2, RR1, Regmap.gss...
      * econstructor...
      * econstructor...
        eapply tr_cont_rb...
        intros * A. destruct (H23 _ A).
        rewrite RR2, RR1, Regmap.gso...
        intros <-...

  - (* step_while_true no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [RBR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [RBR2 RR2]]]]. simpl in *.
    eexists. split.
    + left.
      eapply one_plus_plus ; [Exec_real_nop|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2| | | |]...
    + econstructor; eauto. econstructor 3...
      * intros. simpl.
        destruct (H3 p0 initPCT p) as [_ [? _]]...
      * econstructor 1...
        eapply tr_cont_rb...
        intros * A. destruct (H20 _ A).
        rewrite RR2, RR1...

  - (* step_while_true no joins *)
    destruct H3 as [? [? [X [Y ?]]]].
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [RBR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [RBR2 RR2]]]]. simpl in *.
    eexists. split.
    + left.
      eapply one_plus_plus ; [Exec_real_nop|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond    ; [|rewrite RR2| | | |]...
    + econstructor... econstructor 4...
      econstructor... eapply tr_cont_rb...
      intros * A. destruct (H18 _ A).
      rewrite RR2, RR1... }

    (* step_while_false *) - {
    inversion TS; subst.

  - (* step_while_false with joins *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H8| | |reflexivity|]...
    intros EX_Dsave.
      assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
      assert (B2RJ: B2#rj = (v, inr p))
      by now rewrite RR2, RR1, Regmap.gss.
    exploit exec_Imov;[apply H14| | | |]...
    { simpl. now rewrite H3. }
    intros EX_Dexit.  eexists. split.
    + left.
      eapply one_plus_plus ; [ apply EX_Dsave|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_trans    ; [eapply EX2|].
      eapply one_one_plus  ; [eapply exec_Icond|eapply EX_Dexit]...
      { rewrite RR2... }
      { simpl. now rewrite H2. }
    + econstructor...
      * econstructor.
      * eapply tr_cont_rb... intros * A.
        destruct (H24 _ A).
        assert (req: r <> rj) by (intros <-; eauto).
        rewrite Regmap.gso, RR2, RR1,
        Regmap.gso...

  - (* step_while_false no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    destruct (H4 p1 p initPCT) as [_ [_ X]].
    rewrite X in H3.
    exploit exec_Inop; [apply H16|eapply H3 |]...
    intros EX_Dexit.  eexists. split.
    + left.
      eapply one_plus_plus ; [eapply exec_Inop; eauto; apply real_nopTR|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_trans    ; [eapply EX2|].
      eapply one_one_plus  ; [eapply exec_Icond|eapply EX_Dexit]...
      { rewrite RR2... }
      { simpl. now rewrite H2. }
    + econstructor...
      * econstructor.
      * eapply tr_cont_rb... intros * A.
        destruct (H21 _ A). rewrite RR2, RR1...

  - (* step_while_false no joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    eexists. split.
    + left.
      eapply one_plus_plus ; [eapply exec_Inop;[eauto|apply real_nopTR]|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_one_plus ; [eapply EX2|].
      eapply exec_Icond...
      * rewrite RR2...
      * simpl. now rewrite H2.
    + repeat (econstructor; eauto).
      * eapply tr_cont_rb... intros * A.
        destruct (H19 _ A). rewrite RR2, RR1...
      * decompose [and] H4. apply H16 in H3... }

    (* step_while_expr_errl *) - {
    inv TS.

  - (* step_while_expr_errl *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H4| | |reflexivity|]...
    intros EX_Dsave.
      assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros EX_err. Error.
    + eapply one_plus_plus; [eapply EX_Dsave|]...

  - (* step_while_expr_errl no saves*)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros EX_err. Error.
    + eapply one_plus_plus; [Exec_real_nop|]...

  - (* step_while_expr_errl no joins *)
    Error. eapply one_plus_plus.
    + eapply exec_Inop... now simpl. 
    + specialize (transl_expr_correct _ _ _ _ H).
      unfold transl_expr_prop; simpl... }

    (* step_while_expr_errr *) - {
    inv TS.

  - (* step_while_expr_errr with joins *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H5| | |reflexivity|]...
    intros EX_Dsave.
      assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros EX_err. Error.
    + eapply one_plus_plus; [eapply EX_Dsave|].
      eapply plus_trans   ; [eapply EX1|]...

  - (* step_while_expr_errr ignoring joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros EX_err. Error.
    + eapply one_plus_plus; [Exec_real_nop|].
      eapply plus_trans   ; [eapply EX1|]...

  - (* step_while_expr_errr ignoring joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].  Error.
    eapply one_plus_plus; [Exec_real_nop|].
    eapply plus_trans;    [ eapply EX1|].
    specialize (transl_expr_correct _ _ _ _ H0).
    unfold transl_expr_prop; simpl... }

    (* step_while_rule_err *) - {
    inv TS.

  - (* step_while_rule_err *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H6| | |reflexivity|]...
    intros EX_Dsave.
      assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    Error.
    + eapply one_plus_plus; [eapply EX_Dsave|].
      eapply plus_trans   ; [eapply EX1|].
      eapply plus_one_plus; [eapply EX2|].
      eapply exec_Icond_err...
      * rewrite RR2...
      * simpl. now rewrite H2.

  - (* step_while_rule_err no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    Error.
    + eapply one_plus_plus; [Exec_real_nop|].
      eapply plus_trans   ; [eapply EX1|].
      eapply plus_one_plus; [eapply EX2|].
      eapply exec_Icond_err...
      * rewrite RR2...
      * simpl. now rewrite H2.

  - (* step_while_rule_err no joins *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    Error.
    eapply one_plus_plus; [Exec_real_nop|].
    eapply plus_trans   ; [eapply EX1|].
    eapply plus_one_plus; [eapply EX2|].
    eapply exec_Icond_err...
   * rewrite RR2...
    * simpl. now rewrite H2. }

    (* step_while_false_err *) - {
    inv TS.

  - (* step_while_false_err *)
    destruct (B#rj) as [v tp] eqn:BRJ.
    exploit exec_Imov;[apply H8| | |reflexivity|]...
    intros EX_Dsave.
      assert (MErp: match_env map E (B # rj <- (v,inr p)))
      by (apply match_env_update_temp;eauto).
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
      assert (X: B2 # rj = (v, inr p)). {
        rewrite RR2, RR1, Regmap.gss... }
    exploit exec_Imov_err;[|exact X| | |]...
    { simpl; now rewrite H3. } intros EX_err. Error.
    + eapply one_plus_plus ; [ apply EX_Dsave|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_trans    ; [eapply EX2|].
      eapply one_one_plus  ; [          |eapply EX_err].
      eapply exec_Icond; [|rewrite RR2| | | |]...

  - (* step_while_false_err no saves *)
    exploit (transl_expr_correct _ _ _ _ H)...
    intros [B1 [EX1 [ME1 [BR1 RR1]]]].
    exploit (transl_expr_correct _ _ _ _ H0)...
    intros [B2 [EX2 [ME2 [BR2 RR2]]]]. simpl in *.
    exploit exec_Inop_err;[exact H16| |]...
    { simpl. destruct (H4 p1 p initPCT) as [_ [_ ?]].
      rewrite H5 in H3... }
    intros EX_err. Error.
    + eapply one_plus_plus ; [Exec_real_nop|].
      eapply plus_trans    ; [eapply EX1|].
      eapply plus_trans    ; [eapply EX2|].
      eapply one_one_plus  ; [          |eapply EX_err].
      eapply exec_Icond; [|rewrite RR2| | | |]...


  - (* step_while_false_err no joins *)
    exfalso. decompose [and] H4. eapply H13... }


  - (* step_call *)
    inv TS. destruct
      (functions_tred TRANSL H0)   as [tcallee [smTg smAr]],
      (tr_function_preserves smTg) as [tfntag tsig].
    exploit transl_exprlist_correct...
    intros [rb' [EX [ME' [RBRG RO]]]]. eexists. split.
    + left. eapply star_one_plus;[eexact EX|].
      eapply exec_Icall...
      * simpl in *. rewrite tsig, H1.
        specialize (eq_refl (List.length (rb' ## rargs))) as X.
        rewrite RBRG in X at 1.
        repeat rewrite map_length in X...
      * exploit getTags_atms...
        intros ->. unfold IcallTR.
        unfold inject, injectVTs.
        now rewrite tfntag, getWVTags_obv, H3.
    + repeat (econstructor; eauto).
      eapply tr_cont_rb...
      intros. rewrite RO...

  - (* step_call_args_err *)
    inv TS. exploit transl_exprlist_correct... Error.

  - (* step_call_rule_err *)
    inv TS. destruct
      (functions_tred TRANSL H0)   as [tcallee [smTg smAr]],
      (tr_function_preserves smTg) as [tfntag tsig].
    exploit transl_exprlist_correct...
    intros [rb' [EX [ME' [RBRG RO]]]]. Error.
    eapply star_one_plus;[eexact EX|].
    eapply exec_Icall_err...
    + simpl in *. rewrite tsig, H1.
      specialize (eq_refl (List.length (rb' ## rargs))) as X.
      rewrite RBRG in X at 1.
      repeat rewrite map_length in X...
    + exploit getTags_atms...
      intros ->. unfold IcallTR.
      unfold inject, injectVTs.
      now rewrite tfntag, getWVTags_obv, H3.


  - (* step_pass_control *)

    inv TF. econstructor; split.
    + left. apply plus_one. eapply exec_pass_control...
    + repeat (econstructor; eauto).



    (* Return Steps *)

  - (* step_skip_return *)
    inv TS. inv TK. inv MStk. eexists. split.
    + left. eapply one_one_plus; [eapply exec_Imovi|]...
      * reflexivity.
      * now simpl.
      * eapply exec_Ireturn...
        --now rewrite Regmap.gss.
        --simpl. change defVT with (STags.defVT).
          now rewrite H.
    + rewrite Regmap.gss. econstructor...

  - (* step_skip_return_err *)
    inv TS. inv TK. inv MStk. Error. eapply one_one_plus.
    + eapply exec_Imovi;[eauto| |]; now simpl.
    + eapply exec_Ireturn_err; [|rewrite Regmap.gss| |]...



  - (* step_return *) 
    inv TS. destruct (local_cont_end TK) as [_ Hret].
    inv MStk. exploit transl_expr_correct...
    intros [rb' [EX [_ [RB'RD _]]]]. eexists. split.
    + left. eapply plus_trans; [eapply EX|].
      simpl in RB'RD. destruct rb' # rret eqn:RB'ET.
      eapply one_one_plus; [eapply exec_Imov|]...
      { now simpl. }
      * eapply exec_Ireturn...
        --rewrite Regmap.gss...
        --simpl. now rewrite H1.
    + rewrite Regmap.gss. econstructor...

  - (* step_return_expr_err *)
    inv TS. exploit transl_expr_correct...
    Error.

  - (* step_return_rule_err *)
    inv TS. destruct (local_cont_end TK) as [_ Hret].
    inv MStk. exploit transl_expr_correct...
    intros [rb' [EX [_ [RB'RD RO]]]]. Error.
    eapply plus_trans; [eapply EX|]...
    simpl in RB'RD. destruct rb' # rret eqn: RB'ET.
    eapply one_one_plus; [eapply exec_Imov|]...
    + now simpl.
    + eapply exec_Ireturn_err...
      * rewrite Regmap.gss...
      * simpl. now rewrite H1.


  - (* step_return_control *)
    inv MA. inv MStk. eexists. split.
    + left. apply plus_one. econstructor; simpl...
    + (econstructor; eauto).
      * econstructor.
      * eapply tr_cont_rb... intros.
        rewrite Regmap.gso... intros ->...
        eapply tr_cont_dstk_map_disjoint...
        exists x...
      * eapply match_env_update_var...
Qed.




Lemma transl_initial_states_ex:
  forall S, SSem.initial_state  prog S ->
  exists R, TSem.initial_state tprog R /\ match_states S R.
Proof.
  inversion 1. destruct S; inv H1. inv TRANSL.
  - inversion H0.
  - injection H0 as -> ->. eexists; split;
    repeat econstructor; eauto.
Qed.



Lemma transl_final_states:
  forall S R a, match_states S R -> SSem.final_state S a ->
  exists ta, TSem.final_state R ta /\ match_atom a ta.
Proof.
  intros * MS H. inv H. inv MS.
  inv MStk. exists ta. split;
  [ econstructor
  | auto].
Qed.

Lemma transl_error_states:
  forall S R e, match_states S R -> SSem.error_state S e ->
  exists te, TSem.error_state R te /\ match_TagErr e te.
Proof.
  inversion 2; subst. inv H.
  exists te; split; [econstructor|auto].
Qed.


Section TopLevel.

Let SrcProg : semantics :=  HLL_semantics  prog.
Let TgtProg : semantics := RTLT_semantics tprog.

Theorem RTLgenT_FS : forward_simulation SrcProg TgtProg match_atom match_TagErr.
Proof with eauto with cocpit.
  eapply forward_simulation_star_wf;
  [ instantiate (1:=ms_paramed); exact transl_initial_states_ex
  | exact transl_final_states
  | exact transl_error_states
  | exact lt_state_wf
  | exact transl_step_correct].
Qed.




(* Our Toplevel correctness theorem *)
Theorem refinement_for_safe_programs :
  (forall behS, program_behaves SrcProg behS -> not_wrong behS) ->
   forall behT, program_behaves TgtProg behT -> exists behS,
  program_behaves SrcProg behS /\ behaviour_matches match_atom match_TagErr behS behT.
Proof.
  apply backward_simulation_same_safe_behavior,
  forward_to_backward_simulation;
  [ apply RTLgenT_FS
  | apply TSem.deterministic].
Qed.

Theorem forward_simulation_improves :
  forall behS, program_behaves SrcProg behS ->
  exists behT, program_behaves TgtProg behT /\
  behaviour_improves match_atom match_TagErr behS behT.
Proof.
  eapply forward_simulation_behavior_improves, RTLgenT_FS.
Qed.

End TopLevel.








Corollary transl_steps_correct:
  forall S1 S2, plus SSem.step ge S1 S2 ->
  forall R1, match_states S1 R1 ->
  exists R2,
  (plus TSem.step tge R1 R2 \/ (star TSem.step tge R1 R2 /\ lt_state S2 S1))
  /\ match_states S2 R2.
Proof with eauto.
  apply (@plus_ind2 _ _ _ _ (fun S1 SItmd =>
    forall R1, match_states S1 R1 -> exists RItmd,
        (    plus step tge R1 RItmd
          \/ star step tge R1 RItmd /\ lt_state SItmd S1)
     /\ match_states SItmd RItmd
  ));
  [ exact transl_step_correct
  | intros S1 SItmd S2 Stp transStp IH R1 MS].

  destruct (transl_step_correct S1 SItmd Stp R1 MS) as
    [RItmd [[Stp1I|[Stut1I Lt1I]] MSItmd]];
    (specialize (IH RItmd MSItmd) as
      [R2 [[StpI3|[StutI3 LtI3]] MS2]];
      (exists R2; split;[|exact MS2]));
        [| | |right]; try left.
  - eapply plus_trans...
  - eapply plus_star_plus...
  - eapply star_plus_plus...
  - split.
    + eapply star_trans...
    + eapply lt_state_trans...
Qed.

Corollary transl_initial_states_ex_RS:
  forall R, TSem.initial_state tprog R ->
  exists S, SSem.initial_state  prog S /\ match_states S R.
Proof.
  inversion 1. destruct R; inv H1. inv TRANSL.
  - inversion H0.
  - injection H0 as -> ->. eexists; split;
    repeat econstructor; eauto.
Qed.

Corollary transl_initial_states:
  forall S R, SSem.initial_state prog S ->
    TSem.initial_state tprog R -> match_states S R.
Proof.
  inversion 1. destruct S; inv H1.
  inversion 1. destruct R; inv H3.
  inv TRANSL.
  - inversion H0.
  - injection H2 as <- <-.
    injection H0 as -> <-.
    repeat constructor; auto.
Qed.


Corollary terminating_correct:
  forall (SIni SFin : SSem.state)
         (TIni : TSem.state)
    atm
    (EXs: plus SSem.step ge SIni SFin)
    (ISs: SSem.initial_state  prog SIni)
    (FSs: SSem.final_state SFin atm)
    (ISt: TSem.initial_state tprog TIni),
  exists TFin : TSem.state,
    plus TSem.step tge TIni TFin
 /\ TSem.final_state TFin ($atm).
Proof with eauto.
  intros. specialize (transl_initial_states _ _ ISs ISt) as MSI.
  specialize (transl_steps_correct _ _ EXs _ MSI)
    as [TF [[EXt|[EXt_star Hstut]] MSF]];
  specialize (transl_final_states _ _ _ MSF FSs) as [ta [FSt MA]];
  inv MA; exists TF; split... + inv EXt_star;
                                [inv ISt; inv FSt|econstructor]...
Qed.


Corollary terminating_correct_star:
  forall (SIni SFin : SSem.state)
         (TIni : TSem.state)
         atm
    (EXs: star SSem.step ge SIni SFin)
    (ISs: SSem.initial_state  prog SIni)
    (FSs: SSem.final_state SFin atm)
    (ISt: TSem.initial_state tprog TIni),
  exists TFin : TSem.state,
    star TSem.step tge TIni TFin
 /\ TSem.final_state TFin ($atm).
Proof with eauto.
  intros.
  inversion EXs as [|a SItmd b Hstp Hstr A B]; [subst| subst a b].
  - inv ISs. inv FSs.
  - specialize (transl_initial_states _ _ ISs ISt) as MSI.
    exploit transl_steps_correct;[econstructor| |]...
    clear Hstp Hstr. intros [TFin [[Hpls|[Hstr _]] MSF]];
    specialize (transl_final_states _ _ _ MSF FSs) as [ta [FSt MA]];
    inv MA; exists TFin; split... + inv Hpls. eright...
Qed.


End CORRECTNESS.

End Functor.