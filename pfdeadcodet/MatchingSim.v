From Utils     Require Import Defns Smallstep Behaviours.
From CompCert  Require Import Coqlib Maps Lattice Kildall Errors.
From PIPE      Require Import TagDomain.
From HLL       Require Import Policy.
From RTLgenT   Require Import Inj.
From RGTpf     Require Import Inj.
From DeadcodeT Require Import DeadDomain Compiler.
Import ListNotations.

Module Functor (Export FTags  : TagDomain.FrontEnd)
               (Export HRules : HLL.Policy.Sig FTags)
               (Export HFlags : HLL.Policy.Props FTags HRules)
               (Export Tags   : TagDomain_MiddleTgn FTags)
               (Export Rules  : RTLT_Policy_Tgn FTags Tags HRules HFlags)
               (Export Lang   : RTLT.Language.Sig Tags)
               (Import Sem    : RTLT.Semantics.Sig Tags Rules Lang)
               (Import Flags  : RTLT_Policy_PropT FTags HRules HFlags Tags Rules Lang).

Create HintDb deadcodeDB.

Module Import Comp := DeadcodeT.Compiler.Functor Tags Rules Lang Sem Flags.

(* Matching of language constructs *)
(* Matching of functions and "under" are direct from the translation
   i.e. [transl_function] is [match_function] *)

Inductive match_prog : program -> program -> Prop :=
  | mprog_nil : match_prog [] []
  | mprog_cons: forall i it f tf p tp
                (EQ: i = it)
                (TF: transl_function f = OK tf)
                (MP: match_prog p tp),
                match_prog ((i,f) :: p) ((it,tf) :: tp).

Lemma transl_program_match:
  forall prog tprog, transl_program prog = OK tprog -> match_prog prog tprog.
Proof with try constructor; auto.
  induction prog as [|[f_id f] prog], tprog as [|[tf_id tf] tprog];
  [ 
  | inversion 1
  | intros X; monadInv X
  | intros X; monadInv X]...
Qed.


(* Matching of Semantics constructs *)

Definition match_atom (x y: atom) : Prop := x = y.
Definition match_TagErr (x y: TagErr) : Prop := x = y.
Hint Unfold match_atom match_TagErr : deadcodeDB.

(* two sets of register banks agree for all the  *)
Definition match_env (B1 B2: regbank) (nB: nbank) : Prop :=
  forall r, vagree B1#r B2#r (NB.get r nB).

Inductive match_stacks: stack -> stack -> Prop :=
  | match_stacks_nil :
      match_stacks Stknil Stknil
  | match_stacks_frame :
      forall rd f pc B tf tB an cs tcs
        (ANL : analyze f = Some an)
        (TF  : transl_function f = OK tf)
        (ME  : forall tv v,tv = v -> match_env (B#rd <- v) (tB#rd<- tv)
                     (transfer f pc an!!pc))
        (MStk: match_stacks cs tcs),
      match_stacks (Stackframe rd  f pc  B  cs)
                   (Stackframe rd tf pc tB tcs)
  | match_stacks_ret : forall p cs tp tcs
      (STp : tp = p)
      (MStk: match_stacks cs tcs),
      match_stacks (SretTR p cs) (SretTR tp tcs).


Inductive ms_paramed ma me : state -> state -> Prop :=
  | match_regular_states:
      forall cs f pc B tcs tf tB an p tp
        (TF  : transl_function f = OK tf)
        (STp : tp = p)
        (ANL : analyze f = Some an)
        (ME  : match_env B tB (transfer f pc an!!pc))
        (MStk: match_stacks cs tcs),
      ms_paramed ma me (State  f pc  p  B  cs)
                       (State tf pc tp tB tcs)

  | match_callstate : forall f args p cs tf targs tp tcs
        (TF  : transl_function f = OK tf)
        (SV  : targs = args)
        (STp : tp    = p)
        (MStk: match_stacks cs tcs),
      ms_paramed ma me (Callstate  f  args  p cs)
                       (Callstate tf targs tp tcs)

  | match_returnstate : forall a p cs ta tp tcs
        (MA  : ma a ta)
        (STp : tp = p)
        (MStk: match_stacks cs tcs),
      ms_paramed ma me (Returnstate  a  p  cs)
                       (Returnstate ta tp tcs)
  | match_errorstate: forall e te
        (MEr: me e te),
      ms_paramed ma me (Errorstate  e)
                       (Errorstate te).

Notation match_states := (ms_paramed match_atom match_TagErr).




(* Lemmas about the matching relations *)

Lemma nreg_agree: forall B1 B2 nB r,
  match_env B1 B2 nB -> vagree B1#r B2#r (nreg nB r).
Proof. intros * H. apply H. Qed.
Hint Resolve nreg_agree: deadcodeDB.

Lemma match_env_ge: forall B1 B2 nB nB',
  match_env B1 B2 nB -> NB.ge nB nB' -> match_env B1 B2 nB'.
Proof.
  intros ** r. apply nge_agree with (NB.get r nB); auto.
  apply H0.
Qed.

Lemma match_env_bot: forall B1 B2,
  match_env B1 B2 NB.bot.
Proof.
  intros ** r. unfold nreg.
  rewrite NB.get_bot.
  exact Logic.I.
Qed.

Lemma match_env_same: forall B nB, match_env B B nB.
Proof.
  intros ** r. apply vagree_same.
Qed.

Lemma match_env_update_1:
  forall B1 B2 nB v1 v2 nv r,
  match_env B1 B2 nB -> vagree v1 v2 nv ->
  match_env (B1#r <- v1) (B2#r <- v2) (NB.set r nv nB).
Proof.
  intros ** r. rewrite NB.gsspec, ! PMap.gsspec.
  destruct (peq r r0); auto.
Qed.

Lemma match_env_update: forall B1 B2 nB v1 v2 r,
  vagree v1 v2 (nreg nB r) ->
  match_env B1 B2 (NB.set r Dead nB) ->
  match_env (B1#r <- v1) (B2#r <- v2) nB.
Proof with auto.
  intros ** ?. specialize (H0 r0).
  rewrite NB.gsspec in H0.
  rewrite ! PMap.gsspec.
  destruct (peq r0 r) as [->|]...
Qed.

Lemma match_env_update_dead: forall e1 e2 ne v1 r,
  nreg ne r = Dead ->
  match_env e1 e2 ne -> match_env (e1#r <- v1) e2 ne.
Proof with auto.
  intros ** r0. rewrite PMap.gsspec.
  destruct (peq r0 r) as [->|]...
  unfold nreg in H. now rewrite H.
Qed.

Hint Resolve match_env_update_dead
             match_env_update_1
             match_env_update
             match_env_same : deadcodeDB.

Lemma add_need_all_match_env : forall B tB r ne,
  match_env B tB (add_need_all r ne) -> match_env B tB ne.
Proof with auto.
  intros * H r'. unfold add_need_all in H.
  pose proof (H r'). rewrite NB.gsspec in H0.
  destruct (peq r' r) as [-> |]...
  eapply nge_agree; [constructor 1|apply H0].
Qed.

Lemma add_needs_all_match_env : forall rl B tB ne,
  match_env B tB (add_needs_all rl ne) -> match_env B tB ne.
Proof with eauto.
  induction rl as [|r rl IH]; simpl...
  intros **. apply IH.
  eapply add_need_all_match_env...
Qed.

Lemma match_env_live : forall {B tB r ne a}
  (Br : B # r = a)
  (ME : match_env B tB (add_need_all r ne)),
tB # r = a.
Proof.
  intros. unfold add_need_all in ME.
  pose proof (ME r). rewrite NB.gsspec in H.
  destruct (peq r r);[|congruence].
  now rewrite <- H.
Qed.

Hint Resolve add_need_all_match_env
             add_needs_all_match_env
             match_env_live : deadcodeDB.


Lemma match_env_lives : forall {B tB rl ne al}
  (Brl : B ## rl = al)
  (ME  : match_env B tB (add_needs_all rl ne)),
tB ## rl = al.
Proof with eauto with deadcodeDB.
  induction rl as [| r rl IH], al as [|a al];
  simpl; intros; eauto; inv Brl.
  f_equal...
Qed.

Lemma match_env_lives_tags : forall {B tB rl ne ts}
  (Brl : getTags B rl = ts)
  (ME  : match_env B tB (add_needs_all rl ne)),
getTags tB rl = ts.
Proof with eauto with deadcodeDB.
  induction rl as [| r rl IH], ts as [|t ts];
  simpl; intros; eauto; destruct (B # r) eqn:Br; inv Brl.
  - rewrite (match_env_live Br ME). f_equal.
    eapply IH...
Qed.

Lemma match_env_live2: forall {B tB r1 r2 ne a1 a2}
  (Br1 : B # r1 = a1)
  (Br2 : B # r2 = a2)
  (ME  : match_env B tB (add_needs_all [r1; r2] ne)),
tB # r1 = a1 /\ tB # r2 = a2.
Proof with eauto.
  intros **.
  assert (B ## [r1;r2] = [a1;a2]) by
  (simpl;repeat (try f_equal;eauto)).
  pose proof (match_env_lives H ME).
  inv H0...
Qed.

Hint Resolve match_env_lives
             match_env_lives_tags
             match_env_live2 : deadcodeDB.

Lemma is_dead_sound_1:
  forall nv, is_dead_atm nv = true -> nv = Dead.
Proof.
  destruct nv; simpl; congruence.
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead_atm nv = false -> nv = Live.
Proof.  destruct nv; simpl; congruence. Qed.



Lemma transl_function_at:
  forall {f tf an pc tinst},
  transl_function f = OK tf ->
  analyze f = Some an ->
   f.(body)!pc = Some                    tinst ->
  tf.(body)!pc = Some(transl_instr an pc tinst).
Proof.
  intros. unfold transl_function in H.
  rewrite H0 in H. inv H. simpl.
  now rewrite PTree.gmap, H1.
Qed.
Hint Resolve transl_function_at : deadcodeDB.

Lemma functions_transled:
  forall {f tp id p}
    (MP  : match_prog p tp)
    (GEID: (mkge p) ! id = Some f),
  exists tf,
    transl_function f  = OK tf /\
    (mkge tp) ! id = Some tf.
Proof with auto.
  intros **. revert id f GEID.
  induction MP as [|id b f tf p tp <- H MF IH];
  simpl; intros i f'.
  - rewrite PTree.gempty. inversion 1.
  - rewrite PTree.gsspec.
    destruct (peq i id) as [<- | ?].
    + rewrite PTree.gss. injection 1 as <-.
      exists tf. split...
    + intros A. specialize (IH i f' A).
      rewrite PTree.gso...
Qed.







Lemma analyze_successors:
  forall f an pc tinst pc',
  analyze f = Some an ->
  f.(body)!pc = Some tinst ->
  In pc' (successors_tinst tinst) ->
  NA.ge an!!pc (transfer f pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2.
  destruct a; apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall cs f pc B tcs tf tB an pc' ti ne p tp
    (INSTR: f.(body)!pc = Some ti)
    (SUCC: In pc' (successors_tinst ti))
    (ANPC: an!!pc = ne)
    (STp: tp = p)
    (FUN: transl_function f = OK tf)
    (ANL: analyze f = Some an)
    (ENV: match_env B tB ne)
    (MS : match_stacks cs tcs),
  match_states (State  f pc'  p  B  cs)
               (State tf pc' tp tB tcs).
Proof with eauto.
  intros. econstructor...
  eapply match_env_ge... intros x.
  exploit analyze_successors...
  rewrite ANPC; simpl...
Qed.
Hint Resolve match_succ_states : deadcodeDB.


Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge :=  mkge prog.
Let tge := mkge tprog.


Ltac TransfInstr :=
  match goal with
  | [INSTR: (body _)!_ = Some _,
     FUN: transl_function _ = OK _,
     ANL: analyze _ = Some _ |- _ ] =>
       generalize (transl_function_at  FUN ANL INSTR);
       let TI := fresh "TI" in
       intro TI; unfold transl_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (body _)!?pc = Some _,
     ANL: analyze _ = Some ?an |- _ ] =>
       unfold transfer in *;
       rewrite INSTR in *
  end.

Ltac destructGuard :=
  match goal with
  | A: match_env _ _ (if ?b then _ else _) |- _ =>
    let g := fresh "G" in
    destruct b eqn:g; try destructGuard
  | A: andPFb ?f _ = true |- _ =>
    let x := fresh "Hdfs" in
    let y := fresh "Hlpcp" in
    let xy := fresh "XY" in
    destruct f as [xy|]; [destruct xy as [x y]|];
    unfold andPFb in A;
    (try match goal with
    | B: is_dead_atm ?b = true |- _ =>
      apply is_dead_sound_1 in B
    end); try destructGuard
  | A: false = true |- _ => inversion A
  end.


Ltac Error :=
  eexists; split;
  [|eapply match_errorstate; eauto with deadcodeDB].


Theorem step_simulation :
  forall S1 S2, step ge S1 S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' S2' /\ match_states S2 S2'.
Proof with eauto with deaddomDB deadcodeDB.
  induction 1; intros S1' MSTATE; inv MSTATE.

  - (* exec_Inop *)
    TransfInstr; UseTransfer.
    eexists; split.
    + eapply exec_Inop...
    + eapply match_succ_states...
      left...


  - (* exec_Inop_err *)
    TransfInstr. Error.
    eapply exec_Inop_err...





    (* exec_Imov *) - {
    TransfInstr; UseTransfer. destructGuard;
    [| destruct (it_eq_dec itag ITassign) as [->|] ].

  - (* optimized - reg & rule are dead *)
    eexists; split.
    + eapply exec_Inop...
      apply real_nopTR.
    + eapply match_succ_states...
      * left...

  - (* not optimized -- assignTR doesn't need dest tag *)
    pose proof (match_env_live H0 ME) as tBs.
    apply add_need_all_match_env in ME. {
    destruct (dnd_ImovTR ITassign) eqn:adnd.
    - eexists; split.
      + destruct (tB # rd) eqn:tBd.
        eapply exec_Imov...
        * erewrite e, H2...
      + eapply match_succ_states...
        * left...
    - eexists; split.
      + eapply exec_Imov...
      + eapply match_succ_states...
        * left... }

  - (* not optimized -- assignTR needs dest tag *)
    rewrite (not_ass_mov_dnd n) in ME.
    pose proof (match_env_live H0 ME) as tBs.
    apply add_need_all_match_env in ME.
    pose proof (match_env_live H1 ME) as tBd.
    apply add_need_all_match_env in ME.
    eexists; split.
    + eapply exec_Imov...
    + eapply match_succ_states...
      * left... }


    (* exec_Imov_err *) - {
    TransfInstr; UseTransfer. destructGuard;
    [| destruct (it_eq_dec itag ITassign) as [->|] ].

  - (* optimized *)
    edestruct Hdfs...

  - (* not optimized -- assignTR *)
    pose proof (match_env_live H0 ME) as tBs.
    apply add_need_all_match_env in ME.
    Error. destruct (dnd_ImovTR ITassign) eqn:adnd.
    + destruct (tB # rd) eqn:tBd.
      * eapply exec_Imov_err...
        erewrite e, H2...
    + eapply exec_Imov_err...

  - (* not optimized *)
    rewrite (not_ass_mov_dnd n) in ME.
    pose proof (match_env_live H0 ME) as tBs.
    apply add_need_all_match_env in ME.
    pose proof (match_env_live H1 ME) as tBd.
    apply add_need_all_match_env in ME.
    Error. eapply exec_Imov_err... }





    (* exec_Imovi *) - {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized both atom & rule dead *)
    eexists; split.
    + eapply exec_Inop...
      apply real_nopTR.
    + eapply match_succ_states...
      * left...

  - (* non optimized *)
    eexists; split.
    + eapply exec_Imovi...
    + eapply match_succ_states...
      * left... }


    (* exec_Imovi_err *) - {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized - both atom & rule dead *)
    exfalso. eapply Hdfs...

  - (* non optimized *)
    Error. eapply exec_Imovi_err... }





    (* exec_Iop *) - {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized both atom & rule dead *)
    eexists; split.
    + eapply exec_Inop...
      apply real_nopTR.
    + eapply match_succ_states...
      * left...

  - (* not optimized *)
    pose proof (match_env_live2 H0 H1 ME) as [tB1 tB2].
    eexists; split.
    + eapply exec_Iop...
    + eapply match_succ_states...
      * left... }


    (* exec_Iop_err *) - {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized - both atom & rule dead *)
    exfalso. eapply Hdfs...

  - (* non optimized *)
    pose proof (match_env_live2 H0 H1 ME) as [tB1 tB2].
    Error. eapply exec_Iop_err... }





  - (* exec_Icond *) {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized *)
(*     destruct (peq nt nf) as [<-|]; [|inv G]. *)
    eexists; split.
    + eapply exec_Inop...
      apply real_nopTR.
    + replace nf with nt by
      (destruct (peq nt nf) as [<-|];[auto|inv G]).
      replace (if eval_comp c v1 v2 then nt else nt)
      with nt by (destruct (eval_comp c v1 v2); auto).
      eapply match_succ_states...
      * left...

  - (* same *)
    pose proof (match_env_live2 H0 H1 ME) as [tB1 tB2].
    eexists; split.
    + eapply exec_Icond...
    + eapply match_succ_states...
      * destruct (eval_comp c v1 v2);
        [|right]; left... }


  - (* exec_Icond_err *) {
    TransfInstr; UseTransfer.
    destructGuard.

  - (* optimized - both atom & rule dead *)
    exfalso. eapply Hdfs...

  - (* non optimized *)
    pose proof (match_env_live2 H0 H1 ME) as [tB1 tB2].
    Error. eapply exec_Icond_err... }





  - (* exec_Icall *)
    TransfInstr; UseTransfer. rename tf into tcer.
    destruct (functions_transled TRANSL H0) as [tcee [TF' ?]],
             (tr_function_preserves TF') as [tfntag [tsig _]].
    pose proof (match_env_lives (eq_refl (B ## args)) ME).
    eexists; split.
    + eapply exec_Icall...
      * transitivity (arity cee)...
      * erewrite tfntag,
        match_env_lives_tags...
    + do 3 (econstructor; eauto).
      intros * <-.
      eapply match_env_ge. apply match_env_update...
      eapply analyze_successors... left...


  - (* exec_Icall_err *)
    TransfInstr; UseTransfer. rename tf into tcer.
    destruct (functions_transled TRANSL H0) as [tcee [TF' ?]],
             (tr_function_preserves TF') as [tfntag [tsig _]].
    Error. eapply exec_Icall_err...
    + transitivity (arity cee)...
    + erewrite tfntag,
      match_env_lives_tags...

  - (* exec_pass_control *)
    rename tf into tcee.
    pose proof TF as TF'.
    unfold transl_function in TF'.
    destruct (analyze cee) eqn:X;[| inv TF'].
    eexists; split.
    + eapply exec_pass_control.
    + rewrite (tr_function_params TF).
      rewrite (tr_function_entry  TF).
      econstructor...





  - (* exec_Ireturn *)
    inv MStk. rename tcs0 into tcs,
    MStk0 into MStk. TransfInstr; UseTransfer.
    pose proof (match_env_live H1 ME).
    eexists; split.
    + eapply exec_Ireturn...
    + econstructor...


  - (* exec_Ireturn_err *)
    inv MStk. rename tcs0 into tcs,
    MStk0 into MStk. TransfInstr; UseTransfer.
    Error. eapply exec_Ireturn_err...





  - (* exec_return_control *)
    inv MStk. rename MStk0 into MStk,
    tcs0 into tcs. inv MA.
    eexists; split;
    [ eapply exec_return_control
    | econstructor]...
Qed.


Lemma transl_initial_states_ex:
  forall S, initial_state  prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros **. inv TRANSL; inv H.
  - inv H0.
  - injection H0 as -> <-. eexists;
    split; repeat econstructor; auto.
Qed.

Lemma transl_final_states:
  forall S R a, match_states S R -> final_state S a ->
  exists ta, final_state R ta /\ match_atom a ta.
Proof.
  intros * MS FIN. inv FIN. inv MS.
  inv MStk. exists ta. split;
  [ econstructor
  | auto].
Qed.

Lemma transl_error_states:
  forall S R e, match_states S R -> error_state S e ->
  exists te, error_state R te /\ match_TagErr e te.
Proof.
  inversion 2; subst. inv H.
  exists te; split; [econstructor|auto].
Qed.


Section TopLevel.
Let SrcProg : semantics := Sem.RTLT_semantics  prog.
Let TgtProg : semantics := Sem.RTLT_semantics tprog.

Remark DeadcodeT_FS : forward_simulation SrcProg TgtProg match_atom match_TagErr.
Proof with eauto with cocpit.
  eapply forward_simulation_lockstep;
  [ instantiate (1:=ms_paramed); exact transl_initial_states_ex
  | exact transl_final_states
  | exact transl_error_states
  | exact step_simulation].
Qed.

Theorem refinement_for_safe_programs :
  (forall behS, program_behaves SrcProg behS -> not_wrong behS) ->
   forall behT, program_behaves TgtProg behT -> exists behS,
  program_behaves SrcProg behS /\ behaviour_matches match_atom match_TagErr behS behT.
Proof.
  apply backward_simulation_same_safe_behavior,
  forward_to_backward_simulation;
  [ apply DeadcodeT_FS
  | apply Sem.deterministic].
Qed.


Theorem forward_simulation_improves :
  forall behS, program_behaves SrcProg behS ->
  exists behT, program_behaves TgtProg behT /\
  behaviour_improves match_atom match_TagErr behS behT.
Proof.
  eapply forward_simulation_behavior_improves, DeadcodeT_FS.
Qed.

End TopLevel.


End PRESERVATION.
End Functor.