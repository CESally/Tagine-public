From CompCert Require Import Errors.
From Utils   Require Export Defns.
From RGTpf   Require Import Env Matching.
From RTLgenT Require Import Compiler.
From HLL     Require Import Language.
From RTLT    Require Import Language.


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

Module Import Spec := RGTpf.Matching.Functor
                        STags Source
                        TTags Target
                        CompEnv
                        SRules SFlags
                        TRules TFlags
                        SSem
                        TSem.
Module Import Comp := RTLgenT.Compiler.Functor
                        STags Source
                        TTags Target
                        CompEnv
                        SRules SFlags.

Import ListNotations.


(** * 1 Properties of the monad(ic machinery) *)

(** ** 1.1 Utility functions to extract information from monadic computations *)

Section RTLgenT_monad.

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: state) (i: state_earlier s1 s3),
  bind f g s1 = OK y s3 i -> exists x s2 i1 i2,
  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate. exists a; exists s'; exists s.
  destruct (g a s'); inv H. exists s0; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: state) (i: state_earlier s1 s3),
  bind2 f g s1 = OK z s3 i -> exists x y s2 i1 i2,
  f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
Proof.
  unfold bind2; intros.
  exploit bind_inversion; eauto.
  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x; exists y; exists s2; exists i1; exists i2; auto.
Qed.

Remark bind3_inversion:
  forall (A B C D: Type) (f: mon (A*B*C)) (g: A -> B -> C -> mon D)
         (w: D) (s1 s3: state) (i: state_earlier s1 s3),
  bind3 f g s1 = OK w s3 i -> exists x y z s2 i1 i2,
  f s1 = OK (x, y, z) s2 i1 /\ g x y z s2 = OK w s3 i2.
Proof.
  unfold bind3; intros.
  exploit bind_inversion; eauto.
  intros [[[x y] z] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x, y, z, s2, i1, i2. auto.
Qed.



Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
      discriminate
  | (ret _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "LATER" in (
      let i2 := fresh "LATER" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "LATER" in (
      let i2 := fresh "LATER" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
  | (bind3 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let x3 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "LATER" in (
      let i2 := fresh "LATER" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind3_inversion _ _ _ _ F G X S S' I H) as [x1 [x2 [x3 [s [i1 [i2 [EQ1 EQ2]]]]]]];
      clear H;
      try (monadInv1 EQ2)))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind3 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.


Ltac saturateTrans :=
  match goal with
  | H1: state_earlier ?x ?y, H2: state_earlier ?y ?z |- _ =>
      match goal with
      | H: state_earlier x z |- _ =>
         fail 1
      | _ =>
         let i := fresh "LATER" in
         (generalize (state_earlier_trans x y z H1 H2); intro i;
          saturateTrans)
      end
  | _ => idtac
  end.
(** *** Monotonicity properties of the state *)

(** We build a hint database [rtlg], collecting state monad facts and later facts
    about registers. *)


Lemma instr_at_earlier:
  forall s1 s2 n l,
  state_earlier s1 s2 -> s1.(st_code)!n = Some l -> s2.(st_code)!n = Some l.
Proof.
  intros. inv H.
  destruct (H3 n); congruence.
Qed.

Lemma add_instr_at:
  forall s1 s2 EARLIER instr itag n,
  add_instr instr itag s1 = OK n s2 EARLIER ->
  s2.(st_code)!n = Some (instr, itag).
Proof.
  intros. monadInv H. simpl. apply PTree.gss.
Qed.


(** *** Properties of [update_instr]. *)

Lemma update_instr_at:
  forall n instr itag s1 s2 EARLIER u,
  update_instr n instr itag s1 = OK u s2 EARLIER ->
  s2.(st_code)!n = Some (instr, itag).
Proof.
  intros. unfold update_instr in H.
  destruct (plt n (st_nextnode s1)); [|discriminate].
  destruct (check_empty_node s1 n); [|discriminate].
  inv H. simpl. apply PTree.gss.
Qed.


Hint Resolve state_earlier_refl
             instr_at_earlier
             add_instr_at
             update_instr_at: stateDB.












(** ** 1.2 Facts about registers *)


Create HintDb regDB.
Definition reg_valid (r: reg) (s: state) : Prop :=
  Plt r s.(st_nextreg).
Notation "r 'declared_by' s" := (reg_valid r s)
                                (no associativity, at level 200).

Definition reg_fresh (r: reg) (s: state) : Prop :=
  ~(Plt r s.(st_nextreg)).
Notation "r 'undeclared_in' s" := (reg_fresh r s)
                                  (no associativity, at level 200).


Definition regs_valid (rl: list reg) (s: state) : Prop :=
  forall r, In r rl -> reg_valid r s.

Definition map_valid (m: mapping) (s: state) : Prop :=
  forall r, reg_in_map m r -> reg_valid r s.


Definition decl_btwn (s s': state) (r: reg) : Prop :=
  reg_fresh r s /\ reg_valid r s'.
Hint Extern 0 (decl_btwn ?s1 ?s2 ?r) => split : regDB.



Lemma reg_valid_earlier:
  forall r s1 s2, state_earlier s1 s2 -> reg_valid r s1 -> reg_valid r s2.
Proof.
  inversion 1; subst. intros. eapply Plt_Ple_trans; eauto.
Qed. Hint Resolve reg_valid_earlier: regDB.

Lemma reg_fresh_earlier:
  forall r s1 s2, state_earlier s1 s2 -> reg_fresh r s2 -> reg_fresh r s1.
Proof.
  inversion 1; subst; intros ? ?. apply H3.
  eapply Plt_Ple_trans; eauto.
Qed.

Lemma regs_valid_earlier:
  forall s1 s2 rl, state_earlier s1 s2 -> regs_valid rl s1 -> regs_valid rl s2.
Proof. red; eauto with regDB. Qed.


Hint Resolve (* reg_valid_later *)
             reg_fresh_earlier
             reg_valid_earlier
             regs_valid_earlier: regDB.




Lemma valid_fresh_absurd:
  forall r s, reg_valid r s -> reg_fresh r s -> False.
Proof (fun _ _ H nH => nH H).

Lemma valid_fresh_different:
  forall r1 r2 s, reg_valid r1 s -> reg_fresh r2 s -> r1 <> r2.
Proof. intros * H nH <-. exact (nH H). Qed.

Lemma regs_valid_nil:
  forall s, regs_valid nil s.
Proof. red. inversion 1. Qed.

Lemma regs_valid_cons:
  forall r1 rl s,
  reg_valid r1 s -> regs_valid rl s -> regs_valid (r1 :: rl) s.
Proof. red. inversion 3; subst; auto. Qed.

Lemma regs_valid_app:
  forall rl1 rl2 s,
  regs_valid rl1 s -> regs_valid rl2 s -> regs_valid (rl1 ++ rl2) s.
Proof.
  red. intros until 3.
  apply in_app_iff in H1.
  destruct H1; auto.
Qed.

Lemma new_reg_valid:
  forall s1 s2 r EARLIER,
  new_reg s1 = OK r s2 EARLIER -> reg_valid r s2.
Proof.
  intros. monadInv H. red.
  simpl. apply Plt_succ.
Qed.

Lemma new_reg_fresh:
  forall s1 s2 r EARLIER,
  new_reg s1 = OK r s2 EARLIER -> reg_fresh r s1.
Proof.
  intros. monadInv H.
  unfold reg_fresh; simpl.
  exact (Plt_strict _).
Qed.

Hint Resolve valid_fresh_absurd
             valid_fresh_different
             regs_valid_nil
             (* regs_valid_cons *)
             (* regs_valid_app *)
             new_reg_valid
             new_reg_fresh: regDB.




(** ** 1.4 Properties of operations over compilation environments (mappings) *)

(** The initial (empty) mapping is valid *)

Create HintDb mapDB.





Lemma init_mapping_valid:
  forall s, map_valid init_mapping s.
Proof.
  intros s r [id A].
  rewrite PTree.gempty in A;
  discriminate.
Qed.

Lemma map_valid_earlier:
  forall s1 s2 m,
  state_earlier s1 s2 -> map_valid m s1 -> map_valid m s2.
Proof. red; eauto with regDB. Qed.


Lemma new_reg_not_in_map:
  forall s1 s2 m r EARLIER,
  new_reg s1 = OK r s2 EARLIER -> map_valid m s1 -> ~(reg_in_map m r).
Proof.
  intros * NR MV rim. apply MV in rim.
  apply new_reg_fresh in NR.
  eapply valid_fresh_absurd; eauto.
Qed.

(** *** Properties of [find_var]. *)

(** If a variable is mapped to a register, that register must be in the map. *)

Lemma find_var_in_map:
  forall s1 s2 map x rx EARLIER,
  find_var map x s1 = OK rx s2 EARLIER -> reg_in_map map rx.
Proof.
  intros until rx. unfold find_var.
  caseEq (map!x); intros * mx *;
  inversion 1; subst. exists x; auto.
Qed.
Hint Resolve find_var_in_map: mapDB.

Lemma find_var_valid:
  forall s1 s2 map x r EARLIER,
  find_var map x s1 = OK r s2 EARLIER -> map_valid map s1 -> reg_valid r s1.
Proof. eauto with mapDB. Qed.

Lemma find_var_unmonad:
  forall s1 s2 map x r EARLIER,
  find_var map x s1 = OK r s2 EARLIER -> map ! x = Some r.
Proof.
  unfold find_var. intros * H.
  destruct (map ! x); inv H. auto.
Qed.
Hint Resolve find_var_valid: mapDB.
Hint Resolve find_var_unmonad
             new_reg_not_in_map
             map_valid_earlier: mapDB.

(** *** Properties of [add_var]. *)

(** If we add a variable into a map in a state, and that map was valid in that
    state, then the resulting register and map are both valid in the resulting
    state.   (Recall that "valid" technically means different things for
    registers and maps.)   The resulting mapping being valid (right conjunct of
    the consequent) actually implies the resulting register being valid (left
    conjunct of the consequent), however, it is convenient to state the theorem
    this way. *)

Lemma add_var_valid:
  forall s1 s2 map1 map2 x rx LATER,
  add_var map1 x s1 = OK (rx, map2) s2 LATER ->
  map_valid map1 s1 ->
  reg_valid rx s2 /\ map_valid map2 s2.
Proof with eauto with stateDB regDB.
  intros. monadInv H. split...
  inversion EQ; subst. intros rx [x' A].
  rewrite PTree.gsspec in A.
  destruct (peq x' x); [inv A|]...
  apply reg_valid_earlier with s1...
  apply H0. exists x'...
Qed.

(** This is another function that extracts facts from the monadic computation.
 *)

Lemma add_var_find:
  forall s1 s2 map x rx map' EARLIER,
  add_var map x s1 = OK (rx,map') s2 EARLIER -> map'!x = Some rx.
Proof.
  intros. monadInv H. simpl. apply PTree.gss.
Qed.

(** Adding multiple variables has the same properties as adding one. Cf.
    [add_var_valid] above. *)

Lemma add_vars_valid:
  forall xs s1 s2 map map' rs EARLIER,
  add_vars map xs s1 = OK (rs, map') s2 EARLIER ->
  map_valid map s1 ->
  regs_valid rs s2 /\ map_valid map' s2.
Proof.
  induction xs; simpl; intros; monadInv H;
  [
  | exploit IHxs; eauto; intros [A B];
    exploit add_var_valid; eauto; intros [C D]];
  split; auto.
  - red; simpl; intros; tauto.
  - apply regs_valid_cons; eauto with regDB stateDB.
Qed.

(** Adding a variable, or variables, to a well formed map, preserves the map's
    well-formed-ness *)

Lemma add_var_inj:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i ->
  map_inj map -> map_valid map s1 -> map_inj map'.
Proof with eauto with regDB mapDB stateDB.
  intros. monadInv H.
  intros id1 id2 r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name),(peq id2 name); subst...
  - intros. inv H. elimtype False.
    apply valid_fresh_absurd with r0 s1;
    [ apply H1; exists id2|]...
  - intros. inv H2. elimtype False.
    apply valid_fresh_absurd with r0 s1;
    [ apply H1; exists id1|]...
Qed.


Lemma add_vars_inj:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_inj map -> map_valid map s1 -> map_inj map'.
Proof.
  induction names; simpl; intros; monadInv H.
  - auto.
  - exploit add_vars_valid; eauto. intros [A B].
    eapply add_var_inj; eauto.
Qed.


Lemma target_reg_decl_btwn : forall a ns s rd ne s' map LATER
  (WF: map_valid map s)
  (TR: transl_expr map a ns s = OK (rd,ne) s' LATER),
decl_btwn s s' rd.
Proof with eauto 3 with regDB mapDB.
  induction a; intros; try (monadInv TR); saturateTrans; split...
Qed.


Lemma target_reg_fresh : forall a ns s rd ne s' map LATER
  (WF: map_valid map s)
  (TR: transl_expr map a ns s = OK (rd,ne) s' LATER),
reg_fresh rd s.
Proof with eauto.
  intros. exploit target_reg_decl_btwn... intros [? _]...
Qed.

Lemma target_reg_valid : forall a ns s rd ne s' map LATER
  (WF: map_valid map s)
  (TR: transl_expr map a ns s = OK (rd,ne) s' LATER),
reg_valid rd s'.
Proof with eauto.
  intros. exploit target_reg_decl_btwn... intros [_ ?]...
Qed.

Hint Resolve target_reg_fresh
             target_reg_valid : regDB.



(* Lemma target_reg_decl_btwn_lka_aux : forall a ns s rd ne s' pri sec sec' LATER
  (WF: map_valid pri s)
  (TR: transl_el_aux pri sec a ns s = OK (rd,ne,sec') s' LATER),
reg_fresh rd s \/ reg_in_map sec rd.
Proof with eauto 3 with regDB mapDB.
  induction a; intros; try (monadInv TR); saturateTrans...  
  unfold transl_el_aux in TR.
  destruct sec ! i eqn:seci.
  - injection TR as <- <- <- <-. right. exists i...
  - monadInv TR...
Qed. *)












(* Lemma target_reg_fresh_or_in_map : forall a ns s rd ne s' map LATER
  (WF: map_valid map s)
  (TR: transl_expr map a ns s = OK (rd,ne) s' LATER),
    reg_fresh rd s(*  \/ reg_in_map map rd *).
Proof with eauto 2 with regDB mapDB.
  induction a; intros; try (monadInv TR); saturateTrans;
  [|right| |]; try left...
Qed. *)







(** ** 1.3 Properties of basic operations in the state monad *)



 (* declared between *)

(** The formal specification of the relationship between [transl_expr] and
    [tr_expr]. (There are two cases; one when the expression is the right value
    of some assignment, one when it is not. We do the "not" case first. *)
(** In addition to the translation function [TR], we need the other hypotheses
    to encapsulate some of the other conditions that will be made true in the
    setting up of functions, but do not directly follow from [TR]. *)
(** For example, [WF]: That the [map] to any given sub computation will be valid
    follows from the fact that the initial mapping is valid (Cf.
    [init_mapping_valid]) and that operations that change mappings (Cf.
    [add_var]/[s] & [transl_fun_aux] where [add_vars] is called) preserve their
    validity (Cf. [add_var_valid]/[add_vars_valid]). *)
(** [OK], [VALID] & [VALID2] arise from the [state_later] guarantees of registers
    for different subcomputations being distinct. *)

(** This proof proceeds by an induction over the expression being translated.
    We also annotate the [Eplus] case to illustrate some of the difficulties
    (and delights!) of working with the monadic computations. *)

Lemma match_set_locals:
  forall map1 s1,
  map_inj map1 ->
  forall il rl map2 s2 e rs i,
  match_env map1 e rs ->
  (forall r, reg_fresh r s1 -> rs#r = defAtom) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_locals il e) rs.
Proof with eauto.
  induction il as [| ih il IH]; simpl in *; intros;
  [inv H2|]... monadInv H2. monadInv EQ1. intros id v.
  simpl. repeat rewrite PTree.gsspec.
  destruct (peq id ih); intros; [|exploit IH]...
  subst ih. exists x1. split... inv H2.
  apply H1. eauto 3 with mapDB regDB.
Qed.


Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_params il vl) (init_regs ($ vl) rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs ($ vl) rl)#r = defAtom).
Proof with eauto 3 with regDB mapDB stateDB.
  induction il as [| ih il IH]; intros * AVIM.
  - inv AVIM; split;
    [ apply match_env_empty
    | intros; simpl; apply Regmap.gi].
  - monadInv AVIM. simpl.
    exploit add_vars_valid;
    [ eauto
    | apply init_mapping_valid
    | intros [A B]].
    exploit add_var_valid... intros [C _].
    monadInv EQ1. destruct vl as [| vh vl].
    + (* vl = nil *)
      destruct (IH _ _ _ _ nil _ EQ) as [ME UNDEF]... split;
      [ intros [] v H; inv H
      | intros; apply Regmap.gi].
    + (* vl = v1 :: vs *)
      destruct (IH _ _ _ _ vl _ EQ) as [ME UNDEF]. split.
      * intros id v. repeat rewrite PTree.gsspec.
        destruct (peq id ih); intros * D.
        --injection D as ->. subst ih; exists x1;
          split; [|simpl; rewrite Regmap.gss]...
        --destruct (ME _ _ D) as [r [E F]].
          exists r; split... simpl. rewrite Regmap.gso...
          eapply valid_fresh_different...
          apply B. exists id...
      * intros. simpl. rewrite Regmap.gso...
        apply not_eq_sym. apply valid_fresh_different with s2...
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  tvparams = $ vparams ->
  match_env map2 (set_locals vars (set_params params vparams))
            (init_regs tvparams rparams).
Proof with eauto.
  intros * AVIM AVM1 ->.
  exploit match_set_params_init_regs...
  intros [ME RR]. eapply match_set_locals...
  eapply add_vars_inj...
  - apply init_mapping_inj.
  - apply init_mapping_valid.
Qed.






Lemma tr_expr_earlier:
  forall s1 s2, state_earlier s1 s2 ->
  forall map mdfy a ns nd rd,
  tr_expr s1.(st_code) map mdfy a ns nd rd ->
  tr_expr s2.(st_code) map mdfy a ns nd rd.
Proof.
  intros s1 s2 EXT.
  pose (AT := fun pc i => instr_at_earlier s1 s2 pc i EXT).
  induction 1; econstructor; eauto.
Qed.


Lemma tr_exprlist_earlier:
  forall s1 s2, state_earlier s1 s2 ->
  forall map mdfy al ns nd rl,
  tr_exprlist s1.(st_code) map mdfy al ns nd rl ->
  tr_exprlist s2.(st_code) map mdfy al ns nd rl.
Proof with eauto.
  intros s1 s2 EXT.
  pose (AT := fun pc i => instr_at_earlier s1 s2 pc i EXT).
  induction 1; econstructor...
  eapply tr_expr_earlier...
Qed.


Lemma tr_stmt_earlier: forall s1 s2
    (EARL12: state_earlier s1 s2)
    map s ne ns nret rret dstk
    (TS1: tr_stmt s1.(st_code) map nret rret s    ne ns dstk),
  tr_stmt s2.(st_code) map nret rret s    ne ns dstk.
Proof.
  intros * EXT. generalize tr_expr_earlier
    tr_exprlist_earlier. intros I1 I2 *.
  pose (AT := fun pc i => instr_at_earlier s1 s2 pc i EXT).
  induction 1; try solve [econstructor; eauto].
Qed.




(** * 1 Compiler specifications *)



(** Finally, we show that the compiler satisfies the specification. *)

Lemma transl_expr_charact:
  forall a map rd ne ns s s' EARLIER
     (TR: transl_expr map a ns s = OK (rd,ne) s' EARLIER)
     (WF: map_valid map s),
   tr_expr s'.(st_code) map (decl_btwn s s') a rd   ne ns.
Proof with eauto 5 with mapDB regDB stateDB.
  induction a as [| | op a1  IH1 a2 IH2]; intros;
  try (monadInv TR); saturateTrans.
  - (* Elit *)
    econstructor...
  - (* Evar *)
    econstructor...
  - (* Eop *)
    econstructor.
    + apply tr_expr_earlier with s3...
    + apply tr_expr_earlier with s2...
    + idtac...
    + idtac...
    + idtac...
    + intros [? ?]...
    + intros r [[]|[]]...
Qed.



Lemma transl_exprlist_charact:
  forall es map rs ne ns s s' EARLIER
     (TR: transl_exprlist map es ns s = OK (rs,ne) s' EARLIER)
     (WF: map_valid map s),
   tr_exprlist s'.(st_code) map (decl_btwn s s') es rs   ne ns.
Proof with eauto 3 with mapDB regDB stateDB.
  (* lists *)
  induction es; intros; try (monadInv TR); saturateTrans.
  - left. intros r []...
  - econstructor.
    + eapply transl_expr_charact...
    + apply tr_exprlist_earlier with s0...
    + intros []. apply target_reg_fresh in EQ1...
    + intros r [[]|[]]...
Qed.



Lemma transl_stmt_charact:
  forall map s ne ns nret rret s1 s2 EARLIER jstk
    (TR: transl_stmt map s ns nret rret s1 = OK ne s2 EARLIER)
    (WF: map_valid map s1)
    (RV: regs_valid jstk s1),
  tr_stmt s2.(st_code) map nret rret jstk s   ne ns.
Proof with eauto 3 with mapDB regDB stateDB.
  intros ? s; induction s; intros **;
  simpl in TR; try (monadInv TR); saturateTrans.
  - (* Sseq *)
    exploit IHs2... exploit IHs1... intros.
    econstructor; eauto 5 with mapDB regDB stateDB cocpitDB.
    eapply tr_stmt_earlier...
  - (* Sskip *)
    constructor.
  - (* Sassign *)
    econstructor...
    + eapply tr_expr_earlier with s3...
      eapply transl_expr_charact...
    + intros. pose proof (RV r H).
      intros [ ]. idtac...

    (* Sifthenelse *) - {
    destruct cf_strategy eqn:X;
    try (monadInv TR); saturateTrans.

  - (* Sifthenelse  Normal *)
    eapply tr_Sifthenelse; auto.
    + unfold PIsave...
    + eapply tr_expr_earlier with s9...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s8...
      eapply transl_expr_charact...
    + idtac...
    + eapply tr_stmt_earlier with s6...
      eapply IHs1... intros ? [-> |]; idtac...
    + eapply tr_stmt_earlier with s5...
      eapply IHs2... intros ? [-> |]; idtac...
    + unfold PIrecover...
    + idtac...
    + eauto 5 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + intros **. split; intros [];
      eauto 4 with mapDB regDB stateDB.
  - (* Sifthenelse  No_saves *)
    eapply tr_Sifthenelse_nosaves...
    + eapply tr_expr_earlier with s8...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s7...
      eapply transl_expr_charact...
    + eapply tr_stmt_earlier with s5;
      eauto 4 with mapDB regDB stateDB.
    + eapply tr_stmt_earlier with s4;
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + split; intros [];
      eauto 4 with mapDB regDB stateDB.
  - (* Sifthenelse  No_joins *)
    eapply tr_Sifthenelse_nojoins...
    + eapply tr_expr_earlier with s7...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s6...
      eapply transl_expr_charact...
    + eapply tr_stmt_earlier with s4;
      eauto 4 with mapDB regDB stateDB.
    + eapply tr_stmt_earlier with s...
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + split; intros [];
      eauto 4 with mapDB regDB stateDB. }

    (* Swhile *) - {
    destruct cf_strategy eqn:X;
    try (monadInv TR); saturateTrans.

  - (* Swhile  Normal *)
    eapply tr_Swhile; auto.
    + unfold PIsave...
    + eapply tr_expr_earlier with s8...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s7...
      eapply transl_expr_charact...
    + idtac...
    + eapply tr_stmt_earlier with s5...
      eapply IHs... intros ? [->|]; idtac...
    + unfold PIrecover...
    + unfold PIrecover...
    + idtac...
    + idtac;
      eauto 5 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + split; intros [];
      eauto 4 with mapDB regDB stateDB.
  - (* Swhile  No_saves *)
    eapply tr_Swhile_nosaves...
    + eapply tr_expr_earlier with s7...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s6...
      eapply transl_expr_charact...
    + eapply tr_stmt_earlier with s4...
      eapply IHs...
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + split; intros [];
      eauto 4 with mapDB regDB stateDB.
  - (* Swhile  No_joins *)
    eapply tr_Swhile_nojoins...
    + eapply tr_expr_earlier with s6...
      eapply transl_expr_charact...
    + eapply tr_expr_earlier with s5...
      eapply transl_expr_charact...
    + eapply tr_stmt_earlier with s3;
      eauto 4 with mapDB regDB stateDB.
    + intros [];
      eauto 4 with mapDB regDB stateDB.
    + split; intros [];
      eauto 4 with mapDB regDB stateDB. }
  - (* Scall *)
    exploit transl_exprlist_charact...
    intros A. econstructor.
    + apply tr_exprlist_earlier with s4...
    + idtac...
    + idtac...
    + intros ** [rF _];
      eauto 4 with mapDB regDB stateDB.
  - (* Sreturn *)
    econstructor...
    apply tr_expr_earlier with s0...
    eapply transl_expr_charact...
Qed.



(* Lemma transl_fun_charact: forall f tf s1 s2 EARLIER,
  transl_fun f s1 = OK tf s2 EARLIER ->
  tr_function f tf.
Proof with eauto with stateDB regDB mapDB.
  intros *. unfold transl_fun.
  caseEq(transl_fun_aux f init_state).
  -  congruence.
  - intros [nentry rparams] sfinal INCR TR E. inv E.
    monadInv TR. pose proof init_mapping_valid.
    econstructor...
    + intros. eapply match_init_env_init_reg...
    + eapply add_vars_inj...
      * eapply add_vars_inj...
        eapply init_mapping_inj.
      * eapply add_vars_valid...
    + eapply transl_stmt_charact...
      eapply add_vars_valid in EQ.
      * eapply add_vars_valid in EQ1.
        destruct EQ1... destruct EQ...
      * apply init_mapping_valid.
Qed. *)


Lemma transl_function_charact: forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof with eauto with stateDB regDB mapDB.
  intros *. unfold transl_function.
  caseEq(transl_fun_aux f init_state).
  - congruence.
  - intros [nentry rparams] sfinal INCR TR E. inv E.
    monadInv TR. pose proof init_mapping_valid.
    econstructor...
    + intros. eapply match_init_env_init_reg...
    + eapply add_vars_inj...
      * eapply add_vars_inj...
        eapply init_mapping_inj.
      * eapply add_vars_valid...
    + eapply transl_stmt_charact...
      eapply add_vars_valid in EQ.
      * eapply add_vars_valid in EQ1.
        destruct EQ1... destruct EQ...
      * apply init_mapping_valid.
Qed.


End RTLgenT_monad.


Lemma transl_program_charact: forall P C,
  transl_program P = Errors.OK C ->
  match_prog P C.
Proof.
  induction P as [|[Smain Sfm] Sfs], C as [|[Tmain Tfm] Tfs].
  - constructor.
  - inversion 1.
  - intros X. monadInv X.
  - intros X. monadInv X.
    constructor; auto.
    now apply transl_function_charact.
Qed.
End Functor.
