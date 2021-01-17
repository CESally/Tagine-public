From Utils   Require Import Defns.
From PIPE    Require Import TagDomain.
From HLL     Require Import Language Semantics Policy.
From RTLT    Require Import Language Semantics Policy.
From RTLgenT Require Import Inj Env.
From RGTpf   Require Import Inj.
Import ListNotations.

Module Functor (Export STags  : TagDomain.FrontEnd)
               (Import Source : HLL.Language.Sig STags)
               (Import TTags  : TagDomain_MiddleTgn STags)
               (Import Target : RTLT.Language.Sig TTags)
               (Export CompEnv: CEnvSig STags Source TTags Target)
               (Export SRules : HLL.Policy.Sig STags)
               (Export SFlags : HLL.Policy.Props STags SRules)
               (Export TRules : RTLT_Policy_Tgn STags TTags SRules SFlags)
               (Export SSem   : HLL.Semantics.Sig STags SRules Source)
               (Export TSem   : RTLT.Semantics.Sig TTags TRules Target).

  Notation "'Satom'" := SSem.atom : rtlgent_scope.
  Notation "'Tatom'" := TSem.atom : rtlgent_scope.

Local Open Scope rtlgent_scope.

  Instance injectAtom : Inj Satom Tatom := {
    inject := fun xy =>
                match xy with
                | (x,y) => (x, inl y)
                end
  }.

  Instance injectListOfAtoms : Inj (list Satom) (list Tatom) := {
    inject := map $
  }.


  Theorem toAtoms : forall {l v tv t vp},
  SSem.toAtom    l  = ( v,  t) ->
  TSem.toAtom ($ l) = (tv, vp) ->
    v = tv /\ exists tt, vp = inl tt /\ t = tt.
  Proof with auto.
    simpl. unfold SSem.toAtom, TSem.toAtom, id.
    intros [v' t'] v tv t [tt | p].
    - do 2 (injection 1 as -> ->).
      split... exists tt...
    - inversion 2.
  Qed.

  Theorem inj_lst_atms_alt : forall (atms : list SSem.atom),
    $ atms = combine
              (fst (split atms))
     (map inl (snd (split atms))).
  Proof with auto.
    induction atms; simpl in *...
    destruct a, (split atms) as [vals tags] eqn:SAt_eq.
    simpl in *. f_equal...
  Qed.



  Theorem getTags_atms : forall rb rargs vals tags atms,
    split atms = (vals, tags) ->
    rb ## rargs = $ atms ->
    TSem.getTags rb rargs = $ tags.
  Proof with eauto.
    induction rargs as [| r rargs IH];
    intros * A B.
    - symmetry in B. simpl in *.
      apply map_eq_nil in B.
      rewrite B in A. inv A...
    - destruct atms as [|a atms]; [inv B|].
      destruct vals as [|v vals].
      { inv A. destruct a as [v t],
               (split atms) as [vals' tags'].
        inv H0. }
      destruct tags as [|t tags].
      { inv A. destruct a   as [v' t'],
               (split atms) as [vals' tags'].
        inv H0. }
      pose proof A. simpl in A.
      destruct (split atms) as [vals' tags'] eqn:X,
               a            as [v' t'].
      simpl in *. inv A. inv B.
      rewrite H1, (IH _ _ _ X H2)...
  Qed.

  Class GetTag A B C: Type := {
    gettag : A -> B -> C
  }.

  Instance SGetTag : GetTag env ident (option SValTag) := {
    gettag := SSem.getTag
  }.

  Instance TGetTag : GetTag regbank reg TValTag := {
    gettag := TSem.getTag
  }.

  Hint Unfold SGetTag TGetTag getWVTags : cocpitDB.

  Notation "a ^ b" := (gettag a b).

  Definition map_inj (m: mapping) : Prop := forall x y r,
    m!x = Some r ->
    m!y = Some r -> x = y.

  Definition reg_in_map (m: mapping) (r: reg) : Prop :=
    (exists x, m!x = Some r).

  Local Close Scope rtlgent_scope.

End Functor.