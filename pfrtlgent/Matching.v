From Utils   Require Export Smallstep Behaviours.
From PIPE    Require Export TagDomain.
From HLL     Require Export Language Semantics Policy.
From RTLT    Require Export Language Semantics Policy.
From RTLgenT Require Export Inj Env.
From RGTpf   Require Export Inj Env.
Import ListNotations.

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

Module Export ProofEnv := RGTpf.Env.Functor
                            STags Source
                            TTags Target
                            CompEnv
                            SRules SFlags
                            TRules
                            SSem
                            TSem.

(* Create HintDb matchDB. *)

Local Open Scope rtlgent_scope.

Definition match_atom   (a: Satom  ) (ta: Tatom  ) : Prop := $a = ta.
Definition match_TagErr (e: STagErr) (te: TTagErr) : Prop := $e = te.
Hint Unfold match_atom match_TagErr : cocpitDB.

Definition match_env (map:mapping) (E:env) (B:regbank) : Prop :=
  forall x atm,
  E!x = Some atm ->
  exists rx, map!x = Some rx /\ B # rx = $ atm.

Inductive tr_expr (c: code) (map: mapping) :
      (reg -> Prop) -> expr -> reg ->
      node -> node -> Prop :=

  | tr_Elit : forall (mdfy: reg -> Prop) l ne ns rd,
      c!ne = Some (Imovi ($ l) rd ns, ITconst) ->
      ~reg_in_map map rd -> mdfy rd ->
      tr_expr c map mdfy (Elit l) rd   ne ns

  | tr_Evar: forall (mdfy: reg -> Prop) id ne ns rd rs,
      map!id = Some rs ->
      c!ne = Some (Imov rs rd ns, ITvar) ->
      ~ reg_in_map map rd -> mdfy rd ->
      tr_expr c map mdfy (Evar id) rd   ne ns

  | tr_Eop : forall (mdfy mdf2 mdf1: reg -> Prop)
                    op a1 a2 rd ne n1 n2 ns r1 r2,
      tr_expr c map mdf1 a1 r1   ne n1 ->
      tr_expr c map mdf2 a2 r2   n1 n2 ->
      c!n2 = Some (Iop op r1 r2 rd ns, ITop op) ->
      ~reg_in_map map rd -> mdfy rd -> ~mdf2 r1 ->
      (forall r, mdf1 r \/ mdf2 r -> mdfy r) ->
      tr_expr c map mdfy (Eop op a1 a2) rd   ne ns.


Inductive tr_exprlist (c: code) (map: mapping) :
      (reg -> Prop) -> list expr -> list reg ->
      node -> node -> Prop :=
  | tr_Enil: forall (mdfy: reg -> Prop) n,
      (forall r, ~mdfy r) ->
      tr_exprlist c map mdfy [] []   n n
  | tr_Econs: forall (mdfy mdfy_h mdfy_t: reg -> Prop) a al ne ns r rl n1,
      tr_expr     c map mdfy_h a  r    ne n1 ->
      tr_exprlist c map mdfy_t al rl   n1 ns ->
      ~ mdfy_t r ->
      (forall r, mdfy_h r \/ mdfy_t r -> mdfy r) ->
      tr_exprlist c map mdfy (a :: al) (r :: rl)   ne ns.

Inductive tr_stmt (c: code) (map: mapping)
                  (nret: node) (rret: reg) : list reg -> stmt ->
                  node -> node -> Prop :=
  | tr_Sskip: forall jstk ns,
      tr_stmt c map nret rret jstk Sskip   ns ns
  | tr_Sseq: forall jstk s1 s2 ne n1 ns,
      tr_stmt c map nret rret jstk       s1       ne n1 ->
      tr_stmt c map nret rret jstk          s2    n1 ns ->
      tr_stmt c map nret rret jstk (Sseq s1 s2)   ne ns
  | tr_Sassign: forall jstk x a ne n1 ns rx rd mdfy,
      tr_expr c map mdfy a rd   ne n1 ->
      c!n1 = Some (Imov rd rx ns, ITassign) ->
      map!x = Some rx ->
      (forall r, In r jstk -> ~mdfy r) ->
      tr_stmt c map nret rret jstk (Sassign x a)   ne ns
  | tr_Sifthenelse: forall jstk cmp a1 a2 st sf ne n1
                           n2 ncond ntrue nfalse njoin
                           ns rj r1 r2 mdfy1 mdfy2,
      c!ne = Some (PIsave rj n1) ->
      tr_expr c map mdfy1 a1 r1   n1 n2 ->
      tr_expr c map mdfy2 a2 r2   n2 ncond ->
      c!ncond = Some (Icond cmp r1 r2 ntrue nfalse, ITifS) ->
      tr_stmt c map nret rret (rj::jstk) st   ntrue  njoin ->
      tr_stmt c map nret rret (rj::jstk) sf   nfalse njoin ->
      c!njoin = Some (PIrecover rj ns ITifJ) ->
      ~ reg_in_map map rj -> ~ In rj jstk ->
      ~ mdfy1 rj -> ~ mdfy2 rj -> ~mdfy2 r1 ->
      cf_strategy = Normal ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk
             (Sifthenelse cmp a1 a2 st sf) ne ns
  | tr_Sifthenelse_nosaves: forall jstk cmp a1 a2 st sf ne
                                   n1 ncond ntrue nfalse H
                                   njoin ns r1 r2 mdfy1 mdfy2,
      tr_expr c map mdfy1 a1 r1   ne n1 ->
      tr_expr c map mdfy2 a2 r2   n1 ncond ->
      c!ncond = Some (Icond cmp r1 r2 ntrue nfalse, ITifS) ->
      tr_stmt c map nret rret jstk st   ntrue  njoin ->
      tr_stmt c map nret rret jstk sf   nfalse njoin ->
      c!njoin = Some (Inop ns, ITifJ) ->
      ~mdfy2 r1 -> cf_strategy = No_saves H ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk
             (Sifthenelse cmp a1 a2 st sf) ne ns
  | tr_Sifthenelse_nojoins: forall jstk cmp a1 a2 st sf H
                                   ne n1 ncond ntrue nfalse
                                   ns r1 r2 mdfy1 mdfy2,
      tr_expr c map mdfy1 a1 r1   ne n1 ->
      tr_expr c map mdfy2 a2 r2   n1 ncond ->
      c!ncond = Some (Icond cmp r1 r2 ntrue nfalse, ITifS) ->
      tr_stmt c map nret rret jstk st   ntrue ns ->
      tr_stmt c map nret rret jstk sf   nfalse ns ->
      ~mdfy2 r1 -> cf_strategy = No_joins_nor_saves H ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk
             (Sifthenelse cmp a1 a2 st sf) ne ns
  | tr_Swhile: forall jstk cmp a1 a2 body ne n1
                      n2 ncond nbody nloop nexit
                      ns rj r1 r2 mdfy1 mdfy2,
      c!ne = Some (PIsave rj n1) ->
      tr_expr c map mdfy1 a1 r1   n1 n2 ->
      tr_expr c map mdfy2 a2 r2   n2 ncond ->
      c!ncond = Some (Icond cmp r1 r2 nbody nexit, ITwN) ->
      tr_stmt c map nret rret (rj::jstk) body   nbody nloop ->
      c!nloop = Some (PIrecover rj ne ITwL) ->
      c!nexit = Some (PIrecover rj ns ITwX) ->
      ~ reg_in_map map rj -> ~ In rj jstk ->
      ~ mdfy1 rj -> ~ mdfy2 rj -> ~mdfy2 r1 ->
      cf_strategy = Normal ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk (Swhile cmp a1 a2 body)   ne ns
  | tr_Swhile_nosaves: forall jstk cmp a1 a2 body ne
                              n1 n2 ncond nbody nloop H
                              nexit ns r1 r2 mdfy1 mdfy2,
      c!ne    = Some (Inop n1, ITnone) ->
      tr_expr c map mdfy1 a1 r1   n1 n2 ->
      tr_expr c map mdfy2 a2 r2   n2 ncond ->
      c!ncond = Some (Icond cmp r1 r2 nbody nexit, ITwN) ->
      tr_stmt c map nret rret jstk body   nbody nloop ->
      c!nloop = Some (Inop ne, ITwL) ->
      c!nexit = Some (Inop ns, ITwX) ->
      ~mdfy2 r1 -> cf_strategy = No_saves H ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk (Swhile cmp a1 a2 body)   ne ns
  | tr_Swhile_nojoins: forall jstk cmp a1 a2 body
                              ne n1 n2 ncond nbody H
                              ns r1 r2 mdfy1 mdfy2,
      c!ne = Some (Inop n1, ITnone) ->
      tr_expr c map mdfy1 a1 r1   n1 n2 ->
      tr_expr c map mdfy2 a2 r2   n2 ncond ->
      c!ncond = Some (Icond cmp r1 r2 nbody ns, ITwN) ->
      tr_stmt c map nret rret jstk body   nbody ne ->
      ~mdfy2 r1 -> cf_strategy = No_joins_nor_saves H ->
      (forall r, In r jstk -> ~mdfy1 r /\ ~ mdfy2 r) ->
      tr_stmt c map nret rret jstk (Swhile cmp a1 a2 body)   ne ns
  | tr_Scall: forall jstk x fid bs ne n1 ns rx rargs mdfy,
      tr_exprlist c map mdfy bs rargs   ne n1 ->
      c!n1 = Some (Icall fid rargs rx ns, ITcall) ->
      map!x = Some rx -> (forall r, In r jstk -> ~ mdfy r) ->
      tr_stmt c map nret rret jstk (Scall x fid bs)   ne ns
  | tr_Sreturn: forall a ne n1 ns rd mdfy jstk,
      tr_expr c map mdfy a rd   ne n1 ->
      c!n1 = Some (Imov rd rret nret, ITret) ->
      tr_stmt c map nret rret jstk (Sreturn a)   ne ns.


Inductive tr_cont (c: code) (map: mapping)
                  (ndef: node) (nret: node) (rret: reg)
        : list reg -> regbank ->
          SSem.local_cont -> node -> Prop :=
  | tr_Kseq : forall jstk B s lk ne n1,
      tr_stmt c map      nret rret jstk         s       ne n1 ->
      tr_cont c map ndef nret rret jstk B         lk    n1    ->
      tr_cont c map ndef nret rret jstk B (Kseq s lk)   ne

  | tr_Krule : forall rule p_s lk ne n1
                      rj jstk B itag dv,

      cf_strategy = Normal ->

      B # rj = (dv,inr p_s) ->
      ~ reg_in_map map rj -> ~ In rj jstk ->
      (forall p j s (* j&s are the join point and split point PCs *),
        ImovTR itag j (inr s) p = lift_p (rule j s) defVT) ->

      c!ne = Some (PIrecover rj n1 itag) ->
      tr_cont c map ndef nret rret jstk B lk    n1 ->
      tr_cont c map ndef nret rret (rj::jstk) B (Kjoin rule p_s lk)   ne

  | tr_Krule_nosaves : forall rule ps lk ne n1 jstk B itag H,

      cf_strategy = No_saves H ->

      (forall p, InopTR itag p = rule p ps) ->
      c!ne = Some (Inop n1, itag) ->
      tr_cont c map ndef nret rret jstk B                lk    n1 ->
      tr_cont c map ndef nret rret jstk B (Kjoin rule ps lk)   ne

  | tr_Krule_nojoins : forall rule ps lk ne jstk B H,
      cf_strategy = No_joins_nor_saves H ->
      (forall p p' x, rule p x = inl p' -> p = p') ->
      (forall p x e, rule p x <> inr e) ->
      tr_cont c map ndef nret rret jstk B                lk    ne ->
      tr_cont c map ndef nret rret jstk B (Kjoin rule ps lk)   ne


  | tr_Kemp : forall B,
      c!ndef   = Some(Imovi (O,defVT) rret nret, ITret) ->
      c!nret = Some(Ireturn rret, ITret) ->
      tr_cont c map ndef nret rret [] B Kemp   ndef.

Inductive tr_function: Source.function -> Target.function -> Prop :=
| tr_function_intro: forall f code nret rret nentry rparams nd map,
      (forall atms,
      match_env map 
          (set_locals (locals f) (set_params (Source.params f) atms))
          (init_regs ($ atms) rparams)) ->
      map_inj map ->
      code!nret = Some(Ireturn rret, ITret) ->
      code!nd = Some(Imovi defAtom rret nret, ITret) ->
      tr_stmt code map nret rret [] f.(Source.body)   nentry nd ->
      tr_function f (Target.mkfunction
                       f.(Source.arity)
                       rparams
                       code
                       nentry
                       f.(Source.fntag)
                    ).


Inductive match_prog : Source.program -> Target.program -> Prop :=
  | mprog_nil : match_prog [] []
  | mprog_cons: forall i it f tf p tp
        (EQ: i = it)
        (TF: tr_function f tf)
        (MP: match_prog p tp),
      match_prog ((i,f) :: p) ((it,tf) :: tp).


Inductive match_stacks: SSem.call_cont -> TSem.stack -> Prop :=
  | match_stacks_stop :
      match_stacks Kstop Stknil
  | match_stacks_call : forall x f E lk ck rx tf B ne (* ns *)
                               cs map ndef nret rret jstk
        (* local AST matching *)
        (MWF:map_inj map)
        (ME : match_env map E B)
        (Mx : map ! x = Some rx)
        (TK : tr_cont tf.(body) map ndef nret rret jstk B lk   ne (* ns *))
        (* call stack matching *)
        (MStk: match_stacks ck cs),
      match_stacks (KreturnTo   x  f E lk ck)
                   (Stackframe rx tf ne B cs)
  | match_stacks_ret : forall p ck tp cs
        (STp : p = tp)
        (MStk: match_stacks ck cs),
      match_stacks (KretTR p ck) (SretTR tp cs).


(* match_states parameterized be matching atoms (ma) and errors (me) *)
Inductive ms_paramed ma me : SSem.state -> TSem.state -> Prop :=
  | match_state : forall f s p lk ck E tf ne n1 (* ns *)
                         tp cs B map ndef nret rret dstk
        (MWF : map_inj map)
        (TS  : tr_stmt tf.(body) map nret rret dstk   s    ne n1)
        (TK  : tr_cont tf.(body) map ndef nret rret dstk B lk   n1 (* ns *))
        (STp : tp = p)
        (ME  : match_env map E B)
        (MStk: match_stacks ck cs),
      ms_paramed ma me (SSem.State  f s lk  p E ck)
                       (TSem.State tf  ne  tp B cs)
  | match_callstate : forall f args p ck tf targs tp cs
        (TF  : tr_function f tf)
        (SV  : targs = $ args)
        (STp : tp    = p)
        (MStk: match_stacks ck cs),
      ms_paramed ma me (SSem.Callstate  f  args  p ck)
                       (TSem.Callstate tf targs tp cs)
  | match_returnstate : forall a p ck ta tp cs
        (MA  : ma a ta)
        (STp : tp = p)
        (MStk: match_stacks ck cs),
      ms_paramed ma me (SSem.Returnstate  a  p ck)
                       (TSem.Returnstate ta tp cs)
  | match_errorstate : forall e te
      (MEr : me e te),
      ms_paramed ma me (SSem.Errorstate  e)
                       (TSem.Errorstate te).

Notation match_states := (ms_paramed match_atom match_TagErr).
(* Hint Unfold match_states : cocpitDB. *)









Lemma init_mapping_inj:
  map_inj init_mapping.
Proof.
  unfold init_mapping, map_inj. intros until r.
  rewrite PTree.gempty. inversion 1.
Qed.




Lemma match_env_empty:
  forall map,
  match_env map (PTree.empty Satom) (Regmap.init defAtom).
Proof. intros * x **. now rewrite PTree.gempty in H. Qed.

Lemma match_env_atoms_eq : forall v tv t tp map E B rx x
  (ME : match_env map E B)
  (MID: map ! x = Some rx)
  (EID: E   ! x = Some ( v,  t))
  (RBR: B   #rx =      (tv, tp)),
v = tv /\ exists tt, tp = inl tt /\ t = tt.
Proof with auto.
  intros. destruct (ME _ _ EID) as [rx' [A C]].
  simpl in C.
  rewrite MID in *. injection A as <-.
  rewrite RBR in C. injection C as <- ->.
  split... exists t...
Qed.

Lemma match_env_atoms : forall B rx atm map E x
  (ME : match_env map E B)
  (MID: map ! x = Some rx)
  (EID: E   ! x = Some atm),
B # rx = $ atm.
Proof with eauto.
  intros. destruct (ME _ _ EID) as [rx' [A C]].
  rewrite MID in A. injection A as ->...
Qed.

Lemma match_env_tags_eq: forall t tt map E B x rx tv
  (ME : match_env map E B)
  (MID: map ! x = Some rx)
  (Ex : E   ^ x = Some t)
  (RBR: B   #rx = (tv, inl tt)),
t = tt.
Proof with eauto.
  intros **. unfold gettag,
  SGetTag, SSem.getTag in Ex.
  destruct (E!x) eqn:Ex';[|inversion Ex].
  destruct a as [v t']. injection Ex as ->.
  exploit match_env_atoms_eq...
  intros [_ [tt' [A ->]]]. inv A...
Qed.

Lemma match_env_tags: forall B rx t map E x
  (ME: match_env map E B)
  (Mx: map ! x = Some rx)
  (Ex: E   ^ x = Some t),
B ^ rx = inl t.
Proof.
  intros. unfold gettag, SGetTag, TGetTag,
                 SSem.getTag, TSem.getTag in *.
  destruct (E ! x) as [[v t']|] eqn:eid; [|inversion Ex].
  injection Ex as ->. destruct (ME _ _ eid) as [rx' [A C]].
  rewrite Mx in A. injection A as <-. now rewrite C.
Qed.

Lemma match_env_find_var:
  forall map E B x atm rx
  (ME: match_env map E B)
  (Ex: E  !x = Some atm)
  (Mx: map!x = Some rx),
  B # rx = $ atm.
Proof.
  intros **. destruct (ME _ _ Ex) as [rx' [A C]].
  rewrite Mx in A. now injection A as <-.
Qed.

(** Matching between #<b><tt>#target#</tt></b># register banks and
    #<b><tt>#source#</tt></b># environments is preserved by any extension of that
    register bank. *)

Lemma match_env_invariant:
  forall map E B B'
  (ME: match_env map E B)
  (RR: (forall r, (reg_in_map map r) -> B'#r = B#r)),
  match_env map E B'.
Proof with auto.
  intros ** x atm Ex.
  destruct (ME _ _ Ex) as [rx [Mx A]].
  exists rx. split...
  rewrite RR... exists x...
Qed.

(** Matching between environments is preserved when an unmapped register
   (not corresponding to any #<b><tt>#source#</tt></b># variable) is
   assigned in the #<b><tt>#target#</tt></b># register bank. *)

Lemma match_env_update_temp:
  forall map E B r a
  (ME: match_env map E B)
  (A: ~ (reg_in_map map r)),
  match_env map E (B#r <- a).
Proof with auto.
  intros **. apply match_env_invariant with B...
  intros. destruct (peq r r0) as [<-|];
  [ contradiction
  | apply Regmap.gso]...
Qed.
Hint Resolve match_env_update_temp: cocpitDB.



Lemma match_env_update_var:
  forall map E B x rx a ta
  (MIJ: map_inj map)
  (Mx : map!x = Some rx)
  (ME : match_env map E B)
  (A: $ a = ta),
  match_env map (E!x <- a) (B#rx <- ta).
Proof with eauto.
  intros ** y atm. rewrite PTree.gsspec.
  destruct (peq y x) as [<-| ]; [injection 1 as <- | intros].
  - exists rx; split; [|rewrite PMap.gss]...
  - destruct (ME _ _ H) as [ry [My Bry]].
    exists ry; split... rewrite PMap.gso...
    intros ->...
Qed.



Lemma local_cont_end:
  forall {ndef rret nret c map dstk B lk ne},
  tr_cont c map ndef nret rret dstk B lk   ne ->
     c!ndef = Some (Imovi defAtom rret nret, ITret)
  /\ c!nret = Some (Ireturn rret, ITret).
Proof. induction 1; auto. Qed.
(* Proof.
  induction 1; trivial.
  - (* tr_Kemp case *)
    exact (conj H H0).
Qed. *)

Lemma tr_cont_dstk_map_disjoint :
  forall dstk b map ndef nret rret B lk n1,
  tr_cont b map ndef nret rret dstk B lk   n1 ->
  forall r, In r dstk -> ~ reg_in_map map r.
Proof. induction 1; auto. intros * [<-|]; auto. Qed.

Lemma tr_cont_rb : forall c map lk n1  ndef nret rret jstk B,
    tr_cont c map ndef nret rret jstk B lk   n1 ->
    forall B', (forall r, In r jstk -> B # r = B' # r) ->
    tr_cont c map ndef nret rret jstk B' lk   n1.
Proof with eauto.
  induction 1; intros; [| idtac | | |];
  try solve [econstructor;eauto].
    econstructor 2...
    - rewrite <- H6... left...
    - apply IHtr_cont. intros.
      apply H6. right...
Qed.
Hint Resolve tr_cont_rb : cocpitDB.



Lemma tr_cont_dstk_no_map : forall b map ndef nret rret jstk rb lk n1 (* ns *),
  tr_cont b map ndef nret rret jstk rb lk   n1 (* ns *) ->
  forall r, In r jstk -> ~ reg_in_map map r.
Proof. induction 1; auto. intros * [<-|]; auto. Qed.



Lemma functions_tred:
  forall {f tp id p}
    (MP  : match_prog p tp)
    (GEID: (SSem.mkge p) ! id = Some f),
  exists tf,
    tr_function f tf /\
    (TSem.mkge tp) ! id = Some tf.
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


Lemma tr_function_preserves : forall {f tf},
  tr_function f tf ->
  tf.(fntag) = f.(Source.fntag) /\
  tf.(arity) = f.(Source.arity).
Proof. inversion 1; simpl; auto. Qed.

Lemma tr_function_fntag:
  forall {f tf},
  tr_function f tf ->
  tf.(fntag) = f.(Source.fntag).
Proof. inversion 1; simpl; auto. Qed.

Lemma tr_function_sig:
  forall {f tf},
  tr_function f tf ->
  tf.(arity) = f.(Source.arity).
Proof. inversion 1; simpl; auto. Qed.

End Functor.