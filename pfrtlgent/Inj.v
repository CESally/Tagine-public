From Utils    Require Import Defns.
From PIPE     Require Import TagDomain.
From HLL      Require Import Language Semantics Policy.
From RTLT     Require Import Language Semantics Policy.
From RTLgenT  Require Import Inj.
Import ListNotations.

Module PolicyInjection
    (Export FTags  : TagDomain.FrontEnd)
    (Export MTagT  : TagDomain_MiddleTgn FTags)
    (Export HRules : HLL.Policy.Sig FTags)
    (Export HFlags : HLL.Policy.Props FTags HRules).

  Local Notation "'WM'"      := FTags.M (at level 50).
  Local Notation "'RM'"      := MTagT.M (at level 50).
  Local Notation "'WValTag'" := FTags.ValTag         .
  Local Notation "'RValTag'" := MTagT.ValTag         .
  Local Notation "'WPCTag'"  := FTags.PCTag          .
  Local Notation "'RPCTag'"  := MTagT.PCTag          .
  Local Notation "'WTagErr'" := FTags.TagErr         .
  Local Notation "'RTagErr'" := MTagT.TagErr         .

    Definition VT_unlift (v: RValTag) : WValTag :=
      match v with
      | inl v => v
      | inr _ => FTags.defVT
      end.
    Definition V2P_unlift (v: RValTag) : WPCTag :=
      match v with
      | inl _ => initPCT
      | inr p => p
      end.
    Local Coercion VT_unlift  : MTagT.ValTag >-> FTags.ValTag.
    Local Coercion V2P_unlift : MTagT.ValTag >-> FTags.PCTag.


    Definition lift_pv (res: WM (WPCTag * WValTag)) : M (RPCTag * RValTag) :=
      match res with
      | inl (p, t) => ret (p, inl t)
      | inr serr   => fstop serr
      end.

    Definition lift_v (p: RPCTag) (res: WM WValTag) : M (RPCTag * RValTag) :=
      match res with
      | inl t   => ret (p, inl t)
      | inr serr => fstop serr
      end.

    Definition lift_p (res: WM WPCTag) (t: RValTag) : M (RPCTag * RValTag) :=
      match res with
      | inl p    => ret (p, t)
      | inr serr => fstop serr
      end.

    Definition InopTR (tag: ITag) (p: RPCTag) : M PCTag :=
      match tag return M PCTag with
      | ITnone => ret p
      | ITifJ  => ifJTR p initPCT
      | ITwL   =>  wLTR p initPCT
      | ITwX   =>  wXTR p initPCT
      | _      => fstop defER
      end.

    Definition real_nopTR : forall p, InopTR defIT p = ret p.
    Proof ltac: (unfold defIT, InopTR; auto).

    Definition ImovTR (tag: ITag) (p: RPCTag) (ts td: RValTag)
    : M (RPCTag * RValTag) :=
      match tag with
(*       | ITvar    => lift_v (sguard spci_varTR p) (varTR p ts) *)
      | ITvar    => lift_v p (varTR p ts)
      | ITifJ    => lift_p (ifJTR p ts)  defVT
      | ITwL     => lift_p ( wLTR p ts)  defVT
      | ITwX     => lift_p ( wXTR p ts)  defVT
      | ITret    => ret    (p, ts)
      | ITsavePC => ret    (p, inr p)

  (*  [assignTR] by default takes the "dest" tag, that of the variable being
      assigned to.  In movTR, this would be the tag on the destination register.
      The input flag [ass_dnd] (Assign Doesn't Need Destination) tells us if
      [assignTR] doesn't need the "dest" tag.  That is, [ass_dnd = true]
      indicates that [assignTR] is independent in its 2nd argument, which is the
      variable's (being assigned to) tag.

      In the ImovTR rule, if assignTR doesn't need the dest tag, then we
      automatically pass in the Whilef default value tag. If assignTR _does_ need
      the dest tag, then if the dest register contains a value tag, we pass that
      to [assignTR], and if it contains a PC tag, we return a "default", non-faultstop
      result for the rule. *)
      | ITassign => if dnd_assignTR
                    then lift_pv (assignTR p defVT ts)
                    else lift_pv (assignTR p td    ts)
      | _        => fstop defER
      end.

    Theorem non_ass_movtr_indep: forall it p ts td1 td2,
      it <> ITassign ->
      ImovTR it p ts td1 = ImovTR it p ts td2.
    Proof.
      destruct it; solve [reflexivity|contradiction].
    Qed.

    Definition ImoviTR (tag: ITag) (p: RPCTag) (immt: RValTag)
    : M (RPCTag * RValTag) :=
      match tag with
(*       | ITconst            => lift_v (sguard spci_constTR p) (constTR p immt)
      | ITparam Oadd t1 t2 => lift_v (sguard spci_addTR   p) (addTR p t1 t2)
      | ITparam Osub t1 t2 => lift_v (sguard spci_subTR   p) (subTR p t1 t2) *)
      | ITconst            => lift_v p (constTR p immt)
      | ITparam Oadd t1 t2 => lift_v p (addTR p t1 t2)
      | ITparam Osub t1 t2 => lift_v p (subTR p t1 t2)
      | ITret              => ret (p, immt)
      | _ => fstop defER
      end.

    Definition IopTR (tag: ITag) (p: PCTag) (op: operation) (t1 t2: RValTag)
    : M (RPCTag * RValTag) :=
      match tag, op with
(*       | ITplus , Oadd => lift_v (sguard spci_addTR p) (addTR p t1 t2)
      | ITmonus, Osub => lift_v (sguard spci_subTR p) (subTR p t1 t2) *)
      | ITplus , Oadd => lift_v p (addTR p t1 t2)
      | ITmonus, Osub => lift_v p (subTR p t1 t2)
      | _      , _    => fstop defER
      end.

    Definition IcondTR (tag: ITag) (p: PCTag) (c: comparison) (tl tr: RValTag)
    : M RPCTag :=
      match tag with
      | ITifS => ifSTR p c tl tr
      | ITwN  =>  wNTR p c tl tr
      | _     => fstop defER 
      end.

    Fixpoint getWVTags (lst:list RValTag) : list WValTag :=
      match lst return list WValTag with 
      | t :: ts => (VT_unlift t) :: getWVTags ts
      | []      => []
      end.

    Lemma getWVTags_obv: forall (tags: list WValTag),
      getWVTags (map inl tags) = tags.
    Proof with auto. induction tags;simpl;[|f_equal]... Qed.

    Definition IcallTR (tag: ITag) (p cee: PCTag) (args: list RValTag)
    : M RPCTag :=
      match tag with
      | ITcall => callTR p cee (getWVTags args)
      | _      => fstop defER 
      end.

    Definition IreturnTR (tag: ITag) (p en: RPCTag) (rett: RValTag)
    : M RPCTag :=
      match tag with
      | ITret => retTR p en rett
      | _     => fstop defER 
      end.

End PolicyInjection.

Module Type RTLT_Policy_Tgn
    (Export FTags  : TagDomain.FrontEnd)
    (Export MTagT  : TagDomain_MiddleTgn FTags)
    (Export HRules : HLL.Policy.Sig FTags)
    (Export HFlags : HLL.Policy.Props FTags HRules)
      <: RTLT.Policy.Sig MTagT.
  Include PolicyInjection FTags MTagT HRules HFlags.
End RTLT_Policy_Tgn.












Module PolicyPropsInjection
    (Export FTags    : TagDomain.FrontEnd)
    (Export HRules   : HLL.Policy.Sig FTags)
    (Export HFlags   : HLL.Policy.Props FTags HRules)
    (Export MTagT    : TagDomain_MiddleTgn FTags)
    (Export RRuleT   : RTLT_Policy_Tgn FTags MTagT HRules HFlags)
    (Export RTLT_Tgn : RTLT.Language.Sig MTagT).

    Local Coercion VT_unlift  : MTagT.ValTag >-> FTags.ValTag.
    Local Coercion V2P_unlift : MTagT.ValTag >-> FTags.PCTag.

    Ltac unfolder_aux := try unfold lift_pv;
                         try unfold lift_p;
                         try unfold lift_v;
                         try unfold FTags.fstop in *.

    Ltac depend_on wfflag :=
      let A := fresh "A"  in
      let B := fresh "B"  in
      let C := fresh "C"  in
      let X := fresh "Hb" in
      destruct wfflag as [A|] eqn:X;
      match goal with  (* guaranteed to be matching on A *)
                       (* by semantics of [match goal]   *)
                       (* (matches on latest hyp first   *)
      | H: _ /\ _ /\ _ |- _ => destruct A as [A [B C]]
      | H: _ /\ _      |- _ => destruct A as [A B]
      | H: _ |- _ => idtac
      end;
      simpl;  unfolder_aux;
      [|exact DKnow];
      try (red in A);
      try rewrite X; clear X;
      refine (Know _);
      match goal with
      | H: _ |- _ /\ _ /\ _ => split;[|split]
      | H: _ |- _ /\ _      => split
      | H: _ |- _ => idtac
      end;
      repeat intro.

    Notation    InopTR_is_lpcp it    := (forall p p'         , InopTR    it p          = ret  p'     -> p = p').
    Notation    ImovTR_is_lpcp it    := (forall p p' v1 v2 v', ImovTR    it p v1 v2    = ret (p',v') -> p = p').
    Notation   ImoviTR_is_lpcp it    := (forall p p' v v'    , ImoviTR   it p v        = ret (p',v') -> p = p').
    Notation     IopTR_is_lpcp it op := (forall p p' v1 v2 v', IopTR     it p op v1 v2 = ret (p',v') -> p = p').
    Notation   IcondTR_is_lpcp it    := (forall p p' c v1 v2 , IcondTR   it p c v1 v2  = ret  p'     -> p = p').
    Notation   IcallTR_is_lpcp it    := (forall p p' fnt args, IcallTR   it p fnt args = ret  p'     -> p = p').
    Notation IreturnTR_is_lpcp it    := (forall p p' p_en v  , IreturnTR it p p_en v   = ret  p'     -> p = p').

    Definition dnd_ImovTR (it: ITag) : MProp (forall p v d1 d2,
      ImovTR it p v d1 = ImovTR it p v d2).
    Proof with auto.
      refine (match it with
        | ITassign => _
        | _ => DKnow end).
      depend_on dnd_assignTR...
    Defined.

    Lemma not_ass_mov_dnd : forall {it},
      it <> ITassign -> dnd_ImovTR it = DKnow.
    Proof with auto.
      destruct it... destruct 1...
    Qed.

    Definition lpcp : forall (ti: tinst), MProp (match ti with
      | (Inop    _        , it) =>    InopTR_is_lpcp it
      | (Imov    _ _ _    , it) =>    ImovTR_is_lpcp it
      | (Imovi   _ _ _    , it) =>   ImoviTR_is_lpcp it
      | (Iop op  _ _ _ _  , it) =>     IopTR_is_lpcp it op
      | (Icond   _ _ _ _ _, it) =>   IcondTR_is_lpcp it
      | (Icall   _ _ _ _  , it) =>   IcallTR_is_lpcp it
      | (Ireturn _        , it) => IreturnTR_is_lpcp it
      end).
    Proof with eauto.
      destruct one_pct_val. {
        intros [[] it]; refine (Know _); intros; apply e.
      }

      intros [[] it]. 

      - (* Inop *)
        refine (match it with
        | ITnone => ltac:(refine (Know _); inversion 1)
        | ITifJ  => ltac:(depend_on lpcp_ifJTR        )
        | ITwL   => ltac:(depend_on lpcp_wLTR         )
        | ITwX   => ltac:(depend_on lpcp_wXTR         )
        | _ => ltac:(refine (Know _); simpl; inversion 1) end)...

    - (* Imov *)
        refine (match it with 
          | ITvar    => _
          | ITassign => _
          | ITifJ    => _
          | ITwL     => _
          | ITwX     => _
          | ITret    => _
          | ITsavePC => _
          | _ => ltac:(refine (Know _); simpl; inversion 3) end).
      + (* ITvar *)
        left. simpl. intros.
        destruct (varTR p v1); inv H...
      + (* ITassign *)
        depend_on lpcp_assignTR.
        destruct dnd_assignTR;
        match goal with
        | A: match (assignTR ?p ?v1 ?v2) with _ => _ end = _ 
           |- _ => destruct (assignTR p v1 v2) as [[]|] eqn:?
        end;
        solve [inv H; eapply A; eauto].
      + (* ITifJ *)
        depend_on lpcp_ifJTR.
        destruct (ifJTR p v1) eqn:?; inv H...
      + (* ITwL *)
        depend_on lpcp_wLTR.
        destruct (wLTR p v1) eqn:?; inv H...
      + (* ITwX *)
        depend_on lpcp_wXTR.
        destruct (wXTR p v1) eqn:?; inv H...
      + (* ITret *)
        depend_on lpcp_retTR. inv H...
      + (* ITsavePC *)
        left. simpl. inversion 3...

    - (* Imovi *)
        refine (match it with 
          | ITconst       => _
          | ITret         => _
          | ITparam o _ _ => ltac:(destruct o)
          | _ => DKnow end).
      + (* ITconst *)
        left. simpl. intros.
        destruct (constTR p v); inv H...
      + (* ITret *)
        left. simpl. inversion 1...
      + (* ITparam Osub *)
        left. simpl. intros.
        destruct (subTR p v v0); inv H...
      + (* ITparam Oadd *)
        left. simpl. intros.
        destruct (addTR p v v0); inv H...

    - (* Iop *)
      refine (match it with
        | ITplus  => match o with Oadd => _ | _ => DKnow end
        | ITmonus => match o with Osub => _ | _ => DKnow end
        | _ => DKnow end).
      + (* ITplus *)
        left. simpl. intros.
        destruct (addTR p v1 v2); inv H...
      + (* ITmonus *)
        left. simpl. intros.
        destruct (subTR p v1 v2); inv H...

    - (* Icond *)
      refine (match it with
        | ITifS => ltac:(depend_on lpcp_ifSTR)
        | ITwN  => ltac:(depend_on lpcp_wNTR )
        | _ => DKnow end)...

    - (* Icall *)
      refine (match it with
        | ITcall => ltac:(depend_on lpcp_callTR)
        | _ => DKnow end)...

    - (* Ireturn *)
      refine (match it with
        | ITret => ltac:(depend_on lpcp_retTR)
        | _ => DKnow end)...
    Qed.

    Definition dfs : forall (ti: tinst), MProp (match ti with
      | (Inop    _        , it) => forall p          e, InopTR    it p          <> fstop e
      | (Imov    _ _ _    , it) => forall p v1 v2    e, ImovTR    it p v1 v2    <> fstop e
      | (Imovi   _ _ _    , it) => forall p v        e, ImoviTR   it p v        <> fstop e
      | (Iop op  _ _ _ _  , it) => forall p   v1 v2  e, IopTR     it p op v1 v2 <> fstop e
      | (Icond   _ _ _ _ _, it) => forall p c v1 v2  e, IcondTR   it p  c v1 v2 <> fstop e
      | (Icall   _ _ _ _  , it) => forall p fnt args e, IcallTR   it p fnt args <> fstop e
      | (Ireturn _        , it) => forall p p_en v   e, IreturnTR it p p_en v   <> fstop e
      end).
    Proof with eauto.
      intros [[] it].

      - (* Inop *)
        refine (match it with
          | ITifJ => ltac:(depend_on dfs_ifJTR)
          | ITwL  => ltac:(depend_on dfs_wLTR )
          | ITwX  => ltac:(depend_on dfs_wXTR )
          | _ => DKnow end)...

      - (* Imov *)
        refine (match it with
          | ITvar    => _
          | ITassign => _
          | ITifJ    => _
          | ITwL     => _
          | ITwX     => _
          | ITret    => _
          | _ => DKnow end).
          + (* ITvar *)
            depend_on dfs_varTR.
            destruct (varTR p v1) eqn:?;
            inv H...
          + (* ITassign *)
            depend_on dfs_assignTR;
            destruct dnd_assignTR;
            match goal with
            | G: match (assignTR ?p ?ts ?td) with _ => _ end = _
               |- _ => destruct (assignTR p ts td) as [[]|] eqn:?;
                       [ inv G
                       | eapply A; eauto]
            end.
          + (* ITifJ *)
            depend_on dfs_ifJTR.
            destruct (ifJTR p v1) eqn:?;
            [ inv H
            | eapply A ]...
          + (* ITwL *)
            depend_on dfs_wLTR.
            destruct (wLTR p v1) eqn:?;
            [ inv H
            | eapply A ]...
          + (* ITwX *)
            depend_on dfs_wXTR.
            destruct (wXTR p v1) eqn:?;
            [ inv H
            | eapply A ]...
          + (* ITret *)
            left. simpl. inversion 2.

      - (* Imovi *)
        refine (match it with
          | ITconst       => _
          | ITparam o _ _ => ltac:(destruct o)
          | _ => DKnow end).
        + (* ITconst *)
          depend_on dfs_constTR.
          destruct (constTR p v) eqn:?;
          [ inv H
          | eapply A]...
        + (* ITparam Osub *)
          depend_on dfs_subTR.
          destruct (subTR p v v0) eqn:?;
          [ inv H
          | eapply A ]...
        + (* ITparam Oadd *)
          depend_on dfs_addTR.
          destruct (addTR p v v0) eqn:?;
          [ inv H
          | eapply A ]...

      - (* Iop *)
        refine (match it with
          | ITplus  => match o with Oadd => _ | _ => DKnow end
          | ITmonus => match o with Osub => _ | _ => DKnow end
          | _ => DKnow end).
        + (* ITplus *)
          depend_on dfs_addTR.
          destruct (addTR p v1 v2) eqn:?;
          [ inv H
          | eapply A ]...
        + (* ITmonus *)
          depend_on dfs_subTR.
          destruct (subTR p v1 v2) eqn:?;
          [ inv H
          | eapply A ]...

      - (* Icond *)
        refine (match it with
          | ITifS => ltac:(depend_on dfs_ifSTR)
          | ITwN  => ltac:(depend_on dfs_wNTR)
          | _ => DKnow end)...

      - (* Icall *)
        refine (match it with
          | ITcall => ltac:(depend_on dfs_callTR)
          | _ => DKnow end)...

      - (* Iret *)
        refine (match it with
          | ITret => ltac:(depend_on dfs_retTR)
          | _ => DKnow end)...
    Defined.


    (* solve tag mismatch with *)
    Ltac solve_tmmw H :=
      solve [ split; inversion 1
            | match goal with X: _ = inr ?t, Y: _ = inl ?p
              |- _ => erewrite H, Y in X; inv X end
            | match goal with X: _ = inr ?t, Y: _ = inr ?t'
              |- _ => rewrite H, X in Y; inv Y; split; auto end ].


    Definition wpci : forall (ti: tinst), MProp (match ti with
      | (Inop    _        , it) => InopTR_is_lpcp it
                                /\ forall p1 p2 e,
                                      InopTR it p1 = fstop e <->
                                      InopTR it p2 = fstop e
      | (Icond   _ _ _ _ _, it) => IcondTR_is_lpcp it
                                /\ forall p1 p2 c v1 v2 e,
                                      IcondTR it p1 c v1 v2 = fstop e <->
                                      IcondTR it p2 c v1 v2 = fstop e
      | (Icall   _ _ _ _  , it) => IcallTR_is_lpcp it
                                /\ forall p1 p2 fnt args e,
                                      IcallTR it p1 fnt args = fstop e <->
                                      IcallTR it p2 fnt args = fstop e
      | (Ireturn _        , it) => IreturnTR_is_lpcp it
                                /\ forall p1 p2 p_en v e,
                                      IreturnTR it p1 p_en v = fstop e <->
                                      IreturnTR it p2 p_en v = fstop e
      | (Imov    _ _ _    , it) => ImovTR_is_lpcp it
                                /\ (forall p1 p2 vs vd p1' p2' v1' v2',
                                      ImovTR it p1 vs vd = ret (p1',v1') ->
                                      ImovTR it p2 vs vd = ret (p2',v2') ->
                                      v1' = v2')
                                /\  forall p1 p2 vs vd e,
                                      ImovTR it p1 vs vd = fstop e <->
                                      ImovTR it p2 vs vd = fstop e
      | (Imovi   _ _ _    , it) => ImoviTR_is_lpcp it
                                /\ (forall p1 p2 v p1' p2' v1' v2',
                                      ImoviTR it p1 v = ret (p1',v1') ->
                                      ImoviTR it p2 v = ret (p2',v2') ->
                                      v1' = v2')
                               /\   forall p1 p2 v e,
                                      ImoviTR it p1 v = fstop e <->
                                      ImoviTR it p2 v = fstop e
      | (Iop op  _ _ _ _  , it) => IopTR_is_lpcp it op
                                /\ (forall p1 p2 v1 v2 p1' p2' v1' v2',
                                      IopTR it p1 op v1 v2 = ret (p1',v1') ->
                                      IopTR it p2 op v1 v2 = ret (p2',v2') ->
                                      v1' = v2')
                                /\  forall p1 p2 v1 v2 e,
                                      IopTR it p1 op v1 v2 = fstop e <->
                                      IopTR it p2 op v1 v2 = fstop e
      end).
    Proof with eauto.
      intros [[] it].

      - (* InopTR *)
        refine (match it with
          | ITifJ => ltac:(depend_on wpci_ifJTR)
          | ITwL  => ltac:(depend_on wpci_wLTR)
          | ITwX  => ltac:(depend_on wpci_wXTR)
          | _ => ltac:(refine (Know _);
                       split;[|split];
                       inversion 1; auto) end)...

      - (* ImovTR *)
        refine (match it with
          | ITvar    => _
          | ITassign => _
          | ITifJ    => _
          | ITwL     => _
          | ITwX     => _
          | ITret    => _
          | ITsavePC => DKnow
          | _ => ltac:(refine (Know _); simpl;
                       split;[|split];intros;
                       [ solve [inv H; auto]
                       | solve [inv H; inv H0; auto]
                       | solve [split; inversion 1; auto]])
          end).
        + (* ITvar *)
          depend_on wpci_varTR.
          * (* lpcp component *)
            destruct (varTR p v1); inv H...
          * (* same non PC outputs component *)
            destruct (varTR p1 vs) eqn:X, (varTR p2 vs) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H0 | inv H ].
          * (* same fs behaviour component *)
            destruct (varTR p1 vs) eqn:X, (varTR p2 vs) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].
        + (* ITassign *)
          depend_on wpci_assignTR.
          * (* lpcp component *)
            destruct dnd_assignTR;
            match goal with
            | A: match assignTR ?p ?vs ?vd with _ => _ end = _
               |- _ => destruct (assignTR p vs vd) as [[]|] eqn:X
            end;
            solve [inv H; eapply A; eauto ].
          * (* same non PC outputs component *)
            destruct dnd_assignTR;
            match goal with
            | A: match assignTR ?p1 ?vs1 ?vd1 with _ => _ end = _,
              B: match assignTR ?p2 ?vs2 ?vd2 with _ => _ end = _
               |- _ => destruct (assignTR p1 vs1 vd1) as [[]|] eqn:X,
                                (assignTR p2 vs2 vd2) as [[]|] eqn:Y 
            end;
            solve [ inv H0
                  | inv H
                  | inv H; inv H0; f_equal; eapply B; eauto ].
          * (* same fs behaviour component *)
            destruct dnd_assignTR;
            match goal with
            |- match assignTR ?p1 ?vs1 ?vd1 with _ => _ end = _ <->
               match assignTR ?p2 ?vs2 ?vd2 with _ => _ end = _
            => destruct (assignTR p1 vs1 vd1) as [[]|] eqn:X,
                        (assignTR p2 vs2 vd2) as [[]|] eqn:Y 
            end;
            solve_tmmw C.
        + (* ITifJ *)
          depend_on wpci_ifJTR.
          * (* lpcp component *)
            destruct (ifJTR p v1) eqn:X;
            [ inv H; eapply A; eauto
            | inv H ].
          * (* same non PC outputs component *)
            destruct (ifJTR p1 vs), (ifJTR p2 vs);
            solve [ inv H0
                  | inv H
                  | inv H; inv H0; auto ].
          * (* same fs behaviour component *)
            destruct (ifJTR p1 vs) eqn:?,
                     (ifJTR p2 vs) eqn:?;
            solve_tmmw B.
        + (* ITwL *)
          depend_on wpci_wLTR.
          * (* lpcp component *)
            destruct (wLTR p v1) eqn:?;
            [ inv H; eapply A; eauto
            | inv H ].
          * (* same non PC outputs component *)
            destruct (wLTR p1 vs),
                     (wLTR p2 vs);
            solve [ inv H0
                  | inv H
                  | inv H; inv H0; auto ].
          * (* same fs behaviour component *)
            destruct (wLTR p1 vs) eqn:?,
                     (wLTR p2 vs) eqn:?;
            solve_tmmw B.
        + (* ITwX *)
          depend_on wpci_wXTR.
          * (* lpcp component *)
            destruct (wXTR p v1) eqn:?;
            [ inv H; eapply A; eauto
            | inv H ].
          * (* same non PC outputs component *)
            destruct (wXTR p1 vs), (wXTR p2 vs);
            solve [ inv H0
                  | inv H
                  | inv H; inv H0; auto ].
          * (* same fs behaviour component *)
            destruct (wXTR p1 vs) eqn:?,
                     (wXTR p2 vs) eqn:?;
            solve_tmmw B.
        + (* ITret *)
          depend_on wpci_retTR;
          [ (* lpcp component *)
            inv H; eauto
          | (* same non PC outputs component *)
            inv H; inv H0; eauto
          | (* same fs behaviour component *)
            split; inversion 1 ].

      - (* ImoviTR *)
        refine (match it with
          | ITconst       => _
          | ITret         => _
          | ITparam o _ _ => ltac:(destruct o)
          | _ => DKnow
          end).
        + (* ITconst *)
          depend_on wpci_constTR.
          * (* lpcp component *)
            destruct (constTR p v); inv H...
          * (* same non PC outputs component *)
            destruct (constTR p1 v) eqn:X, (constTR p2 v) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H | inv H0 ].
          * (* same fs behaviour component *)
            destruct (constTR p1 v) eqn:X,
                     (constTR p2 v) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].
        + (* ITret *)
          left; simpl; split;[|split]; intros.
          * (* lpcp component *)
            inv H...
          * (* same non PC outputs component *)
            inv H; inv H0...
          * (* same fs behaviour component *)
            split; inversion 1.
        + (* ITparam Osub / ITmonus *)
          depend_on wpci_subTR.
          * (* lpcp component *)
            destruct (subTR p v v0); inv H...
          * (* same non PC outputs component *)
            destruct (subTR p1 v v0) eqn:X, (subTR p2 v v0) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H | inv H0 ].
          * (* same fs behaviour component *)
            destruct (subTR p1 v v0) eqn:X, (subTR p2 v v0) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].
        + (* ITparam Oadd / ITplus *)
          depend_on wpci_addTR.
          * (* lpcp component *)
            destruct (addTR p v v0); inv H...
          * (* same non PC outputs component *)
            destruct (addTR p1 v v0) eqn:X, (addTR p2 v v0) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H | inv H0 ].
          * (* same fs behaviour component *)
            destruct (addTR p1 v v0) eqn:X, (addTR p2 v v0) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].
(*             solve_tmmw B. *)

      - (* IopTR *)
        refine (match it with
          | ITplus  => match o with Oadd => _ | _ => DKnow end
          | ITmonus => match o with Osub => _ | _ => DKnow end
          | _ => ltac:(refine (Know _); destruct o;
                       simpl; repeat split; intros;
                       solve [ inv H
                             | auto ])
          end).
        + (* ITplus *)
          depend_on wpci_addTR.
          * (* lpcp component *)
            destruct (addTR p v1 v2); inv H...
          * (* same non PC outputs component *)
            destruct (addTR p1 v1 v2) eqn:X, (addTR p2 v1 v2) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H | inv H0 ].
          * (* same fs behaviour component *)
            destruct (addTR p1 v1 v2) eqn:X,
                     (addTR p2 v1 v2) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].

        + (* ITmonus *)
          depend_on wpci_subTR.
          * (* lpcp component *)
            destruct (subTR p v1 v2); inv H...
          * (* same non PC outputs component *)
            destruct (subTR p1 v1 v2) eqn:X, (subTR p2 v1 v2) eqn:Y;
            solve [ inv H; inv H0; erewrite A, X in Y; inv Y; auto
                  | inv H | inv H0 ].
          * (* same fs behaviour component *)
            destruct (subTR p1 v1 v2) eqn:X,
                     (subTR p2 v1 v2) eqn:Y;
            solve [ erewrite A, X in Y; inv Y; intuition
                  | split; inversion 1 ].

      - (* IcondTR *)
        refine (match it with
          | ITifS => ltac:(depend_on wpci_ifSTR)
          | ITwN  => ltac:(depend_on wpci_wNTR)
          | _ => ltac:(refine (Know _); split;
                       simpl; [inversion 4|split])
          end)...

      - (* IcallTR *)
        refine (match it with
          | ITcall => ltac:(depend_on wpci_callTR)
          | _      => ltac:(refine (Know _); split;
                            simpl; [inversion 3|split])
          end)...

      - (* IreturnTR *)
        refine (match it with
          | ITret => ltac:(depend_on wpci_retTR)
          | _     => ltac:(refine (Know _); split;
                           simpl; [inversion 3|split])
          end)...
    Defined.


    Ltac solve_tmmw' H :=
      match goal with
      | X: _ = inl _, Y: _ = inr _ 
        |- _ => erewrite H, X in Y; inv Y
      | X: _ = inr _, Y: _ = inr _ 
        |- _ => erewrite H, X in Y; inv Y; auto
      | X: _ = inl _, Y: _ = inl _ 
        |- _ => erewrite H, X in Y; inv Y; auto
      end.


    Definition spci : forall (ti: tinst), MProp (match ti with
      | (Inop    _        , it) => forall p1 p2         , InopTR    it p1          = InopTR    it p2
      | (Imov    _ _ _    , it) => forall p1 p2 v1 v2   , ImovTR    it p1 v1 v2    = ImovTR    it p2 v1 v2
      | (Imovi   _ _ _    , it) => forall p1 p2 v       , ImoviTR   it p1 v        = ImoviTR   it p2 v
      | (Iop op  _ _ _ _  , it) => forall p1 p2 v1 v2   , IopTR     it p1 op v1 v2 = IopTR     it p2 op v1 v2
      | (Icond   _ _ _ _ _, it) => forall p1 p2 c v1 v2 , IcondTR   it p1 c v1 v2  = IcondTR   it p2 c v1 v2
      | (Icall   _ _ _ _  , it) => forall p1 p2 fnt args, IcallTR   it p1 fnt args = IcallTR   it p2 fnt args
      | (Ireturn _        , it) => forall p1 p2 p_en v  , IreturnTR it p1 p_en v   = IreturnTR it p2 p_en v
      end).
    Proof with eauto.
      intros [[] it].

      - (* Inop *)
        refine (match it with
          | ITifJ => ltac:(depend_on spci_ifJTR)
          | ITwL  => ltac:(depend_on spci_wLTR )
          | ITwX  => ltac:(depend_on spci_wXTR )
          | _ => DKnow
          end)...

      - (* Imov *)
        refine (match it with
          | ITvar    => DKnow (* by design of whilef sem *)
          | ITifJ    => _
          | ITwL     => _
          | ITwX     => _
          | ITret    => DKnow
          | ITsavePC => DKnow
          | ITassign => _
          | _ => DKnow
          end).
        + (* ITassign *)
          depend_on spci_assignTR.
          destruct dnd_assignTR; erewrite A...
        + (* ITifJ *)
          depend_on spci_ifJTR. erewrite A...
        + (* ITwL *)
          depend_on spci_wLTR. erewrite A...
        + (* ITwX *)
          depend_on spci_wXTR. erewrite A...

      - (* Imovi *)
        (* by design of whilef sem *)
        refine (match it with
          | ITconst       => DKnow
          | ITret         => DKnow
          | ITparam o _ _ => DKnow
          | _ => DKnow
          end).

      - (* IopTR *)
        refine (match it with
          | ITplus  => match o with Oadd => DKnow | _ => DKnow end
          | ITmonus => match o with Osub => DKnow | _ => DKnow end
          | _ => ltac:(refine (Know _); auto)
          end).

      - (* Icond *)
        refine (match it with
          | ITifS => ltac:(depend_on spci_ifSTR)
          | ITwN  => ltac:(depend_on spci_wNTR )
          | _ => DKnow
        end)...

      - (* IcallTR *)
        refine (match it with
          | ITcall => ltac:(depend_on spci_callTR)
          | _ => DKnow
          end)...

      - (* IreturnTR *)
        refine (match it with
          | ITret => ltac:(depend_on spci_retTR)
          | _ => DKnow
          end)...
    Defined.

End PolicyPropsInjection.

Module Type RTLT_Policy_PropT
    (Export FTags    : TagDomain.FrontEnd)
    (Export HRules   : HLL.Policy.Sig FTags)
    (Export HFlags   : HLL.Policy.Props FTags HRules)
    (Export MTagT    : TagDomain_MiddleTgn FTags)
    (Export RRuleT   : RTLT_Policy_Tgn FTags MTagT HRules HFlags)
    (Export RTLT_Tgn : RTLT.Language.Sig MTagT)
      <: RTLT.Policy.Props MTagT RTLT_Tgn RRuleT.
Include PolicyPropsInjection FTags HRules HFlags MTagT RRuleT RTLT_Tgn.
End RTLT_Policy_PropT.
