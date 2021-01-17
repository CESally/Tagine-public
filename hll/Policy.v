From Utils Require Export Defns.
From PIPE  Require Export TagDomain.


Module Type Sig (Import Tags : TagDomain.FrontEnd).

  Parameter constTR : PCTag -> ValTag -> M ValTag.
  Parameter varTR   : PCTag -> ValTag -> M ValTag.
  Parameter addTR   : PCTag -> ValTag -> ValTag -> M ValTag.
  Parameter subTR   : PCTag -> ValTag -> ValTag -> M ValTag.

  Definition opTR op :=
    match op with
    | Oadd => addTR
    | Osub => subTR
    end.

  Parameter assignTR : forall (curr: PCTag) (lv rv: ValTag), M (PCTag * ValTag).

  (* if Split TR *)
  (* if Join  TR *)
  Parameter ifSTR : forall (curr: PCTag) (cmp: comparison)
                           (lv rv: ValTag)    , M PCTag.
  Parameter ifJTR : forall (curr split: PCTag), M PCTag.

  (* while eNtry TR *)
  (* while Loop  TR *)
  (* while eXit  TR *)
  Parameter wNTR : forall (entry: PCTag) (cmp: comparison)
                          (lv rv: ValTag)    , M PCTag.
  Parameter wLTR : forall (curr split: PCTag), M PCTag.
  Parameter wXTR : forall (curr split: PCTag), M PCTag.


  Parameter callTR : forall (curr callee_fntag: PCTag)
                            (arg_tags: list ValTag), M PCTag.
  Parameter retTR  : forall (curr fn_entry: PCTag)
                            (retval: ValTag)       , M PCTag.

End Sig.


Module Type Props (Import Tags   : PIPE.TagDomain.FrontEnd)
                  (Import Policy : Policy.Sig Tags).

  Notation assignTR_is_lpcp := (forall p p' vl vr v', assignTR p vl vr    = ret (p',v') -> p = p').
  Notation    ifSTR_is_lpcp := (forall p p' c l r   ,    ifSTR p c l r    = ret  p'     -> p = p').
  Notation    ifJTR_is_lpcp := (forall p p' sp      ,    ifJTR p sp       = ret  p'     -> p = p').
  Notation     wNTR_is_lpcp := (forall p p' c v1 v2 ,     wNTR p c v1 v2  = ret  p'     -> p = p').
  Notation     wLTR_is_lpcp := (forall p p' sp      ,     wLTR p sp       = ret  p'     -> p = p').
  Notation     wXTR_is_lpcp := (forall p p' sp      ,     wXTR p sp       = ret  p'     -> p = p').
  Notation   callTR_is_lpcp := (forall p p' fnt args,   callTR p fnt args = ret  p'     -> p = p').
  Notation    retTR_is_lpcp := (forall p p' p_en v  ,    retTR p p_en v   = ret  p'     -> p = p').

  Notation varTR_is_dfs := (forall p v e , varTR p v  <> fstop e).
  Notation ifJTR_is_dfs := (forall p sp e, ifJTR p sp <> fstop e).
  Notation  wLTR_is_dfs := (forall p sp e,  wLTR p sp <> fstop e).
  Notation  wXTR_is_dfs := (forall p sp e,  wXTR p sp <> fstop e).

  Parameter

    (* dnd := doesn't need destination *)
    (dnd_assignTR : MProp (forall p vr vx vy, assignTR p vx vr = assignTR p vy vr))

    (one_pct_val  : MProp (forall p1 p2 :  PCTag, p1 = p2))
    (one_vt_val   : MProp (forall v1 v2 : ValTag, v1 = v2))

    (* lpcp := local pc pure *)
    (lpcp_assignTR : MProp assignTR_is_lpcp)
    (lpcp_ifSTR    : MProp    ifSTR_is_lpcp)
    (lpcp_ifJTR    : MProp    ifJTR_is_lpcp)
    (lpcp_wNTR     : MProp     wNTR_is_lpcp)
    (lpcp_wLTR     : MProp     wLTR_is_lpcp)
    (lpcp_wXTR     : MProp     wXTR_is_lpcp)
    (lpcp_callTR   : MProp   callTR_is_lpcp)
    (lpcp_retTR    : MProp    retTR_is_lpcp)

    (* doesn't fstop *)
    (dfs_constTR  : MProp (forall p v e       ,  constTR p v        <> fstop e))
    (dfs_varTR    : MProp  varTR_is_dfs                                        )
    (dfs_addTR    : MProp (forall p v1 v2 e   ,    addTR p v1 v2    <> fstop e))
    (dfs_subTR    : MProp (forall p v1 v2 e   ,    subTR p v1 v2    <> fstop e))
    (dfs_assignTR : MProp (forall p lv rv e   , assignTR p lv rv    <> fstop e))
    (dfs_ifSTR    : MProp (forall p c vl vr e ,    ifSTR p c vl vr  <> fstop e))
    (dfs_ifJTR    : MProp ifJTR_is_dfs                                         )
    (dfs_wNTR     : MProp (forall p c vl vr e ,     wNTR p c vl vr  <> fstop e))
    (dfs_wLTR     : MProp  wLTR_is_dfs                                         )
    (dfs_wXTR     : MProp  wXTR_is_dfs                                         )
    (dfs_callTR   : MProp (forall p fnt args e,   callTR p fnt args <> fstop e))
    (dfs_retTR    : MProp (forall p p_en v e  ,    retTR p p_en v   <> fstop e))




    (* pc insensitivity *)
    (* weak   pci := fses & value outputs do not depend on PC, and rule is lpcp *)
    (* strong pci := fses & all   outputs do not depend on PC. (e.g. output PC comes from vals) *)


    (* for the expr rules (which, by design, do not output a PC tag (exprs are PC side-effect free))
       in particular, expr rules cannot be spci. Even though this looks similar in format to spci
       rules, it is really an encoding of wpci.  *)
    (wpci_constTR  : MProp (forall p1 p2 v       ,  constTR p1 v        =  constTR p2 v       ))
    (wpci_varTR    : MProp (forall p1 p2 v       ,    varTR p1 v        =    varTR p2 v       ))
    (wpci_addTR    : MProp (forall p1 p2 v1 v2   ,    addTR p1 v1 v2    =    addTR p2 v1 v2   ))
    (wpci_subTR    : MProp (forall p1 p2 v1 v2   ,    subTR p1 v1 v2    =    subTR p2 v1 v2   ))


    (* see for yourself if you'd like *)
(*  (wpci_constTR : MProp ((forall p1 p2 v v1' v2' ,
                              constTR p1 v = ret v1' ->
                              constTR p2 v = ret v2' -> v1' = v2') /\
                            forall p1 p2 v e, constTR p1 v = fstop e <-> constTR p2 v = fstop e))
    (wpci_varTR   : MProp ((forall p1 p2 v v1' v2' ,
                              varTR p1 v = ret v1' ->
                              varTR p2 v = ret v2' -> v1' = v2') /\
                            forall p1 p2 v e, varTR p1 v = fstop e <-> varTR p2 v = fstop e))
    (wpci_addTR   : MProp ((forall p1 p2 v1 v2 v1' v2',
                            addTR p1 v1 v2 = ret v1' ->
                            addTR p2 v1 v2 = ret v2' -> v1' = v2') /\
                            forall p1 p2 v1 v2 e, addTR p1 v1 v2 = fstop e
                                              <-> addTR p2 v1 v2 = fstop e))
    (wpci_subTR   : MProp ((forall p1 p2 v1 v2 v1' v2',
                            subTR p1 v1 v2 = ret v1' ->
                            subTR p2 v1 v2 = ret v2' -> v1' = v2') /\
                            forall p1 p2 v1 v2 e, subTR p1 v1 v2 = fstop e
                                              <-> subTR p2 v1 v2 = fstop e)) *)

    (* weak pci *)
    (wpci_assignTR : MProp (assignTR_is_lpcp
                        /\ (forall p1 p2 vl vr p1' p2' v1' v2',
                              assignTR p1 vl vr = ret (p1',v1') ->
                              assignTR p2 vl vr = ret (p2',v2') ->
                              v1' = v2')
                        /\  forall p1 p2 vl vr e,
                              assignTR p1 vl vr = fstop e <-> assignTR p2 vl vr = fstop e))

    (wpci_ifSTR  : MProp ( ifSTR_is_lpcp /\ forall p1 p2 c lv rv  e,  ifSTR p1 c lv rv  = fstop e <->  ifSTR p2 c lv rv  = fstop e))
    (wpci_ifJTR  : MProp ( ifJTR_is_lpcp /\ forall p1 p2 sp       e,  ifJTR p1 sp       = fstop e <->  ifJTR p2 sp       = fstop e))
    (wpci_wNTR   : MProp (  wNTR_is_lpcp /\ forall p1 p2 c lv rv  e,   wNTR p1 c lv rv  = fstop e <->   wNTR p2 c lv rv  = fstop e))
    (wpci_wLTR   : MProp (  wLTR_is_lpcp /\ forall p1 p2 sp       e,   wLTR p1 sp       = fstop e <->   wLTR p2 sp       = fstop e))
    (wpci_wXTR   : MProp (  wXTR_is_lpcp /\ forall p1 p2 sp       e,   wXTR p1 sp       = fstop e <->   wXTR p2 sp       = fstop e))
    (wpci_callTR : MProp (callTR_is_lpcp /\ forall p1 p2 fnt args e, callTR p1 fnt args = fstop e <-> callTR p2 fnt args = fstop e))
    (wpci_retTR  : MProp ( retTR_is_lpcp /\ forall p1 p2 p_en v   e,  retTR p1 p_en v   = fstop e <->  retTR p2 p_en v   = fstop e))

    (* strong pci *)

    (spci_assignTR : MProp (forall p1 p2 vl vr   , assignTR p1 vl vr    = assignTR p2 vl vr   ))
    (spci_ifSTR    : MProp (forall p1 p2 c lv rv ,    ifSTR p1 c lv rv  =    ifSTR p2 c lv rv ))
    (spci_ifJTR    : MProp (forall p1 p2 sp      ,    ifJTR p1 sp       =    ifJTR p2 sp      ))
    (spci_wNTR     : MProp (forall p1 p2 c lv rv ,     wNTR p1 c lv rv  =     wNTR p2 c lv rv ))
    (spci_wLTR     : MProp (forall p1 p2 sp      ,     wLTR p1 sp       =     wLTR p2 sp      ))
    (spci_wXTR     : MProp (forall p1 p2 sp      ,     wXTR p1 sp       =     wXTR p2 sp      ))
    (spci_callTR   : MProp (forall p1 p2 fnt args,   callTR p1 fnt args =   callTR p2 fnt args))
    (spci_retTR    : MProp (forall p1 p2 p_en v  ,    retTR p1 p_en v   =    retTR p2 p_en v  ))


    (* redundancy *)
    (redun_varTR : MProp (varTR_is_dfs /\ forall p v v', varTR p v = ret v' -> v = v')).

  Inductive PolCF :=
  | Normal : PolCF
  | No_saves:(forall p sp1 sp2,
                  ifJTR p sp1 = ifJTR p sp2
               /\  wLTR p sp1 =  wLTR p sp2
               /\  wXTR p sp1 =  wXTR p sp2)
               -> PolCF
  | No_joins_nor_saves : ifJTR_is_dfs /\ ifJTR_is_lpcp
                      /\  wLTR_is_dfs /\  wLTR_is_lpcp
                      /\  wXTR_is_dfs /\  wXTR_is_lpcp
                      -> PolCF.
  Extract Inductive PolCF => "option bool" ["Some true" "Some false" "None"].

  Parameter cf_strategy : PolCF.


(*   Theorem opc__wpci_is_spci: (forall p1 p2 : PCTag, p1 = p2) ->
    ((forall p p' vl vr v', assignTR p vl vr    = ret (p',v') -> p = p')
     <-> 
     (forall p1 p2 vl vr   , assignTR p1 vl vr    = assignTR p2 vl vr   )).
  Proof with auto.
    split; intros.
    - rename p1 into p. rewrite (H p2 p) in *...
    - rewrite (H p' p) in *. auto.
  Qed.

  Theorem wspci_disjoint_assignTR: (exists p1 p2: PCTag, p1 <> p2) ->
    (wpci_assignTR &p spci_assignTR) = DKnow.
  Proof with auto.
    destruct wpci_assignTR as [[A [B C]] |], spci_assignTR as [D|]; auto;
    intros [p1 [p2 dp]]; exfalso.
    destruct (assignTR p1 defVT defVT) as [[p1' v1']|e1] eqn:X,
             (assignTR p2 defVT defVT) as [[p2' v2']|e2] eqn:Y.
    - rewrite <- (A _ _ _ _ _ X) in X. rewrite (D _ p2) in X.
      pose proof (A _ _ _ _ _ X)...
    - erewrite D, Y in X. inv X.
    - erewrite D, Y in X. inv X.
    - 
    apply A in X.
    
  Qed. *)

End Props.