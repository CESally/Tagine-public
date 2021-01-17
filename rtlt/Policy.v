From Utils Require Export Defns.
From PIPE  Require Export TagDomain.
From RTLT  Require Export Language.


Module Type Sig (Import Tags : TagDomain.MiddleEnd).

  Parameters
  (InopTR    : ITag -> PCTag ->                                   M  PCTag)
  (ImovTR    : ITag -> PCTag -> ValTag -> ValTag ->               M (PCTag * ValTag))
  (ImoviTR   : ITag -> PCTag -> ValTag ->                         M (PCTag * ValTag))
  (IopTR     : ITag -> PCTag -> operation  -> ValTag -> ValTag -> M (PCTag * ValTag))
  (IcondTR   : ITag -> PCTag -> comparison -> ValTag -> ValTag -> M  PCTag)
  (IcallTR   : ITag -> PCTag -> PCTag -> list ValTag ->           M  PCTag)
  (IreturnTR : ITag -> PCTag -> PCTag -> ValTag ->                M  PCTag).

  Parameter real_nopTR: forall p, InopTR defIT p = ret p.

End Sig.


Module Type Props (Import Tags   : PIPE.TagDomain.MiddleEnd)
                  (Import Lang   : RTLT.Language.Sig Tags)
                  (Import Policy : RTLT.Policy.Sig Tags).

  Notation    InopTR_is_lpcp it    := (forall p p'         ,    InopTR it p          = ret  p'     -> p = p').
  Notation    ImovTR_is_lpcp it    := (forall p p' v1 v2 v',    ImovTR it p v1 v2    = ret (p',v') -> p = p').
  Notation   ImoviTR_is_lpcp it    := (forall p p' v v'    ,   ImoviTR it p v        = ret (p',v') -> p = p').
  Notation     IopTR_is_lpcp it op := (forall p p' v1 v2 v',     IopTR it p op v1 v2 = ret (p',v') -> p = p').
  Notation   IcondTR_is_lpcp it    := (forall p p' c v1 v2 ,   IcondTR it p c v1 v2  = ret  p'     -> p = p').
  Notation   IcallTR_is_lpcp it    := (forall p p' fnt args,   IcallTR it p fnt args = ret  p'     -> p = p').
  Notation IreturnTR_is_lpcp it    := (forall p p' p_en v  , IreturnTR it p p_en v   = ret  p'     -> p = p').

  Parameter dnd_ImovTR : forall it, MProp (forall p v d1 d2, ImovTR it p v d1 = ImovTR it p v d2).

  Parameter lpcp : forall (ti: tinst), MProp (match ti with
    | (Inop    _        , it) =>    InopTR_is_lpcp it
    | (Imov    _ _ _    , it) =>    ImovTR_is_lpcp it
    | (Imovi   _ _ _    , it) =>   ImoviTR_is_lpcp it
    | (Iop op  _ _ _ _  , it) =>     IopTR_is_lpcp it op
    | (Icond   _ _ _ _ _, it) =>   IcondTR_is_lpcp it
    | (Icall   _ _ _ _  , it) =>   IcallTR_is_lpcp it
    | (Ireturn _        , it) => IreturnTR_is_lpcp it
    end).

  Parameter dfs : forall (ti: tinst), MProp (match ti with
    | (Inop    _        , it) => forall p          e,    InopTR it p          <> fstop e
    | (Imov    _ _ _    , it) => forall p v1 v2    e,    ImovTR it p v1 v2    <> fstop e
    | (Imovi   _ _ _    , it) => forall p v        e,   ImoviTR it p v        <> fstop e
    | (Iop op  _ _ _ _  , it) => forall p   v1 v2  e,     IopTR it p op v1 v2 <> fstop e
    | (Icond   _ _ _ _ _, it) => forall p c v1 v2  e,   IcondTR it p  c v1 v2 <> fstop e
    | (Icall   _ _ _ _  , it) => forall p fnt args e,   IcallTR it p fnt args <> fstop e
    | (Ireturn _        , it) => forall p p_en v   e, IreturnTR it p p_en v   <> fstop e
    end).

  Parameter wpci : forall (ti: tinst), MProp (match ti with
    | (Inop    _        , it) => InopTR_is_lpcp it
                              /\ forall p1 p2 e, InopTR it p1 = fstop e <->
                                                 InopTR it p2 = fstop e
    | (Icond   _ _ _ _ _, it) => IcondTR_is_lpcp it
                              /\ forall p1 p2 c v1 v2 e, IcondTR it p1 c v1 v2 = fstop e <->
                                                         IcondTR it p2 c v1 v2 = fstop e
    | (Icall   _ _ _ _  , it) => IcallTR_is_lpcp it
                              /\ forall p1 p2 fnt args e, IcallTR it p1 fnt args = fstop e <->
                                                          IcallTR it p2 fnt args = fstop e
    | (Ireturn _        , it) => IreturnTR_is_lpcp it
                              /\ forall p1 p2 p_en v e, IreturnTR it p1 p_en v = fstop e <->
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

  Parameter spci : forall (ti: tinst), MProp (match ti with
    | (Inop    _        , it) => forall p1 p2         ,    InopTR it p1          =    InopTR it p2
    | (Imov    _ _ _    , it) => forall p1 p2 v1 v2   ,    ImovTR it p1 v1 v2    =    ImovTR it p2 v1 v2
    | (Imovi   _ _ _    , it) => forall p1 p2 v       ,   ImoviTR it p1 v        =   ImoviTR it p2 v
    | (Iop op  _ _ _ _  , it) => forall p1 p2 v1 v2   ,     IopTR it p1 op v1 v2 =     IopTR it p2 op v1 v2
    | (Icond   _ _ _ _ _, it) => forall p1 p2 c v1 v2 ,   IcondTR it p1 c v1 v2  =   IcondTR it p2 c v1 v2
    | (Icall   _ _ _ _  , it) => forall p1 p2 fnt args,   IcallTR it p1 fnt args =   IcallTR it p2 fnt args
    | (Ireturn _        , it) => forall p1 p2 p_en v  , IreturnTR it p1 p_en v   = IreturnTR it p2 p_en v
  end).

End Props.