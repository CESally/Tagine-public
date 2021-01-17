From CompCert Require Import Errors.
From PIPE     Require Import TagDomain.
From HLL      Require Import Language Policy.
From RTLT     Require Import Language.
From RTLgenT  Require Import Inj Env SEMonad.


Module Functor (Import STags  : TagDomain.FrontEnd)
               (Import Source : HLL.Language.Sig STags)
               (Import TTags  : TagDomain_MiddleTgn STags)
               (Import Target : RTLT.Language.Sig TTags)
               (Import CompEnv: Env.CEnvSig STags Source TTags Target)
               (Import SRules : HLL.Policy.Sig STags)
               (Import SFlags : HLL.Policy.Props STags SRules).
Import ListNotations.

Module Export CompilerMonad := SEMonad.Functor STags Source TTags Target CompEnv.
Local Open Scope rtlgent_scope.

Remark new_reg_earlier:
  forall s,
  state_earlier s (mkstate (Pos.succ s.(st_nextreg))
                         s.(st_nextnode) s.(st_code) s.(st_wf)).
Proof.
  constructor; simpl. apply Ple_refl. apply Ple_succ. auto.
Qed.

Definition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg)
       (mkstate (Pos.succ s.(st_nextreg)) s.(st_nextnode) s.(st_code) s.(st_wf))
       (new_reg_earlier s).

Fixpoint new_regs (map: mapping) (al: list expr)
                    {struct al}: mon (list reg) :=
  match al with
  | [] =>
      ret nil
  | a :: bl =>
      do r  <- new_reg;
      do rl <- new_regs map bl;
      ret (r :: rl)
  end.

Definition add_var (map: mapping) (x: ident) : mon (reg * mapping) :=
  do r <- new_reg; ret (r, (map!x <- r)).

Fixpoint add_vars (map: mapping) (xs: list ident)
                  {struct xs} : mon (list reg * mapping) :=
  match xs with
  | nil => ret (nil, map)
  | x :: xs =>
      do (rs, map1) <- add_vars map  xs;
      do (r , map2) <- add_var  map1 x;
      ret (r :: rs, map2)
  end.

Definition str_of_pos (s:string) (p:positive) : string := s.
 (**r TODO: find a scheme to report variable names *)

Definition find_var (map: mapping) (x: ident) : mon reg :=
  match map!x with
  | Some r => ret r
  | None   => error (str_of_pos "RTLgen: unbound variable " x)
  end.



Fixpoint transl_expr (map : mapping) (a : expr) (ns : node)
                     {struct a} : mon (reg * node) :=
  match a with
  | Elit l => do rd <- new_reg;
              do ne <- add_instr (Imovi ($ l) rd ns) ITconst;
                ret (rd,ne)
  | Evar v => do rd <- new_reg;
              do rs <- find_var map v;
              do ne <- add_instr (Imov rs rd ns) ITvar;
                ret (rd,ne)
  | Eop op a1 a2 =>
      do rd <- new_reg;
      do n2 <- reserve_instr;
      do (r2,n1) <- transl_expr map a2 n2;
      do (r1,ne) <- transl_expr map a1 n1;
      do xx <- update_instr n2 (Iop op r1 r2 rd ns) (ITop op);
        ret (rd,ne)
  end.


Fixpoint transl_exprlist (map: mapping) (al: list expr) (ns: node)
                     {struct al} : mon (list reg * node) :=
  match al with
  | []      => ret ([], ns)
  | b :: bs => do (rs, n1) <- transl_exprlist map bs ns;
               do (r , ne) <- transl_expr map b n1;
                 ret (r :: rs, ne)
  end.


Fixpoint transl_stmt (map: mapping) (s: stmt) (ns: node)
                     (nret: node) (rret: reg) {struct s} : mon node :=
  match s with
  | Sseq s1 s2 =>
      do n1 <- transl_stmt map s2 ns nret rret;
        transl_stmt map s1 n1 nret rret
  | Sskip =>
      ret ns
  | Sassign x a =>
      do rx <- find_var map x;
      do n1 <- reserve_instr;
      do (ra, ne) <- transl_expr map a n1;
      do xx <- update_instr n1 (Imov ra rx ns) ITassign;
        ret ne
  | Sifthenelse c a1 a2 strue sfalse =>
    match cf_strategy with Normal =>
      (* both saves & joins *)
      do rj <- new_reg;
      do njoin <- add_tinst (PIrecover rj ns ITifJ);
      do nfalse <- transl_stmt map sfalse njoin nret rret;
      do ntrue  <- transl_stmt map strue  njoin nret rret;
      do ncond <- reserve_instr;
      do (r2, n2) <- transl_expr map a2 ncond;
      do (r1, n1) <- transl_expr map a1 n2;
      do ne <- add_tinst (PIsave rj n1);
      do xc <- update_instr ncond (Icond c r1 r2 ntrue nfalse) ITifS;
        ret ne
    | No_saves _ =>
      (* no saves, but joinTR fires *)
      do njoin <- add_tinst (Inop ns, ITifJ);
      do nfalse <- transl_stmt map sfalse njoin nret rret;
      do ntrue  <- transl_stmt map strue  njoin nret rret;
      do ncond <- reserve_instr;
      do (r2, n1) <- transl_expr map a2 ncond;
      do (r1, ne) <- transl_expr map a1 n1;
      do xc <- update_instr ncond (Icond c r1 r2 ntrue nfalse) ITifS;
        ret ne
    | No_joins_nor_saves _ =>
      (* no saves & no joins *)
      do nfalse <- transl_stmt map sfalse ns nret rret;
      do ntrue  <- transl_stmt map strue  ns nret rret;
      do ncond <- reserve_instr;
      do (r2, n1) <- transl_expr map a2 ncond;
      do (r1, ne) <- transl_expr map a1 n1;
      do xc <- update_instr ncond (Icond c r1 r2 ntrue nfalse) ITifS;
        ret ne
    end
  | Swhile c a1 a2 body =>
    match cf_strategy with Normal =>
      (* both saves & joins *)
      do rj <- new_reg;
      do nexit <- add_tinst (PIrecover rj ns ITwX);
      do nloop <- reserve_instr;
      do nbody <- transl_stmt map body nloop nret rret;
      do ncond <- reserve_instr;
      do (r2,n2) <- transl_expr map a2 ncond;
      do (r1,n1) <- transl_expr map a1 n2;
      do ne <- add_tinst (PIsave rj n1);
      do xx <- update_instr ncond (Icond c r1 r2 nbody nexit) ITwN;
      do xy <- update_tinst nloop (PIrecover rj ne ITwL);
        ret ne
    | No_saves _ =>
      (* no saves, but wLTR & wXTR fire *)
      do nexit <- add_tinst (Inop ns, ITwX);
      do nloop <- reserve_instr;
      do nbody <- transl_stmt map body nloop nret rret;
      do ncond <- reserve_instr;
      do (r2,n2) <- transl_expr map a2 ncond;
      do (r1,n1) <- transl_expr map a1 n2;
      do ne <- add_tinst (noop n1);
      do xx <- update_instr ncond (Icond c r1 r2 nbody nexit) ITwN;
      do xy <- update_tinst nloop (Inop ne, ITwL);
        ret ne
    | No_joins_nor_saves _ =>
      (* no saves & no joins *)
      do ne <- reserve_instr;
      do nbody <- transl_stmt map body ne nret rret;
      do ncond <- reserve_instr;
      do (r2,n2) <- transl_expr map a2 ncond;
      do (r1,n1) <- transl_expr map a1 n2;
      do xc <- update_instr ncond (Icond c r1 r2 nbody ns) ITwN;
      do xe <- update_instr ne (Inop n1) ITnone;
        ret ne
    end
  | Scall x fid cl =>
      do rargs <- new_regs map cl;
      do rx <- find_var map x;
      do n1 <- reserve_instr;
      do (rargs, ne) <- transl_exprlist map cl n1;
      do xx <- update_instr n1 (Icall fid rargs rx ns) ITcall;
        ret ne
  | Sreturn a =>
      do n1 <- reserve_instr;
      do (rd, ne) <- transl_expr map a n1;
      do xx <- update_instr n1 (Imov rd rret nret) ITret;
        ret ne
  end.



Definition transl_fun_aux (f: Source.function) : mon (node * list reg) :=
  do (rparams, map1) <- add_vars init_mapping f.(Source.params);
  do (rlocals, map2) <- add_vars map1 f.(Source.locals);
  do rret <- new_reg;
  do nret <- add_instr (Ireturn rret) ITret;
  do nd   <- add_instr (Imovi defLit rret nret) ITret;
  do nentry <- transl_stmt map2 f.(Source.body) nd nret rret;
  ret (nentry, rparams).

Definition transl_function (f: Source.function) : Errors.res Target.function :=
  match transl_fun_aux f init_state with
  | Error msg => Errors.Error [MSG msg]
  | OK (nentry, rparams) s i => Errors.OK ( Target.mkfunction
                                            f.(Source.arity)
                                            rparams
                                            s.(st_code)
                                            nentry
                                            f.(Source.fntag))
  end.

Local Open Scope error_monad_scope.
Fixpoint transl_program (p: Source.program) : Errors.res Target.program :=
  match p with
  | (i,f) :: tl => do tf <- transl_function f;
                   do tp <- transl_program tl;
                     Errors.OK ((i,tf) :: tp)
  | []          => Errors.OK []
  end.

Local Close Scope error_monad_scope.
End Functor.
