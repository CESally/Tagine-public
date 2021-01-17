From PIPE    Require Import TagDomain.
From HLL     Require Import Policy Semantics.
From Utils   Require Import Defns Smallstep Behaviours.
From RTLgenT Require Import Compiler.
From RGTpf   Require Export Sim.
Import List Notations.


Module Thm (Export STags  : TagDomain.FrontEnd)
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

Module Import Simulation := RGTpf.Sim.Functor
                      STags Source
                      TTags Target
                      CompEnv
                      SRules SFlags
                      TRules TFlags
                      SSem
                      TSem.

Locate match_atom.
Print  match_atom.
Locate match_TagErr.
Print  match_TagErr.
Locate program_behaves.
Print  program_behaves.
Locate not_wrong.
Print  not_wrong.
Locate behaviour_improves.
Print  behaviour_improves.

Section Proof.
Variable  prog: Source.program.
Variable tprog: Target.program.
Hypothesis TRANSL: match_prog prog tprog.

Let SrcProg := SSem.HLL_semantics   prog. (* the semantics of HLL (param-ed by prog) *)
Let TgtProg := TSem.RTLT_semantics tprog.

Theorem Semantic_Preservation_RTLgenT :
  (forall behNW, program_behaves SrcProg behNW -> not_wrong behNW) ->
   forall behT, program_behaves TgtProg behT -> exists behS,
  program_behaves SrcProg behS /\ behaviour_matches match_atom match_TagErr behS behT.

Proof Simulation.refinement_for_safe_programs prog tprog TRANSL.

End Proof.

End Thm.
