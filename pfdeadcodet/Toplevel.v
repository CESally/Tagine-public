From PIPE     Require Import TagDomain.
From HLL      Require Import Policy.
From Utils    Require Import Defns Smallstep Behaviours.
From RTLgenT  Require Import Inj.
From RGTpf    Require Import Inj.
From DCTpf    Require Export MatchingSim.
Import List Notations.

Module Thm (Export FTags  : TagDomain.FrontEnd)
           (Export HRules : HLL.Policy.Sig FTags)
           (Export HFlags : HLL.Policy.Props FTags HRules)
           (Export Tags   : TagDomain_MiddleTgn FTags)
           (Export Rules  : RTLT_Policy_Tgn FTags Tags HRules HFlags)
           (Export Lang   : RTLT.Language.Sig Tags)
           (Import Sem    : RTLT.Semantics.Sig Tags Rules Lang)
           (Import Flags  : RTLT_Policy_PropT FTags HRules HFlags Tags Rules Lang).


Module Import Simulation := MatchingSim.Functor
                              FTags HRules HFlags
                              Tags Rules Lang Sem Flags.


Locate program_behaves.
Print  program_behaves.
Locate behaviour_improves.
Print  behaviour_improves.
Locate not_wrong.
Print  not_wrong.

Section Proof.
Variable  prog : Lang.program.
Variable tprog : Lang.program.
Hypothesis TRANSL : match_prog prog tprog.

Let SrcProg := Sem.RTLT_semantics  prog. (* is the semantics of RTLT param-ed by prog *)
Let TgtProg := Sem.RTLT_semantics tprog.


Theorem Semantic_Preservation  :
  (forall behS, program_behaves SrcProg behS -> not_wrong behS) ->
   forall behT, program_behaves TgtProg behT -> exists behS,
  program_behaves SrcProg behS /\ behaviour_matches match_atom match_TagErr behS behT.
Proof Simulation.refinement_for_safe_programs prog tprog TRANSL.

End Proof.
End Thm.
