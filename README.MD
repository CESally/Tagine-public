This directory contains the codebase of the Tagine prototype compiler as described in CPP '21 Towards Formally Verified Compilation of Tag-Based Policy Enforcement

The project only requires the Coq proof assistant and builds under version 8.10




Architectural notes
--------------------------------------------------

The top level semantic preservation theorems can be found in `pfrtlgent/Toplevel.v` and `pfdeadcodet/Toplevel.v`

**Intermediate Representations**

- `hll/`
  This directory contains the definition of the HLL IR. We have tried to factorize the IR's syntax to be separate from both its semantics and its policy signature. `Policy.v` defines the set of rules needed to implement a HLL policy. These are in a 1-to-1 correspondence with Control Points.
  + hll/Language.v
  + hll/Semantics.v
  + hll/Policy.v

- `rtl/`
  This directory contains the definition of the RTL<sup>T</sup> IR . Its structure is similar to the `hll/` directory.
  + rtlt/Language.v
  + rtlt/Semantics.v
  + rtlt/Policy.v

**Compiler passes**

- `rtlgent/`
  The definition of the RTLgen<sup>T</sup> translation pass from HLL to RTL<sup>T</sup>.
  `Inj.v` defines a target tag set out of a source one.
  `Env.v` defines some notations and lemmas
  `SEMonad.v` is the definition of a monad used from compilation
  `Compiler.v` is the actual compiler function definitions.

  + rtlgent/Inj.v
  + rtlgent/Env.v
  + rtlgent/SEMonad.v
  + rtlgent/Compiler.v

- `pfrtlgent/`
  The proof of correctness for RTLgen<sup>T</sup>
  `Inj.v` is the defines a target policy out of a source one, as well as the injection of policy properties.
  `Env.v` contains some notations and lemmas.
  `Matching.v` contains the matching relation. This matching relation does not speak to the compiler/translation functions directly. Instead `ModelsMatching.v` demonstrates that each constituent matching relation (matching over expressions, statements etc) logically follows from their compilation functions. That is, if C is the result of compiling S, then S ~ C, where S and C are source and target expressions/statements/etc.
  `Sim.v` contains the forward simulation argument. **This is the real heart of the proof.** The semantic preservation theorem follows as a corollary.
  `Toplevel.v` contains just the semantic preservation theorem, and is a ``superfluous'' file, in that is intended for presentation purposes.

  + pfrtlgent/Inj.v
  + pfrtlgent/Env.v
  + pfrtlgent/Matching.v
  + pfrtlgent/ModelsMatching.v
  + pfrtlgent/Sim.v
  + pfrtlgent/Toplevel.v

- `deadcodet/`
  The definition of the Deadcode<sup>T</sup> optimization pass over RTL<sup>T</sup>. The directory contains the domain (for the dataflow analysis) and the compiler.
  + deadcode/DeadDomain.v
  + deadcode/Compiler.v

- `pfdeadcodet/`
  The proof of correctness for Deadcode<sup>T</sup>.
  + pfdeadcode/MatchingSim.v

- `cset/`
  The definition of a compiler pass for common sub-expression elimination. This pass does not have an accompanying proof, though our paper discusses it's design.
  + cset/CSETdomain.v
  + cset/Compiler.v

- `compcert/`
  This directory contains files directly taken from CompCert. They mostly consist of analyses used by the optimizations, as well as some general utility tactics used in many files.
  + compcert/Axioms.v
  + compcert/Iteration.v
  + compcert/Maps.v
  + compcert/Coqlib.v
  + compcert/Kildall.v
  + compcert/Ordered.v
  + compcert/Heaps.v
  + compcert/Lattice.v
  + compcert/Wfsimpl.v
  + compcert/Errors.v

- `utils/`
  This directory contains the metatheory of program behaviours and general transition semantics
  + utils/Behaviours.v
  + utils/Defns.v
  + utils/Smallstep.v

- `pipe/`
  Contains the signatures of tag domains used at different stages of the compiler toolchain
  + pipe/TagDomain.v



