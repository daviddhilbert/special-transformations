# Module compatibility for the downstream Palomar submission

This isolated compatibility branch starts from the checked weighted-zero
revision 25852c85a31c67069b148bd31348128318303510. It does not replace the
Special transformations release or its separate Palomar entry.

The changes add Lean module headers, public imports and exposed declaration
sections to the inherited sources. Compiler-required helper visibility and
explicit Mathlib imports are adjusted. Mathematical declaration types and
proof bodies are retained. ACVF-QE is pinned to the published module-compatible
revision 8f90dfd22de9f2c821382830eee326d1f0cf4990 with the same Lean 4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

The downstream module-format Integration7.HKPrincipalVolumeKernel and
PalomarPaperSolution build passed locally. The exported principal-kernel type
retains the canonical-model and BaseContext hypotheses. Its axiom audit uses
only propext, Classical.choice and Quot.sound. This checks the dependency
closure consumed by that entry, not a new audit of every predecessor module.
Full Palomar preflight and registration belong to the downstream submission
and have not occurred at this preparation stage.
