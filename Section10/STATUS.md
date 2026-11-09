# Section 10 status

The verification recorded below used Lean 4.33.1. The standalone
Section10 target is a local checkpoint on the Lean 4.35.0 main
baseline. Fresh 4.35.0 compilation and headline review are pending.

The target is [Section 10 of arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1#page=27),
with the author's finite-volume `RV[n]` and `VF[n]` scope. The two legacy
proof files and the scaffold remain historical material.

| Paper target | Current scope |
| --- | --- |
| Definitions 10.1 and 10.3 | The positive-degree RV and Gamma form, object and essential-map data are checked. `EssentialVFMap` has a same-base definable bijection between subsets with VF-small complements, and the two measure-preservation predicates use its actual mixed VF Jacobian. The full categories, degree-zero assembly and category laws are open. |
| Remark 10.2 | The almost-everywhere equivalence and inverse on VF morphism classes are open. |
| Theorem 10.4 | Open. The legacy lemma assumes the existence of the desired lifted object. |
| Theorem 10.5 | The positive-degree [RV-valued](RVVolumeRepresentative.lean) and [Gamma-valued](GammaVolumeLift.lean) cases both pass compilation, type and axiom review, and the library import check. Each gives an essential bijection between the full lifts, follows the original label isomorphism at every source point, and satisfies the measure equation pointwise for the restricted map. |
| Corollary 10.6 | Open. |

Both statements use the released ACVF language, the paper's
pure-characteristic-zero setting through `BaseContext`, and the explicit
`VFGammaGeneratedBase` condition on the original parameter base. Both
volume maps are finite-to-one. The essential RV isomorphism is between
the parts whose volume tuples have no absorbing coordinate. The VF
representative has complements of dimension strictly below the degree
`k + 1` in the full source and target lifts. Its measure equation uses
the determinant on its own fixed-label VF chart.

The RV form takes values in nonzero RV. Its input isomorphism satisfies
both the pointwise Gamma condition and the actual Section 9 RV Jacobian
condition outside a definable RV-small set. The only external premise is
the authorized `FiniteHenselianExtensionReference`. It supplies
henselianity of a finite extension and equality of residue and field
degrees for an unchanged value group in residue characteristic zero.
The Section 9 adapter constructs the graph-field input to 9.16 from
this premise.

The Gamma form is a definable map into the actual Gamma imaginary,
presented by all nonzero RV codes. Its input isomorphism satisfies the
pointwise Gamma condition. Its proof uses the checked weighted lift and
the definable product-value test, with no external mathematical premise.
Both cases use [EssentialVFMap.lean](EssentialVFMap.lean) to transfer
the Jacobian across a restriction to the complement of the closure of
the exceptional VF projection.

## Verification

`Section10.Library` is the active entry point of the `Section10` Lake
target. Fresh pinned `lake env` source checks ran
`lean -j 1 -DElab.async=false -o …` on `EssentialVFMap.lean`,
`RVVolumeRepresentative.lean`, `GammaVolumeLift.lean` and
`Library.lean`. All four exited 0. The library imported both theorem
modules and printed the full types and axioms for the two Theorem 10.5
statements, their restriction and Gamma locus helpers, and the earlier
almost-everywhere RV theorem. Each axiom list is exactly
`[propext, Classical.choice, Quot.sound]`. The type and source review
checked the two small complements, same-base bijection, original label
graph, the pointwise volume laws, and the explicit hypotheses above.

The checks used Lean 4.33.1 (compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and ACVF-QE
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`. Linux recovered briefly
and the proofs were checked in an isolated Windows Lake project with
the same pins after further Linux timeouts. The Mathlib umbrella
artifact matches the pinned Linux cache hash. All 513 restored project
providers matched the earlier source and artifact records. The
already source-checked Linux builds of `RVVolumeLift.lean` and
`WeightedJacobianLocus.lean` were reused with matching fingerprints.

The local evidence is under `.scratch/section10/windows/` in
`Library.log` (full type and axiom output), the individual compiler logs
and exit-code files, `provider-check-final.log` and
`final-fingerprints.sha256`. The earlier Linux proof receipts are under
`.scratch/section10/` in `RVVolumeLift.log` and
`WeightedJacobianLocus.log`, with their respective exit-code files.

See [handoff](HANDOFF.md) for the precise next step and
[reuse survey](REUSE-SURVEY.md) for the source audit.
