# Reuse candidates and their limits

All paths below are relative to `Section3/` unless stated otherwise. This is
a source-inspection map, not a fresh compiler audit. The code was moved
unchanged. Existing headers claiming "proved" or "green" may describe an old
encoding, a conditional theorem, or a superseded statement.

| Files | Useful content / limitation |
| --- | --- |
| `Sec3_frozen.lean`, `Sec3_sat.lean`, `Sec3_draft.lean` | Parameter and target vocabularies, plus deliberate placeholders. Historical transcriptions need review; do not bulk-import them as established theorems. |
| `Sec3Infra.lean` | Sorted definability, Boolean combinations, rv-fibres, Gamma vocabulary, and conditional algebraicity descent. |
| `AclFibres.lean`, `UniformCover.lean`, `Sec3Count.lean`, `Sec3Corrected.lean` | Nonempty-family issue, uniform-cover argument and bounded-finiteness formulas. The general compactness step remains to be closed. |
| `M3AclField.lean` | Field closure of the VF part of acl. Does not alone prove Corollary 3.14. |
| `Exchange.lean` | VF/RV closure vocabulary and reductions of exchange to definable-relation finiteness; do not assume the reduction's premise is proved. |
| `AlgIndImag.lean`, `AclZero.lean`, `Sec3Fibre.lean` | Closure-size argument, zero-fibre treatment and geometric fibre-size proof; exchange is still explicit in the key final interface. |
| `Sec3Average.lean` | Valuation-average argument and residue-characteristic safeguards; separately derive RV nonconstancy and check the original paper statement. |
| `M8FinImage.lean`, `M8ProjectRV.lean`, `M8ProjectRVN.lean` | Finite RV images/coding candidates and tuple constructions; inspect extra named parameters versus definability over the original base. |
| `BallSec3.lean`, `M7Centres.lean` | Ball geometry and diagnostics for an excessively strong center-set transcription; arbitrary center choice is not definable choice. |
| `InfRVDefGam.lean` | Gamma-fibre definability/finiteness argument with uniform-bound and C-minimality hypotheses still explicit. |
| `Sec3FunIntoPower.lean` | Set-theoretic quotient/powerset descent and uniqueness, useful for Notation 3.16; integrate actual definability. |
| `Sec3Tail.lean`, `Sec3TailGamma.lean` | Statements and partial reductions for 3.17--3.19; constant-family special cases and choice-based reductions do not close the general results. |
| `Balls.lean` | Earlier Section 2 ball geometry. Its extra `RV0` wrapper and C-minimality placeholder need auditing against the released encoding; do not import a competing RV language. |
| `LegacyScaffold/` | Earlier Basic/Language/Definable stubs, preserved as history. |

Shared candidates retained in `../Shared/`: `SubstVar.lean`, `ExSortedG.lean`,
`ParamBridgeRelabel.lean`, `ParamBridgeShift.lean`, `SubstParam.lean`,
`JunkTrue.lean` and `MulNormalForm.lean`. `Enc`, `RVCalc`, `VFField` and
`VFValued` are supplied by the pinned ACVF-QE dependency; their duplicate
local copies and the rest of the old QE campaign have been removed.
`../Section4/Compose.lean` supplies a candidate definable-function composition
layer; using shared infrastructure does not expand the next task to Section 4.
`../Archive/Milestone0/Saturation.lean` is the historical `Sat` interface.

Use `../Archive/MOVE-INDEX.json` to resolve old `QE/...` and `Milestone0/...`
references in comments. `../Archive/inspect_legacy.py` can list source imports,
placeholder counts and dependency order; none of these is a proof certificate.
