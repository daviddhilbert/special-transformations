# Section 8 reuse survey

November 6, 2026. Initial scope: Lemma 8.1, its unary and polydisc
prerequisites, and interfaces needed next for 8.2. Earlier-section proofs
are used through their existing interfaces; no new reference hypothesis
or external code is introduced.

| Candidate | Comparison and decision |
| --- | --- |
| [Yin, §8](https://arxiv.org/pdf/1006.2467v1#page=19) | The proof of 8.1 reduces to projections and fibres; no §7 lifting theorem is used. Follow this proof in the released language. Use the pairwise condition on distinct points, as in the proof. |
| `Section3/OpenBallCodes.lean`, `OpenBallCenters.lean` | Use `OpenBallCodes.rawBall`, `ball_eq_open`, `membership_raw_definable`, and `rawBall_normalize` for actual sorted open-ball membership and normalization. The first two arguments are a centre and a VF representative of a finite radius. |
| `Section3/RootFreeConstancy.lean`, `ValuedNeighbourhood.lean` | Reuse `finite_definable_obstacles` from the checked unary QE development: membership is constant on balls avoiding a finite obstacle set. Shrinking around a point outside that set supplies the C-minimality step. `infinite_valued_neighbourhood` supplies infinitude of those balls. These avoid rebuilding unary C-minimality or the ball combinatorics. |
| `Section4/PolydiscLocal.lean`, `FullDimension.lean` | Reuse `ValuedPolydisc`, its neighbourhood proof, and `exists_nonzero_ball_subset`; the uniform box is a special case with all step values equal. The checked `lemma_4_6` and `independent_definable_contains_polydisc` are candidates for the 8.2 dimension argument. The older `Sec8Points.lean` is an obsolete §4 attempt. |
| `Section8/Sec8ValCons.lean`, `Sec8AlmostCont.lean`, `Sec8Top.lean` | Historical proof ideas for 8.3, 8.6, 8.7 and 8.9. The old `ValLayer` introduces a second valuation interface. The continuity wrapper assumes the regularity, definability and closure steps. Do not import these files or count their conditional headlines as paper proofs. |
| Pinned Mathlib, `Mathlib/ModelTheory/Definability.lean` and `Mathlib/Topology/Algebra/Valued/ValuedField.lean` | Use finite tuple projection, precomposition with definable maps, and the valued topology. Mathlib supplies no ACVF-specific dimension or local constancy premise for this proof. The pinned tree is Apache-2.0 at `0df444a360eaa60ab8c11dca51a86af692955474`. |

The earlier local proofs are in this MIT project, using the pinned ACVF-QE
package at `f3ef4ee679f921079aa8f742a2807a9cc724d2d6` with its existing
notices. See Sections 3 and 4 status records for their source and audit
scope. No code from another project is ported.

External searches used “C-minimal / C-minimality”, “definable discrete finite”,
“algebraically closed valued field definable set” and “valued topology
open ball” with Lean, plus focused Mathlib pull-request searches. The
current upstream Mathlib search found generic topology, set and valuation
material; the saved catalog tree at `805bbc496804387c2c87f9773b149ddd3a5286d2`
is a source snapshot, not the dependency used. The prior catalog snapshots
in `.scratch/catalog-audit/` cover Lean Pool
(`de237ae89555e2abebcd8e7ca91058acaee4fe45`), Tau Ceti
(`e8758b7b2f82b9b1c3f33b992ab8f499b510240f`), the community intentions
registry (`9a41615eee8393237d4ee801df8ac8bc5ab8e4e2`) and Reservoir
(`a5774ea3b51fef4a496f35c791cfa660c914454f`). The relevant files concern
valuation algebra or first-order infrastructure; they do not supply this
paper lemma. Indexed Palomar, Formalpedia and TheoremSearch coverage is
partial, including the saved ACVF search results and current discovery
queries. A reusable formalization of 8.1 was not found in these searches.
Repeat the search for the slope and regularity prerequisites before
implementing them.

The focused 8.3 search compared valuation estimates, dominant monomials,
and ordered-group semilinearity in Mathlib and the indexed Lean literature.
The local proof of polynomial RV constancy in `Section3/PolynomialLocal.lean`
and pinned Mathlib's `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`,
`eval_divByMonic_pow_rootMultiplicity_ne_zero`, and
`eval_divByMonic_eq_trailingCoeff_comp` give a direct route to the
polynomial germ. Mathlib's real or complex estimates at infinity have a
different topology and limit. The discrete valuation field formalizations
address rank-one discrete valuations. This step uses the same valuation
codomain as Section 4 and has no discreteness or rank assumption.

For the unary graph, `Section4/PolynomialCover.lean` gives a finite
polynomial cover after the Section 4 independent-point theorem rules out
a generic graph point. `Section3/TupleCompactness.lean` then gives a finite
cover by first-order polynomial shapes. The candidate value law uses a
single punctured germ from `Section3/GammaThresholdGeometry.lean` and
the clopen-ball results in Mathlib. For choosing the radius, the same
Section 3 module gives finite thresholds and a canonical endpoint on the
actual Gamma carrier with an arbitrary Gamma base. `GammaRVSeparation`
and `Section4/GammaMultiplicationSyntax.lean` supply first-order syntax
for the endpoint and for multiplication of Gamma values.

For 8.4, the repository's pinned `ImmediateRVTransport` treats
transport across an immediate valued extension. `ValuedSlopeIntegrality`
uses the value-group part of immediacy and invariance of the valuation
on the algebraic closure under automorphisms over a henselian field.
`ImmediateHenselianExtension` states these inputs explicitly.
[Engler–Prestel, *Valued Fields*](https://link.springer.com/book/10.1007/3-540-30035-X),
Theorems 5.2.2 and 5.2.5 for the henselization and its immediacy, and
Theorem 4.1.3 for uniqueness of the extended valuation.

The polynomial and ordered-group steps use pinned Mathlib.
The valued-language singleton transfer uses the released valued-field
QE bridge in `Section3/AlgebraicSubfieldModel.lean`, together with
Mathlib's fixed-field theorem. The new-scale construction uses
`Saturated.definable_finite_subcover` over the finite VF presentation
of the graph. For 8.5 the bounded angular ratio uses the checked
`lemma_3_17` in `Section3/SmallFamilyConstancy.lean`. The pairwise
law uses the complete RV witness fibre, which lets a fixed witness
be used throughout one smaller ball.

The later search found general definable-set operations in Mathlib and
formalizations of discrete valuation rings and local fields. Their
rank-one local-field results do not supply generic continuity or RV
fibre constancy in ACVF. For 8.7, reuse the actual valuation topology
and `Section4/FullDimension.lean` to compare the exceptional locus and
its closure. The direct proof at independent inputs uses
`exists_independent_of_contains_box` from Section 4 to choose a centre
inside the output ball, the `tupleField_eq_adjoin` bridge, and Mathlib's
`AlgebraicIndependent.sumElim_iff` and `extendScalars`. Naming the RV
radius does not enlarge the VF parameter field. For 8.9, reuse the
checked `Section4/MultivariateLocal.lean`
lemmas for VF equations and RV terms. Restrict the well-sorted VF
subterms to the VF variables to make those neighbourhoods uniform in
the RV variables. `Section3/RVFibreConstancy.lean` gives related unary
uniformity.
