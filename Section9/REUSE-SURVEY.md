# Section 9 reuse survey

November 7, 2026 (America/Los_Angeles). The target is arXiv:1006.2467v1,
Section 9, with immediate attention to Lemma 9.15 and the dependence of
Theorem 9.16 on its first clause. The startup baseline is
`32d7815b7a58624a620abb9d6423721b7e094520`. Lean is pinned to 4.33.1,
Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474` and ACVF-QE to
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

| Source | Reuse decision |
| --- | --- |
| Published `Section8.GammaBalls.gammaUniformBall` and `Section3.Values.vfValueHom` | Direct inputs to `Limits.lean`. They use the actual value-group quotient and the paper's order. Only the formal VF point at infinity is new. |
| `Section9/Sec9Limits.lean` | Proof reference for the finite-point part of the limit lemmas. Its custom `NAdvf` and abstract definability do not match the active language. Its infinity ball uses the opposite inequality from the complement of the closed ball in the paper. Its finite-limit bound leaves C-minimality and definability as hypotheses. |
| `Section9/Sec9AE.lean` and `LegacyScaffold/` | Historical candidates only. Use the published Section 8 exceptional-set definitions rather than duplicating them. |
| Published Section 3 closure results, Section 4 dimensions, and `Section8.UnaryPolynomial` | The VF algebraicity and dimension calculations give the graph dimension. The unary file shows how to extract polynomial constraints from actual definable graphs using QE. It needs a multivariate extension for the implicit branch step. |
| Published `Section7.MultivariateHensel.multivariate_simpleRoot_lift`, `Section7.ValuationHenselian.valuationRing_henselian`, and `Section7.ResidueConstructibility` | Direct candidates for the Hensel branch and residue correspondence. The existing root-lifting theorem supplies existence and uniqueness in a specified residue class. It does not establish that a given lifted graph has such a presentation or identify its derivative. Section 7's reuse survey records the Tau Ceti etale lifting port at catalog revision `e8758b7b2f82b9b1c3f33b992ab8f499b510240f` and its Apache-2.0 license. |
| [HK, Lemmas 3.20 and 5.4–5.5 and Proposition 5.22](https://arxiv.org/pdf/math/0510133v3#page=59) | Mathematical proof references for the residue-generic type and the unary comparison. Corollary 5.23's second claim, interpreted as the ordinary determinant on a generic point of each polydisc, has the arity-two obstruction in `LEMMA-9.15.md`. No HK result is assumed as a checked Lean input. |
| [Yin, Integration in ACVF, §§2–3](https://arxiv.org/pdf/0809.0473#page=6) | Usage and proof reference. Lemma 2.33 repeats the problematic assertion, while the unary Gamma-linearity result in Lemma 3.16 has its own hypotheses. Neither is an assumed Lean input. |
| [Mathlib analytic inverse](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Inverse.html), [p-adic measures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/Measure/Basic.html), [Haar measure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar/Basic.html) | Upstream candidates for the separate mixed-characteristic descent route. The norms and completeness in the inverse theorem are appropriate for a finite extension of `Q_p`. They do not give the topology or differentiability of an arbitrary-rank ACVF. Exact pinned local-field interfaces and the change-of-variables lemma still need inspection. |
| Pinned `Mathlib/MeasureTheory/Function/Jacobian.lean` and `RingTheory/Polynomial/GaussNorm.lean` | The inspected Haar Jacobian theorem uses real vector spaces, and the Gauss norm uses real values. Neither directly applies to its corresponding Section 9 task. For the arbitrary-rank Gauss calculation, use the published Section 7 polynomial normalization and the no-cancellation argument from residue independence. |

Searches used `ACVF`, `motivic integration`, `Jacobian`, `residue`,
`implicit derivative`, `henselian`, `Gauss valuation`, and
`unramified finite extension`, including upstream Mathlib and PR search,
Reservoir, Lean Pool, Palomar, Tau Ceti, the Lean community registry,
TheoremSearch and Formalpedia. The public catalog pages and indexed
results were accessible. Search coverage is incomplete where the catalog
requires interactive search. No checked proof of the corrected
comparison or descent statement was found in these searches. The
[monogenic extensions project](https://github.com/uw-math-ai/monogenic-extensions)
has a relevant standard-étale result, but proving that the valued
extension has the requisite integral presentation remains necessary.
Its exact revision and proof status need review if a port becomes useful.
No external code was copied into Section 9.

The November 7 continuation targets the intrinsic coarsening argument.
Pinned `Mathlib/RingTheory/Valuation/ValuationSubring.lean` provides
`ValuationSubring.ofPrime`, `mapOfLE`, and `ofPrime_valuation_eq_one_iff_mem_primeCompl`.
Reuse these Apache-2.0 APIs to pass from the fine valuation to its
coarsening. The prime ideal to supply consists of the integral elements
with value at least one positive threshold from the coefficient field in
additive order. Its complement becomes the units of the localization.
The draft `GammaCoarsening.lean` implements the threshold ideal and the
primality argument. The model-theoretic realization and restriction to
the coefficient valuation still need proofs.

The limit proofs reuse the unary definable germ theorem in
`Section8.UnaryGerm`, the ball code and raw projection interfaces in
Sections 3 and 4, and the valuation-topology neighbourhood basis in
`Section8.VFNeighbourhoods`. The finite-point arguments for 9.2–9.3 use
the ball identities directly. The bounded-chart root estimate uses
finite sums and products of valuation inequalities from pinned Mathlib.
The unary finite-fibre graph for 9.5 uses
`Section4.PolynomialCover.exists_polynomial_vanishing_on_selection`.
The polydisc argument adapts the one in
`Section8.UnaryPolynomial.unary_graph_polynomial_relation`, replacing
the singleton fibre contradiction by infinitude of an open VF side.
This produces a polynomial over the original VF parameter field.

The weighted determinant computation for 9.16 uses the row weights and
simple-block calculations already proved in `Section7.LiftingAlgebra`
and `Section7.JacobianNormalization`. The extended local-system and
correspondence witnesses retain these values and keep the original Section 7
theorems as projections. Their compiler checks are separate from the
global lifting theorem. The matrix reduction
uses pinned Mathlib nonsingular inverses and the residue ring map. The
Taylor estimate uses Mathlib's multivariate polynomial partial
derivative and valuation inequalities. These steps use no new external
mathematical inputs.

For generic full differentiation, reuse
`Section4.MapAlgebraicity.map_output_vf_coordinate_isAlgebraic`,
`Section4.PolydiscLocal.independent_definable_mem_nhds`, and the checked
generic continuity and RV local-constancy results from Section 8. A
simple-root equation already valid on the local graph and the
arbitrary-rank Taylor estimate suffice. The finite-to-one case of the
generic chain rule uses `Section4.VFCategories.vfDim_le_of_finite_map`
on the inverse image of the exceptional set of the second map. At
independent points, the equivalent rank argument uses the reversed finite
graph and `Section4.FiniteCorrespondence.tupleField_trdeg_mono_of_isAlgebraic`.

The Gauss step uses `MvPolynomial.as_sum`, `pderiv_monomial` and the
valuation sum bound for polynomial differentiation, and
`IntermediateField.mem_adjoin_range_iff` for quotients. For separable
derivation extension, pinned Mathlib provides
`Algebra.FormallyEtale.of_isSeparable` in
`Mathlib/RingTheory/Etale/Field.lean` and the base change isomorphism
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`. The extension and
uniqueness proofs use the latter, so they apply to the ring neighbourhoods
as well as the separable field extensions.

The November 8 standing approval covers the Stacks Project and its Lean
formalization, including
[Stacks Project, Lemma 10.155.1](https://stacks.math.columbia.edu/tag/04GN)
for étale neighbourhoods of the henselization and
[Lemma 15.125.6](https://stacks.math.columbia.edu/tag/0ASK) for henselization
of valuation rings. The [AxiomMath Stacks formalization](https://github.com/AxiomMath/Stacks)
at `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` uses Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. In that revision, `04GN` is
`IsLocalRing.exists_henselization`, and `0ASK` is
`isWeaklyUnramified_henselization_and_strictHenselization`. The three-module
source closure for `04GN` compiled in scratch with the project's pin.
Its full type and axiom audit passed, as did the adapter from the
filtered-colimit presentation to Section 9's elementwise étale cover.
The port removes an unused import unavailable under the pin and makes the
augmentation cocone's naturality equality explicit. The dependency audit
for `0ASK` found 119 Stacks modules and 194 direct Mathlib imports in their
transitive Stacks closure. The construction instead proves the
valuation-ring step from the filtered étale presentation, using the local
flat-ideals argument below. The scratch port has its upstream Apache-2.0
license.
The checked eleven-module source subset is copied byte for byte to
[VendoredStacks](VendoredStacks/README.md) with its upstream license.
The `Section9Stacks` Lake library keeps the original module names.

The ordinary universal property at [04GS](https://stacks.math.columbia.edu/tag/04GS)
also passed in scratch under the project pin. The adapter combines it
with `04GN` to produce an ind-étale ordinary henselization and a local
algebra map to a henselian target. The adapter's type and axiom audit
passed. Separately, `HenselizedImageAudit.lean` verifies that an injective
local map from a valuation ring into the ambient valuation ring identifies
its image with the ambient valuation ring restricted to its fraction
field. The filtered valuation-ring argument below verifies that the
ordinary henselization is a valuation ring and its local map is
injective in this setting.

The pinned upstream `Valuation/Extension/Etale.lean` separates the
valuation-ring part of `0ASK` from the surjectivity of the value-group
map and the strict henselization. For this project it is enough to port
the valuation-ring construction and the ordinary local henselization
embedding. The Gauss field has the value group of its algebraically
closed coefficient field. `exists_same_value_of_isAlgebraic` already
proves that algebraic extensions of a field with these divisible values
add no values. This avoids porting the tensor-square normality and
descent-of-associated-powers arguments for surjectivity in the general
étale case. `GaussExtensionAudit.lean` now checks the same-value result
over the Gauss field directly. The upstream local argument uses normality
to get domains. `LocalFlatValuationAudit.lean` instead obtains the domain
property from freeness of the nonzero principal ideals. The full type and
axiom audit passed for the resulting valuation-ring theorem on local,
flat, essentially finite formally unramified algebras over a valuation
ring. `AlgebraicLocalStageAudit.lean` checks algebraicity and injectivity
on each localized stage. `FilteredValuationAudit.lean` then verifies that
the ind-étale local ring is a valuation ring, algebraic over the base,
and injects into the target domain. `EmbeddedHenselizationAudit.log`
checks the embedded field and its henselian valuation ring, algebraicity,
and elementwise étale cover. `GraphReferenceAudit.log` checks the finite
graph-field assembly and the adapter to the ACVF model from the named
Engler–Prestel finite-extension input.

The residue chart argument uses the standard smooth presentation of
relative dimension zero and reducedness of a smooth algebra over a
reduced ring. The relevant Stacks tags are
[00T6](https://stacks.math.columbia.edu/tag/00T6) and
[033B](https://stacks.math.columbia.edu/tag/033B). Pinned Mathlib already
proves the needed Nullstellensatz as
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` in
`Mathlib.RingTheory.Nullstellensatz`, corresponding to
[00FV](https://stacks.math.columbia.edu/tag/00FV). The polynomial chart
uses that checked statement. `ResidueChartReducedness.lean` proves
reducedness for the specific open square system, and `VolumeChartAudit.log`
checks the chart soundness that uses it.

For the generic residue tangent, reuse
`Section4.ResiduePolynomialCover.exists_residue_polynomial_vanishing_on_selection`
and `Section4.PureFieldAlgebraicity.finite_field_definable_isAlgebraic`.
Remove repeated output factors over the fraction field of the input
polynomial ring using pinned Mathlib's `radical` and the equivalence
between squarefreeness and separability in characteristic zero.
For the lower-dimensional lift, reuse the Section 3 finite choice
gluing and the Section 7 barycentre of a finite algebraic witness in an
RV ball. The local VF head is the only new VF tuple in the algebraic
representative construction.
