# Independent automated release-record review

Reviewed proof commit `d7d74197031665b4c1e9ea4486c1898ff32f2d50` and the uncommitted
`docs/ERRATA-AND-DEVIATIONS.md` with SHA-256
`2e1d177a28b3d6f2f54a43f1e2b084a7840869dc53480b7448a3b16a2a5e8004`.
The Lean sources remained unchanged during this review. This is an independent
source, statement, scope and release-record review; it is not an exhaustive
semantic review of every theorem in the project or a replacement for the
separate full build and axiom audit.

## Primary-source check

I read the actual pinned-version primary text, rather than inferring it from
repository notes: [Yin, arXiv:1006.2467v1](https://arxiv.org/html/1006.2467v1)
and [Hrushovski–Kazhdan, arXiv:math/0510133v3](https://arxiv.org/html/math/0510133v3).
For Yin I checked Definitions 2.1–2.6, Remark 3.19, the Section 9 limit and
Jacobian definitions, Lemmas 9.11–9.15 and the Section 10 definitions. I checked
the surrounding standing hypotheses, particularly the removal of the full
RV-dimension assumption before Lemma 9.15. For HK I checked Definitions 8.10
and 8.13 and their surrounding dimension and measure conventions.

## Errata verdicts

| Entry | Source check | Verdict and independent obstruction check |
| --- | --- | --- |
| E1 RV inversion | Immediately before Convention 2.5, inverse symbols are omitted. | **CONFIRMED.** This is the existing author-approved correction. The pinned encoding names RV inversion and leaves VF inversion unnamed. The record properly separates the corrected QE language from the unchanged same-base definable sets. |
| E2 RV kernel | Definition 2.2(6) specifies a surjective homomorphism, but omits the kernel link. | **CONFIRMED.** Squaring the usual RV map is still surjective; its induced valuation is doubled and has the same valuation ring and maximal ideal. Its kernel additionally contains −1 in residue characteristic zero. `Axioms.rvEqLink` supplies the missing leading-term relation. The record correctly identifies the counterexample as mathematical, not a separate Lean theorem. |
| E3 subgroup remark | Remark 3.19 has no infinitude qualification. | **CONFIRMED.** The definable group {1,−1} is neither a ball nor the valuation units. Any ball containing both contains their midpoint, zero; the valuation units also contain 3. The linked `rawSigns_not_ball` and `rawSigns_not_valuation_units` prove the claimed obstructions. Retraction, without an unproved infinite-group replacement, is appropriate. |
| E4 partial Jacobians | Lemmas 9.11–9.12 include pointwise claims. | **CONFIRMED.** For F(x,y)=(x,x+y) and G equal to doubling on the diagonal and the identity elsewhere, partial determinants at zero are 1 and 1 but that of G∘F is 2. The documented discontinuous focus similarly obstructs a pointwise special-bijection Jacobian. Full differentiability and the stated generic replacements address the actual defects. |
| E5 RV chain | The assertion after Definition 9.14 is pointwise. | **CONFIRMED.** Recomputing the three labelled branches gives the relevant pairwise tangent slopes 1, 1 and 2. Pairwise volume correspondences forget different branches, so finite fibres do not rescue the pointwise identity. The replacement retains one common label and an RV-small exceptional set; the Gamma cancellation identity is pointwise. |
| E6 Gamma comparison | Lemma 9.15 includes the unrestricted Gamma clause. | **CONFIRMED.** Recomputing all five rational branches gives a bijection on the punctured maximal-ideal square with nonzero determinant valuation off the axes. Translation places it in a fixed RV polydisc. The earlier full RV-dimension restriction has been removed in the source and cannot rescue this clause. The Lean certificate checks the ordered-group permutation and changed sum, exactly as the record says. |

The six classifications are justified. The record consistently distinguishes
checked replacements and Lean obstructions from mathematically documented
counterexamples that have not themselves been fully formalized.

## Deviations

| Entry | Review finding |
| --- | --- |
| D1 guarded rational normal form | Accurate adopted scope, with explicit guards and no claim of a Lean refutation of the polynomial-only target. The named headline declaration exists. |
| D2 open radii | Accurate: `Balls.OpenRadius` uses the order dual of the nonzero multiplicative value group. The infinity-radius singleton is handled as a closed disc. |
| D3 limits | Accurate equivalent covering reformulation. The definition and `IsLimitSet.mono` support enlarging the center family; proper-subset minimality and local boundedness do not assert a global bound. |
| D4 weighted zero | Accurate convention change, rather than an alleged false theorem in Yin. HK's measured definitions have no special degree-zero exception. The repository adopts that convention within its stated finite-volume scope. See the code checks below. |
| D5 scope and presentation | Accurate after the final addition recording the established one-absorbing-point presentation and reversed multiplicative valuation order. Yin's printed language lists separate zero/infinity symbols; the release record now presents the implementation convention as an adopted presentation, without asserting a new source defect or reopening the authorized encoding. |
| D6 separate QE cases | Accurate: the nontrivial theory and canonical trivial case are separate, and no QE theorem for their union is claimed. |
| D7 reference inputs | Accurate when the two inputs are understood as two explicit reference packages. The Section 8 package contains its stated henselization/immediacy properties, and the later package remains explicit on the affected positive-degree results. The new zero results add neither package nor a Gamma-to-RV section. |

## Weighted-zero implementation and statement checks

I read `WeightedZero.lean`, `WeightedZeroRepresentation.lean`,
`WeightedZeroResults.lean`, `WeightedZeroScissors.lean`,
`WeightedZeroUnit.lean` and `WeightedFormProducts.lean`, together with their
ordinary-category and volume-scale interfaces. I also inspected the available
full-type output and the linked corrected Section 9 declarations.

- `MeasuredVFZero` ranges over the ordinary `VFFiniteObject ... 0` family,
  retaining arbitrary mixed ambient presentations. It is not restricted to
  presentations with no VF coordinates. `MeasuredRVZero` uses the ordinary
  finite-volume RV zero objects.
- Forms are actual same-base definable maps. RV weights are nonzero RV values;
  Gamma weights are values in the actual Gamma carrier. The Gamma equality
  lemma compares Gamma values, not representatives or RV classes.
- `ExactMap` requires a definable bijection and pointwise equality of the
  supplied weights. No nonempty locus is discarded. The zero lift labels are
  bijective; `liftMap` is the actual transported map, its label identity is
  checked, and `liftMap_measure` supplies determinant one and the weight law.
- The neutral-form constructions preserve the original underlying objects.
  The four `iso_iff` comparisons and four completeness results justify the
  record's statement about ordinary **isomorphisms**. They do not claim an
  equivalence with an ordinary category containing arbitrary noninvertible
  maps.
- The six RV/Gamma zero versions of 10.4–10.6 are present. Representation
  transports the existing ordinary zero presentation and the given form;
  scissors use the actual restricted forms and the checked representation
  result. Their parameter, saturation and base-context hypotheses remain
  visible. No missing representation or descent obligation is disguised as a
  hypothesis.
- Product formulas retain both pointwise densities. Gamma multiplication is
  supplied by the definable quotient multiplication construction, without
  choosing a definable Gamma-to-RV section. The record does not overclaim a
  graded semiring theorem.

I checked the named Section 9 corrected theorem interfaces: the generic
composition theorem retains the finite-fibre first-map hypothesis, positive
arity and its actual Jacobian/exceptional-set data; the RV chain replacement
retains the common source label and finite-volume assumptions. The distinct
Gamma descent premise is explicitly acknowledged.

## Link and publication checks

All 33 relative file links in the release record resolve. All linked Lean
declaration names were located, including the two `Remark319Audit` obstructions,
the corrected Jacobian results, `monomialPermutation_bijOn_and_changes_sum`,
and the normal-form declaration. The pinned external encoding link identifies
the actual ACVF-QE revision. The record has six grouped errata and seven grouped
deviations, matching its count table. It contains no private absolute paths or
unsupported MathJax macro definitions.

**Disposition: approved for inclusion in the release.** No further release-record
or Lean edits are required by this review. Final publication remains dependent
on the separate complete build, headline-type and axiom audits and
the other project-integrity checks. This approval does not certify every
project theorem's semantic correspondence to the paper.
