# Errata and deviations

This record compares the formalization with Yimu Yin, *Special transformations
in algebraically closed valued fields*, arXiv:1006.2467v1. Locations use that
version's definition and theorem numbers. An erratum records a defect in the
printed assertion or language specification; a deviation records an adopted
convention, scope, equivalent reformulation or proof supplement. A supplied
argument for a true assertion is treated as a deviation, rather than an erratum.
Counts are grouped entries, not the number of affected assertions. HK,
*Integration in valued fields*, arXiv:math/0510133v3, is a comparison reference
for the measured-zero convention; its theorems are not assumed as Lean inputs.

| Source | Errata | Deviations |
| --- | ---: | ---: |
| Yin, arXiv:1006.2467v1 | 6 | 7 |

## Yin: Special transformations

### Errata

1. **Section 2, immediately before Convention 2.5: RV inversion.** The printed
   language omits inverse function symbols. The adopted QE language names RV
   inversion, totalized at the one absorbing element, and leaves VF inversion
   unnamed. Theorem 2.3 concerns this corrected language. Naming the definable
   inverse does not change later same-base definable sets or acl/dcl. See the
   [language record](../LANGUAGE-ERRATA.md) and
   [pinned QE interface](../SpecialTransformations.lean). This is a language
   correction, not merely a repair of a Lean transcription.

2. **Definition 2.2(6): kernel of the RV homomorphism.** The quotient map on
   nonzero elements must have kernel `1 + 𝔪`. Surjectivity and a valuation alone
   do not determine that kernel: squaring the usual RV map in pure
   characteristic zero gives a larger kernel. The released theory's
   `Axioms.rvEqLink` imposes the leading-term equality, including its kernel
   instance. See the [kernel record](../LANGUAGE-ERRATA.md#kernel-of-the-rv-map-in-definition-22)
   and [pinned language source](https://github.com/daviddhilbert/ACVF-QE/blob/173708265d7959e031bf9552ee884501fc21f2cb/Proofs/Enc.lean).
   The squaring counterexample is a mathematical explanation, not a separately
   claimed Lean counterexample theorem.

3. **Remark 3.19: multiplicative subgroup classification.** The entire remark
   is retracted. The definable group `{1,-1}` refutes the unrestricted
   classification. `Remark319Audit.rawSigns_not_ball` and
   `rawSigns_not_valuation_units` in
   [Remark319Audit.lean](../Section3/Remark319Audit.lean) certify the obstruction
   in the stated pure-characteristic-zero scope. No infinite-group replacement
   is asserted; the remark is excluded, not counted as proved. See the
   [retraction and dependency review](../Section3/RETRACTIONS.md).

4. **Lemmas 9.11–9.12: pointwise partial-Jacobian assertions.** The everywhere
   claims require correction. A discontinuous definable focus can prevent the
   Jacobian of a special bijection from existing at a point. Defined partial
   derivatives alone do not give the pointwise chain rule. The replacements
   use full differentiability on actual fixed-label charts, or the stated
   almost-everywhere results with a finite-to-one first map for generic
   composition. Zero arity is pointwise with determinant one. The concrete
   counterexamples are explained mathematically in
   [DIFFERENTIATION-ERRATA.md](../Section9/DIFFERENTIATION-ERRATA.md), not asserted
   there as Lean counterexample theorems. The corrected results are
   `lemma_9_11_ae` in [SpecialJacobianAE.lean](../Section9/SpecialJacobianAE.lean),
   `mixedVFJacobian_comp_of_full_derivative` in
   [MixedJacobian.lean](../Section9/MixedJacobian.lean), and `lemma_9_12_ae` in
   [MixedDifferentiationAE.lean](../Section9/MixedDifferentiationAE.lean).

5. **After Definition 9.14: pointwise RV chain rule.** Finite volume fibres
   do not imply the pointwise rule for the pairwise volume correspondences.
   The three-branch residue-field example in
   [RV-CHAIN-ERRATUM.md](../Section9/RV-CHAIN-ERRATUM.md) has factor Jacobians one
   and composition Jacobian two at the distinguished label. This example is
   documented mathematically. The checked replacement
   `rvJacobian_chain_ae_finite_volume` in
   [GenericRVJacobianChain.lean](../Section9/GenericRVJacobianChain.lean) uses a
   same-base RV-small exceptional set and one common source label; its
   zero-arity counterpart is pointwise. The Gamma cancellation rule remains
   pointwise.

6. **Lemma 9.15: unrestricted Gamma comparison.** This clause is withdrawn.
   The rational branch bijection of a punctured maximal-ideal square in
   [LEMMA-9.15.md](../Section9/LEMMA-9.15.md) gives the valued-field obstruction.
   `monomialPermutation_bijOn_and_changes_sum` in
   [GammaObstruction.lean](../Section9/GammaObstruction.lean) checks the
   underlying ordered-group permutation and changed sum of valuations; it is
   not a Lean formalization of every valued-field derivative in the example.
   The finite-volume RV comparison remains in
   [PaperLiftComparison.lean](../Section9/PaperLiftComparison.lean). The distinct
   constant-finite-Jacobian Gamma descent theorem is in
   [GammaPolydiscDescent.lean](../Section9/GammaPolydiscDescent.lean), with its
   explicit reference premise.

### Deviations

1. **Definition 2.4: guarded rational VF factors.** The normal form uses
   rational functions with explicit pole guards in place of a strict
   polynomial-only target. This is an adopted scope choice; no Lean
   counterexample to the polynomial-only version is claimed. The same-base,
   model-uniform result is
   `GuardedRVNormalForm.definition_2_4_guarded_rational_normal_form` in
   [GuardedRationalNormalForm.lean](../Section3/GuardedRationalNormalForm.lean).
   See [NORMAL-FORM-NOTE.md](../Section3/NORMAL-FORM-NOTE.md).

2. **Section 2 ball conventions: proper open discs have finite radius.** The
   radius type is `Balls.OpenRadius`, the order dual of the units of the
   multiplicative value group with zero. A radius at infinity gives a
   singleton closed disc, not a proper open disc. The finite-radius
   inequalities and later preparation statements are unchanged. See
   [OPEN-DISC-RADIUS-NOTE.md](../Section3/OPEN-DISC-RADIUS-NOTE.md) and
   [BallGeometry.lean](../Section3/BallGeometry.lean).

3. **Definition 9.1: full cover and local boundedness.** The covering clause
   uses the union over all candidate centers; a permitted subcover implies
   this full cover, and conversely the full set itself is an admissible
   choice. Minimality means no proper subset is a limit set. No global range
   bound is inserted. A finite affine limit set gives local boundedness;
   infinity-coordinate neighborhoods do not. See
   [LIMIT-SET-ERRATUM.md](../Section9/LIMIT-SET-ERRATUM.md), `IsLimitSet`,
   `IsMinimalLimitSet`, and `IsLimitSet.mono` in
   [Limits.lean](../Section9/Limits.lean). This equivalent covering
   reformulation is not counted as a false-assertion erratum.

4. **Definitions 10.1 and 10.3: weighted degree zero.** Replace the printed
   ordinary zero-category exceptions by actual same-base nonzero RV forms,
   or actual Gamma forms, on the ordinary finite-volume zero objects.
   Isomorphisms preserve the exact weight at every point. The VF category
   retains arbitrary ordinary zero-dimensional mixed presentations. No
   nonempty zero locus is discarded; the empty-coordinate determinant is
   one. Ordinary zero categories remain separate, and their isomorphisms
   recover the neutral-form subcategories. This adopts the all-degree
   measured convention of HK Definitions 8.10/8.13 within this repository's
   existing scope; it does not assume HK's theorems. The six concrete zero
   versions of 10.4–10.6 are in
   [WeightedZeroResults.lean](../Section10/WeightedZeroResults.lean).
   [WeightedZero.lean](../Section10/WeightedZero.lean) gives the exact lift,
   [WeightedZeroUnit.lean](../Section10/WeightedZeroUnit.lean) the neutral
   comparisons, and
   [WeightedFormProducts.lean](../Section10/WeightedFormProducts.lean) the
   pointwise product-density formulas. See the
   [measured-zero record](../Section10/WEIGHTED-ZERO-ERRATUM.md).

5. **Theorem-specific scope.** The agreed library excludes C-minimality for
   trivial valuations, the whole-field ball case of Lemma 8.4, and the broader
   ambient categories in Sections 9–10. `Section3.theorem_2_8_c_minimal` is
   proved for nontrivially valued models, via Theorem 2.3; the author
   confirmed on November 18, 2026 that the trivially valued case of
   Theorem 2.8 is out of scope and will not be formalized. The later results use finite-volume
   `RV[n]`/`VF[n]`, retaining their actual parameter, characteristic,
   saturation, homogeneity and generation assumptions. The implementation
   retains one absorbing RV element, `rv(0)`, and reverses the paper's
   additive value order when using Mathlib's multiplicative valuation.
   No second absorbing point is introduced. See
   [Section 3 status](../Section3/STATUS.md),
   [Section 8 status](../Section8/STATUS.md), and
   [RV-CATEGORY-AUDIT.md](../Section9/RV-CATEGORY-AUDIT.md).

   The provider audit of November 18, 2026 recorded these statement-level
   scope points. They change no Lean statement and assert no new defect in
   the paper:
   - Theorems 5.4/5.5 with named Gamma parameters were previously stated
     only with three discharged inputs as parameters
     (`Section5/GammaExistence.lean`). The input-free
     `Section5.Paper.theorem_5_4_gamma`, `theorem_5_5_gamma` and
     `theorem_5_5_finite_gamma` in
     [GammaPaper.lean](../Section5/GammaPaper.lean) assume saturation, a
     small real base and the paper's VF/Gamma-generated base; the
     `*_of_fieldBase` forms assume instead that the VF part of the real base
     is a field.
   - `Section4.Paper.lemma_4_13` is the discharged form of Lemma 4.13 in
     the released model; the `RVExchangeInput` form remains for general
     structures.
   - Some statements carry hypotheses that are stronger than, or unused
     by, the proof: `theorem_10_4_*` takes `VFGammaGeneratedBase`, which its
     proof does not use; `theorem_7_6` assumes `VFGammaGeneratedBase`; the
     Lemma 8.6 forms take a named `δ > 1`. `lemma_8_4_partial` omits the
     definability of `c` and `r`; the named-Gamma form linked from the
     blueprint retains it.
   - `Section3.GammaParameters.commonRealNames` and
     `GammaCodes.representative` choose RV representatives for use inside
     proofs only; no theorem here assumes them to lie in a base. The
     `SpecialTransformationsGammaQE` target keeps the
     `DiamondIntegral.Section5.GammaQE` names for its consumer.
   See the [README notes on statements](../README.md#notes-on-statements).

6. **Theorem 2.3: separate valuation cases.** The nontrivial RV theory and
   the canonical trivially valued theory have separate QE statements. No
   uniform QE theorem for their union is claimed. The trivial canonical case
   reduces to ACF in the pinned QE dependency. See
   [LANGUAGE-ERRATA.md](../LANGUAGE-ERRATA.md#trivial-valuations-and-qe).

7. **Reference hypotheses and proof supplements.** The two authorized
   Engler–Prestel inputs remain explicit: the henselization input used in
   Section 8, and `FiniteHenselianExtensionReference` for the affected
   positive-degree Section 9/10 results. Attributed Stacks results are
   supplied by checked imports rather than additional asserted axioms.
   The new zero-degree results introduce no such reference input and assume
   no definable Gamma-to-RV section. Gamma Theorem 9.16
   (`GammaLift.gamma_theorem_9_16_finite_volume` in
   [GammaPrescribedVolumeLift.lean](../Section9/GammaPrescribedVolumeLift.lean))
   takes the same henselized graph-field data as the real-parameter
   positive-arity Theorem 9.16; it adds no further reference input. See
   [Section 8 status](../Section8/STATUS.md),
   [Section 9 status](../Section9/STATUS.md), and
   [Section 10 status](../Section10/STATUS.md).

## Proof routes and scope

The formal proof supplies same-base definable constructions, genuine
small-parameter model-theoretic hypotheses, and actual chart derivatives.
It reuses the pinned ACVF-QE language and theory, local checked geometry,
and attributed Stacks imports. The weighted zero proof transports the supplied
form through the ordinary finite lift presentation, using the definable
inverse of the zero label projection. It descends through weighted scissors
and retains both densities under products. No external measured integration
theorem supplies these conclusions.

RES, pure value-group measured categories, tensor decompositions and the
sequel's integration kernel, normalization and function integration are
outside this release's scope. HK arXiv:math/0510133v3 is used only for the
stated convention comparison. Detailed certificates and hypotheses remain
in the linked section records; build and axiom audits do not replace their
mathematical scope statements.
