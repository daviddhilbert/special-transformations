# Section 10 continuation

Follow the root workflow and [Section 3 handoff](../Section3/HANDOFF.md).
The paper target is [arXiv:1006.2467v1, §10](https://arxiv.org/pdf/1006.2467v1#page=27)
in the approved finite-volume `RV[n]` and `VF[n]` scope for both
RV-valued and Gamma-valued forms. The [Section 9 handoff](../Section9/HANDOFF.md)
records the prescribed lift and the explicit Engler–Prestel input.

The corrected measured-zero convention is implemented in
[WeightedZero.lean](WeightedZero.lean),
[WeightedZeroRepresentation.lean](WeightedZeroRepresentation.lean),
[WeightedZeroScissors.lean](WeightedZeroScissors.lean),
[WeightedZeroUnit.lean](WeightedZeroUnit.lean),
[WeightedFormProducts.lean](WeightedFormProducts.lean) and
[WeightedZeroResults.lean](WeightedZeroResults.lean). See the
[erratum](WEIGHTED-ZERO-ERRATUM.md) and current status for the scope and
verification. The local branch starts at published main `f76d100`; the
migrated original checkout and all its pre-existing edits are preserved.

Downstream interfaces (namespace `SpecialTransformations.Section10`):

- `MeasuredRVZero S d`, `MeasuredVFZero hc S d`, and the underlying
  `WeightedZero.underlying`, `form`, `domain`, `weight`. Take `d` to be
  `rvVolumeScale` or `gammaVolumeScale hc`. `WeightedZero.ExactMap` and
  `WeightedZero.iso_iff` describe total exact weight-preserving arrows.
- `ZeroForm.pullback`, `pullback_weight`, `restrict`, `restrict_weight`;
  `MeasuredRVZero.restrict` and `MeasuredVFZero.restrict` retain the same
  form. `rvZeroNeutral`, `gammaZeroNeutral`, `vfRVZeroNeutral`,
  `vfGammaZeroNeutral` supply the ordinary neutral embeddings. Their
  `_iso_iff` and `_complete` lemmas identify the neutral subcategories.
  `WeightedZero.asUnit`/`forgetUnit` retain the actual form map.
- `MeasuredRVZero.lift`, `lift_weight`, `liftMap`, `liftMap_labels`,
  `liftMap_measure`; `theorem_10_4_rv_zero`, `theorem_10_4_gamma_zero`,
  `theorem_10_5_rv_zero`, `theorem_10_5_gamma_zero`;
  `MeasuredRVZero.liftHom`, `liftHom_generator`, `lift_scissor`;
  `corollary_10_6_rv_zero`, `corollary_10_6_gamma_zero`.
- `ZeroForm.rvProduct`/`rvProduct_weight`,
  `gammaProduct`/`gammaProduct_weight` work on arbitrary definable domains,
  so a zero factor retains its actual density in mixed products.
  `gammaZeroForm_weight_eq_iff` distinguishes exact Gamma equality.
- `VFInDegree` now uses weighted zero objects; generic `RVInDegree` and
  `RVDegreeCoproduct` take an explicit zero object family. Concrete RV,
  Gamma and unit-volume coproducts supply the corresponding weighted
  zero category. `vfZeroDegreeEquiv`, `vfPositiveDegreeEquiv`,
  `rvZeroDegreeEquiv`, `rvPositiveDegreeEquiv` are the case adapters.

The complete Section 10 build and 68 headline type/axiom audits passed
under published Lean 4.35.0 pins. A separate full explicit-type check also
passed. Evidence is under `.scratch/weighted-zero/` and
`.scratch/section10-verified/`. The complete project-root `lake -R build`
also exited 0 (10,042 jobs), with `SpecialTransformations` compiled. There
is no remaining mathematical or verification obligation in this handoff
scope; downstream pin adaptation and its compatibility build belong to
the sequel session.
The zero lift introduces no finite-extension or Gamma-section premise.
The positive RV lift retains its existing explicit reference input.
Do not change the sequel's pin here. No new Section 2–9 mathematics,
RES, pure Gamma categories, tensor decomposition, integration kernel,
normalization, or general coarsening package is a remaining task.
The proof checkpoint is included in the authorized v1.1 publication. See
[the release verification record](../docs/RELEASE-v1.1.md) for the full
project audit and blueprint scope. Subsequent publication requires its own
authorization.

Both positive-degree cases of Theorem 10.5 are checked and integrated
through [Library.lean](Library.lean). See [STATUS.md](STATUS.md) for the
proof types, explicit hypotheses and verification receipts.

The RV proof starts with [RVVolumeLift.lean](RVVolumeLift.lean).
The forward RV proof uses the two conditions of Definition 10.3 separately.
The pointwise Gamma condition gives the value of the ratio everywhere on
the essential label set. The generic RV condition identifies the ratio
with the Section 9 RV Jacobian outside an RV-small exception. Both are
inputs to the checked prescribed lift, which provides the VF-small
exception. Its image under the lifted bijection is also VF-small.

The pointwise representative is proved in
[EssentialVFMap.lean](EssentialVFMap.lean) and
[RVVolumeRepresentative.lean](RVVolumeRepresentative.lean).
Project the source VF-small cut to the VF coordinates and take its
definable closure. Use Section 8's `vfRawClosure_dim_lt_arity` and
tuple rank bounds for the projection and the mixed preimage. The
complement contains a neighbourhood in each fixed-label chart of a
surviving point. Restrict the map and its target to the image of that
complement and transfer the local Jacobian to the restriction.
Section 9's `rvEssentialLift_complement_dim_lt` accounts for the
degenerate parts removed before lifting.

The Gamma-valued proof is in [GammaVolumeLift.lean](GammaVolumeLift.lean)
and [WeightedJacobianLocus.lean](WeightedJacobianLocus.lean). It starts with
`exists_weighted_liftMap_of_rvIso` in
[WeightedLiftJacobian.lean](../Section9/WeightedLiftJacobian.lean).
It supplies the quotient of target and source total coordinate values
at every independent source point. The proof uses the definable mixed
determinant to compare the values of `J * ∏ xᵢ` and `∏ yᵢ`, then applies
the pointwise Gamma rule on the restricted lift. The separately retained ordinary degree-zero results in
[ZeroDegree.lean](ZeroDegree.lean) specialize Sections 5 and 7. The corrected
measured-zero results are in the six modules listed above.

The fresh checks and full headline audit ran in the isolated Windows
Lake environment after Linux resumed intermittently. The pins and
restored artifact hashes matched. See `.scratch/section10/windows/` for
local logs and exit-code receipts.

Both cases of 10.4 are proved in
[RVVolumeSurjectivity.lean](RVVolumeSurjectivity.lean) and
[GammaVolumeSurjectivity.lean](GammaVolumeSurjectivity.lean). Section 3
QE determines the graph of the Gamma form by the original RV tags and
finitely many additional RV values of VF terms. Section 5 prepares this
tuple, and the form itself descends through the pullback labels. Both
cases share the determinant-one restriction. Standalone compilation,
library import, and both headline audits passed under the original Lean
4.33.1 pins.

[EssentialVFGerms.lean](EssentialVFGerms.lean) characterizes agreement
outside a definable VF-small subset by equality on independent points.
[EssentialVFMeasure.lean](EssentialVFMeasure.lean) applies Lemma 9.12 to
the composable restrictions and transfers the measure equations across the
small cut. [MeasuredVFCategory.lean](MeasuredVFCategory.lean) identifies
the quotient with these germs and supplies the groupoid. The separate
[RV groupoids](MeasuredRVCategory.lean) use the RV chain rule of Section 9.

[MeasuredScissors.lean](MeasuredScissors.lean) transports forms along
the canonical lift and proves that it respects the scissors relations.
[MeasuredPositiveLift.lean](MeasuredPositiveLift.lean) derives the
surjectivity of the two homomorphisms using Theorems 10.4 and 10.5.
[UnitVolume.lean](UnitVolume.lean) restricts this to neutral weights, and
[GradedCategories.lean](GradedCategories.lean) supplies the coproducts
indexed by degree. The library entry point contains the type and axiom
checks for the corresponding declarations. The pinned local check exited
0, and all 29 axiom reports contain only the three accepted axioms. The
full types and receipt are in `.scratch/section10/Library-local.log` and
`.scratch/section10/section10-local-audit.json`.
