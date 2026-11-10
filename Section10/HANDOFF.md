# Section 10 continuation

Follow the root workflow and [Section 3 handoff](../Section3/HANDOFF.md).
The paper target is [arXiv:1006.2467v1, §10](https://arxiv.org/pdf/1006.2467v1#page=27)
in the approved finite-volume `RV[n]` and `VF[n]` scope for both
RV-valued and Gamma-valued forms. The [Section 9 handoff](../Section9/HANDOFF.md)
records the prescribed lift and the explicit Engler–Prestel input.

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
the pointwise Gamma rule on the restricted lift. At degree zero,
[ZeroDegree.lean](ZeroDegree.lean) uses the unmeasured categories of
Definitions 10.1 and 10.3 and specializes the lift results from Sections
5 and 7.

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
