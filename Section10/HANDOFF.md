# Section 10 continuation

The verification recorded below used Lean 4.33.1. The standalone
Section10 target is a local checkpoint on the Lean 4.35.0 main
baseline. Fresh 4.35.0 compilation and headline review are pending.

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
the pointwise Gamma rule on the restricted lift. At degree zero, use
the unmeasured categories as in Definitions 10.1 and 10.3.

The fresh checks and full headline audit ran in the isolated Windows
Lake environment after Linux resumed intermittently. The pins and
restored artifact hashes matched. See `.scratch/section10/windows/` for
local logs and exit-code receipts.

Start next with the RV-valued case of 10.4. Add the volume form as a graph coordinate
before applying special bijections, then use the approved almost-everywhere
form of 9.11. Check a separate bridge for the Gamma-valued case, where a
Gamma coordinate is an imaginary and the allowed objects have RV tags.
For Remark 10.2 and 10.6, check composition and inversion on common
full-dimensional domains, and reuse the Section 4 and Section 7 scissors
infrastructure after verifying its weighted variants.
