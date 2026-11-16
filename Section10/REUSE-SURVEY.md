# Section 10 reuse survey

## Weighted degree-zero correction (November 15, 2026)

The implementation starts from published main
`f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`, not the older migrated local
checkout. Pins: Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, ACVF-QE
`939346b0a99899e22a873479364e3cc5d142731c`. Existing positive results are
retained. Their published standalone Section 10 build and headline audit
passed in Actions run 42738182685; that receipt does not certify new zero
results.

Specification: the author's accepted handoff adopts actual same-base
definable nonzero RV forms, and actual Gamma forms, in degree zero.
The comparison sources are Yin, arXiv:1006.2467v1, Definitions 10.1/10.3
and 10.4–10.6, and HK, arXiv:math/0510133v3, Definitions 8.10/8.13.
HK is a convention reference, not an assumed theorem. RES, pure Gamma
categories and tensor decompositions are outside this task.

Direct local reuse (repository MIT): `VolumeScale` and its two instances,
`Map.inverse`, ordinary `RVFiniteObject` and `VFFiniteObject`,
`Section5.corollary_5_7_finite_of_rvCoded`, `Section9.liftLabelMap`,
`hasMixedVFJacobianAt_zero_arity`, and the additive scissor universal
property. Zero label projection is itself bijective, so no new valued-field
lifting theorem or Gamma-to-RV section is needed. The VF zero family keeps
the full ordinary zero-dimensional mixed presentations, not only arity zero.
Neutral-form comparison concerns ordinary **isomorphisms**: ordinary
categories also have noninvertible maps, unlike measured groupoids.

Focused external searches used “Lean Hrushovski volume forms”, “Lean
measured RV degree zero”, and “weighted FullSubcategory” in Mathlib/GitHub,
plus HK/Lean queries naming Reservoir, Lean Pool, Palomar, Tau Ceti,
the Lean projects registry, TheoremSearch and Formalpedia. No compatible
independent weighted-zero implementation was found in these indexed
searches. Catalog coverage is incomplete. The existing source and prior
survey supply the least costly route; no external proof is imported or
ported. Fresh `lake -R build Section10` and the 68-headline audit exited 0 under
the published pins. A separate explicit-type/definition audit exited 0;
all selected axioms are allowed. See `STATUS.md` and scratch receipts.
The project-root integration build also exited 0 (10,042 jobs).

Surveyed November 8, 2026 for the positive-degree RV forward lift in
[arXiv:1006.2467v1, §10](https://arxiv.org/pdf/1006.2467v1#page=28).

| Candidate | Comparison and decision |
| --- | --- |
| `Sec10.lean`, `Sec10RVVol.lean` at `8489f026528cf2990b509fdc5e14663f796aa8cb` (MIT) | Historical statement and proof sketches. They import pre-move milestone modules. The RV-side 10.5 assumes a lift and a supplied Jacobian function. The current proof instead applies Section 9 to an actual definable bijection and its mixed VF Jacobian. The 10.4 hypothesis in the snapshot already contains a transported form and a target lift. |
| `LegacyScaffold/VolumeForms.lean` at the same revision (MIT) | Outline with TODOs and a historical import path. |
| [Section 4 finite-volume categories and lift](../Section4/CanonicalLift.lean), [Section 9 essential restriction](../Section9/RVFiniteEssential.lean) and [prescribed lift](../Section9/PrescribedVolumeLift.lean) (repository MIT) | Direct reuse. The current `RVFiniteObject` enforces finite volume fibres, `RVFiniteEssentialIso` restricts to nonzero volume tuples, and 9.16 constructs the required map and VF-small exception. `GaussGraphConstruction.lean` instantiates its graph-field input from the authorized Engler–Prestel reference, as recorded in the [Section 9 status](../Section9/STATUS.md). |
| [Section 9 coordinate arithmetic](../Section9/UniformRVScaling.lean) and [Section 4 named division](../Section4/RVNamedDivision.lean) | Reuse the definable coordinate product directly. The older division API is division by named constants, while the ratio in 10.5 has a variable denominator. Use the released RV inverse symbol on that coordinate before applying the existing product map. |
| [Section 7 positive Grothendieck lift](../Section7/PositiveLift.lean) | Reuse candidate for Corollary 10.6. Its current classes forget volume forms and require a separate measure-preserving invariance proof. |

The environment is Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (Apache-2.0), and ACVF-QE
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6` (MIT). The [Section 9
handoff](../Section9/HANDOFF.md) records the source and audit trail for the
graph-field adapter and its vendored Stacks prerequisites. No additional
external mathematical premise is used.

Searches used “motivic integration”, “Hrushovski Kazhdan”, “RV Jacobian”,
“volume forms” and “Grothendieck semiring”, together with “Lean” and
“Mathlib”. Domain-filtered searches covered GitHub/Mathlib, Reservoir,
Lean Pool, Palomar, Tau Ceti, the Lean projects registry, TheoremSearch
and Formalpedia. The local catalog snapshots and the pinned Mathlib tree
are additional discovery sources. The searches surfaced the paper and
unrelated uses of motivic terminology. A compatible independent Section 10
proof was not found in these searches. Catalog coverage is limited to the
indexed results and local snapshots.

## Pointwise representatives and the Gamma forward lift

- [Section 8's closure dimension theorem](../Section8/VFDefinableTopology.lean)
  supplies a definable closure of a small VF projection. Use
  [Section 4's tuple rank bounds](../Section4/VFDimensionRank.lean) to pass
  the dimension drop to the projection and back to its mixed preimage.
  [Section 9's closure comparison](../Section9/LimitTopology.lean) supplies
  a ball at each retained point. The fixed-label chart definition then
  transfers the determinant by shrinking the original chart. The legacy
  Section 10 code assumed Jacobian locality. The Mathlib search for
  valued-field closure and finite-dimensional definable sets returned
  general topological closure and local-field APIs, while the needed
  dimension theorem is already in Section 8.
- [WeightedLiftJacobian.lean](../Section9/WeightedLiftJacobian.lean) supplies
  the value of the determinant at independent VF tuples for a chosen lift.
  Reuse the same-base mixed derivative locus and determinant map in
  [MixedDerivativeFormula.lean](../Section9/MixedDerivativeFormula.lean)
  and [MixedJacobianValue.lean](../Section9/MixedJacobianValue.lean). The
  new condition compares the values of VF products using the existing
  `termValueEq` syntax from [UnaryGerm.lean](../Section8/UnaryGerm.lean).
  A definable choice of representatives for a Gamma-valued volume form
  is unnecessary. The Gamma object uses the existing imaginary
  presentation, which includes all nonzero RV codes of each value.

These are direct uses of local MIT-licensed proofs under the existing
pins. The Gamma route introduces no external premise.

## RV-valued surjectivity

For [Theorem 10.4](https://arxiv.org/pdf/1006.2467v1#page=28), the paper
adds the volume form as an RV graph coordinate. Section 5 already proves
the map-preparation version of this construction. Use `rvPreparation_all`
in [GeneralAssembly.lean](../Section5/GeneralAssembly.lean) and
`uniformVerticalObstacles` in [VerticalObstacles.lean](../Section5/VerticalObstacles.lean).
The prepared volume form is constant on the full mixed RV key. Reuse the
object, relabelling bijection and finite-volume proof in
[PullbackLift.lean](../Section5/PullbackLift.lean) and the finite-map
characterization in [VFFiniteMaps.lean](../Section4/VFFiniteMaps.lean).
The bridges compare the raw codes in the two presentations over the
original base. The volume form descends by the definable graph of its
factorization through the key.

Reuse the generic determinant-one result of Lemma 9.11 from
[SpecialJacobianGeneric.lean](../Section9/SpecialJacobianGeneric.lean).
The pullback relabelling preserves VF coordinates. On the intersection
of its composite chart with the original special-bijection chart, the
VF functions therefore agree. Use the checked Jacobian exception and
essential restriction results to obtain the pointwise measure equation.

The local results use the repository's MIT license and the existing
pins. A focused search for Lean formalizations of Yin's special bijections,
RV pullbacks and volume surjectivity found the paper and related motivic
integration literature. The local checked preparation and differentiation
interfaces supply the prerequisites without a new reference hypothesis.

## Gamma-valued surjectivity

The November 9 search for Lean implementations of Gamma-valued motivic
surjectivity and finite VF support for mixed RV formulas found Yin's
paper and related formalization candidates, but no independent proof
compatible with the pinned language. The unary finite-support result in
[MixedPolynomialSupport.lean](../Section3/MixedPolynomialSupport.lean)
is a close local analogue. For arbitrary VF arity, reuse the checked
`DefinableOver.quantifier_free` and `qf_source_boolean` from Section 3.
Their sorted Boolean expressions already isolate the VF polynomials
inside RV expressions. Collect their RV values by a syntax induction
and use the original parameter package to make the tuple definable.

Use all real RV codes of Gamma in the graph relation. Agreement on the
collected data and the original RV labels makes membership agree for
every code of the Gamma output. The form then descends through the same
pullback labels and determinant-one essential map as the RV case.
This reuses the local MIT-licensed development and the existing pins,
with no choice of a definable Gamma-to-RV section or new reference
hypothesis.

## Essential morphisms and measured scissors

The paper's Remark 10.2 uses agreement outside a VF-small set. Use the
dimension and independent-tuple results in [Section 4](../Section4/VFDimensionRank.lean)
to recognize agreement over the original parameter set. The chain and
inverse laws use [Lemma 9.12](../Section9/MixedDifferentiationAE.lean) on
the actual composable restrictions and the uniqueness of the fixed-label
Jacobian. On RV use the existing
[finite-volume RV chain rule](../Section9/GenericRVJacobianChain.lean) and
the [Gamma product formula](../Section9/GammaJacobian.lean).

For Corollary 10.6 use the existing
[positive additive presentation](../Section4/PositiveAdditivePresentation.lean).
The [Section 7 lift and restriction identities](../Section7/LiftedIsomorphism.lean)
handle the underlying sets. The remaining check compares the two
pullbacks of the same weight along the original label map. Under the
printed, now superseded zero convention, the paper uses unmeasured
categories. [Corollary 7.7](../Section7/PositiveSurjectivity.lean) remains
the source for the separately retained ordinary zero result. The corrected
weighted-zero construction is recorded at the top of this survey.
The constant-volume versions use the same determinant-one representation
as Theorem 10.4, including its preservation of the range of the form.

The source survey on November 9 checked
[the numbered statements in the paper](https://arxiv.org/pdf/1006.2467v1#page=27)
and searched for compatible Lean proofs of measured essential bijections
and Grothendieck scissors. The search found the paper and related motivic
integration literature. The checked MIT-licensed local proofs provide the
needed interfaces under the existing Lean, Mathlib and ACVF-QE pins.
