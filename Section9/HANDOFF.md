# Section 9 continuation

Started November 7, 2026 from published revision
`32d7815b7a58624a620abb9d6423721b7e094520`. Follow root `WORKFLOW.md`,
`AGENTS.md` and `Section3/HANDOFF.md`. Work from the audited
`Section9.Library` boundary described in [STATUS.md](STATUS.md).

Start with [LEMMA-9.15.md](LEMMA-9.15.md). The three-cone, two-ray
permutation rules out the printed Gamma assertion and the proposed
agreement on a full VF-dimensional locus in every fibre. It also tests
the multidimensional passage in HK 5.23. Use the corrected targets
separately. Prove 9.16 by computing the determinant of the chosen Section 7
lift, then applying the affine tail correction. The arbitrary-lift RV
comparison in 9.15 is a separate target.
For later descent, use the constant-valuation statement and the intrinsic
proof by coarsening at positive infinitesimal values. This is the route the
author prefers. The mixed-characteristic argument remains an alternative;
the author approved Loeser's change-of-variables reference for that route.
On November 7, 2026 the author approved retaining
the RV clause of 9.15, removing its unrestricted Gamma clause, retaining
9.16 with its pointwise Gamma compatibility, and treating constant-finite-
valuation Gamma descent as a separate target. Gamma-volume lifting remains
in scope. The author approved restricting the active Jacobian targets to
RV[n], with finite-to-one volume maps. Existing ambient-category results
can be reused internally. The author extended this scope to the volume
categories in [Section 10](../Section10/README.md), using RV[n] and VF[n]
for both RV-valued and Gamma-valued forms. On November 8, 2026 the author
gave standing approval to use the Stacks Project and its Lean formalization.
Other new external mathematical references require approval before use.

Theorem 9.16 already requires finite-to-one f and g, hence RV[n]. See
[RV-CATEGORY-AUDIT.md](RV-CATEGORY-AUDIT.md) for the VF[n] target, finite-fibre
restrictions and lower-dimensional head construction without global unit
normalization. Marker, Engler--Prestel and the Stacks Project remain
authorized reference inputs under the standing agreement. Record exact
tags and check source compatibility and theorem types before using the
recent Stacks Lean formalization.

Use [TARGETS.md](TARGETS.md) for the full Section 9 proof order. The
post-restart checks verified 9.2–9.5, the VF differentiation core, the
same-base existence and continuity statements for 9.8–9.9 and the
approved 9.12. The positive-arity 9.11 headline for the actual special
chain and its inverse passed the type and axiom audit. Its separate
zero-arity statement compiled. For 9.15,
Gauss evaluation, the power-basis bound, reduction
of a bounded derivation and identification of the simple-root slope all
compile. The ring-theoretic derivation bound compiles for an étale
cover and for a simple generator with a residue power basis. The
existence of that generator from residue degree equality also compiled.
The Stacks `04GN` and `04GS` source closures and headline audits passed
in scratch under the project pin. The ordinary local-map adapter, the
surjective-image étale cover, and the valuation-ring image identification
also passed. The local étale stage is a valuation ring by the checked
flat-ideals argument. `FilteredValuationAudit.lean` checks its transfer
to the henselization, together with injectivity and algebraicity.
`EmbeddedHenselizationAudit.log` checks the embedded henselization and
its étale cover. The licensed source subset is in `VendoredStacks/`.
`GraphReferenceAudit.log` checks the library construction that adjoins
the finite algebraic output tuple and isolates the Engler–Prestel input
for henselianity and residue degree in residue characteristic zero.
`acvf_henselizedGaussGraphInput_of_finite_extension_reference` supplies
this graph-field input in the published ACVF language.

For the uniform comparison, work first in a fixed nonzero Gamma fibre
and normalize it by auxiliary representatives. Use the diagonal simple
equations `Pᵢ(X,Yᵢ)` that vanish on the entire residue correspondence.
Over the rational function field in `X`, their tensor-product quotient
is finite étale by squarefreeness. A Boolean combination of polynomial
zero tests in this finite product of fields is represented by a single
idempotent. For an atomic test `a = 0`, choose a partial inverse `b`
with `a²b = a` and use `1 − ab`. Use multiplication for conjunction
and subtraction from `1` for negation. Lift the selector to a polynomial
and clear its denominators. Its nonvanishing cuts out the correspondence
on the generic fibre of the square system. The bad input locus is
definable and contains only dependent tuples, so the existing residue
polynomial cover supplies one nonzero polynomial vanishing on it. This
gives one open chart above the complement of a proper input locus.

For chart soundness, include the two Jacobian block determinants in
`R`. The localization of the polynomial quotient by `Pᵢ` on this
chart is standard smooth of relative dimension zero over the input
polynomial ring. It is reduced. [Stacks 00T6](https://stacks.math.columbia.edu/tag/00T6),
[Stacks 033B](https://stacks.math.columbia.edu/tag/033B).
The Nullstellensatz then expresses any polynomial vanishing on the
correspondence in the ideal generated by `Pᵢ` after localizing at `R`.
See [Stacks 00FV](https://stacks.math.columbia.edu/tag/00FV).
Clearing the localization gives the certificate used in
`ResidueTangentChart.lean`. Thus the tangent on the chart is the kernel
of the differential of the `Pᵢ`, and the two block determinants give
an invertible graph. The equation, nonvanishing, chart containment
and input coverage conditions are first order for each choice of
finite monomial supports. Quantify over the coefficient tuple.
The resulting formulas cover all nonzero tuples of RV scales, so
apply the same-base finite subcover theorem to that set of tuples.
This avoids choosing a section of the map to Gamma. For the
dimension bound, fix one scale tuple on a maximal value fibre of a
candidate bad set. One of the selected supports gives a certificate
at that scale. Name its finitely many coefficients when choosing an
independent normalized input. The nonzero input-cut polynomial then
cannot vanish there.

For the comparison with a chosen lift, project the definable locus
where the full mixed derivative is missing or its RV determinant
disagrees with the chart value to the source labels. At an independent
normalized residue tuple, every VF representative has Gauss
evaluation over the auxiliary VF field. Thus the pointwise comparison
holds at every representative of that label. This rules out full RV
dimension for the projected discrepancy locus by taking a maximum
value fibre and then an independent residue tuple there. The same
argument works against a given definable prescribed form on the
full-dimensional branch of 9.16.

The pointwise RV chain rule after Definition 9.14 fails in `RV[1]`.
[RV-CHAIN-ERRATUM.md](RV-CHAIN-ERRATUM.md) gives the three-sheet example.
Use the generic chain rule with one graph point and coordinate
derivations on the joint graph field. The Gamma chain rule remains
pointwise.

For 9.16, the checked Section 7 witnesses retain both simple blocks and
their weights. The weighted gluing and the derivative formula for a
selected polynomial branch compiled. `FiniteHeadCover.lean` gives the
finite coordinate cover. `WeightedLiftJacobian.lean` applies the branch
formula to the actual head map and passed its type and axiom audit.
`AffineTailJacobian.lean` passed the audit for the affine extension's
determinant. `LiftLabelRepresentatives.lean` builds the finite family
of tail and prescribed determinant labels. The affine tail graph uses
the default branch on the VF-small head exception.
The head value suffices on every head pair and avoids discarding head
labels.

`WeightedAffineLift.lean` compiles the fixed-head construction with
the actual same-base map. `FiniteHeadPrescribedLift.lean` passed the
type and axiom audit for its same-base exceptional set and the paper's
Gamma compatibility form. The lift reindexes the two heads separately
with their determinant signs and glues along a finite refinement of the
source labels. The full-dimensional part uses the residue comparison.
[DIFFERENTIATION-ERRATA.md](DIFFERENTIATION-ERRATA.md) records the
obstructions and the replacements for 9.11 and 9.12 approved on
November 7, 2026. The replacement 9.11 is almost everywhere under the
paper's standing hypotheses. The replacement 9.12 assumes full
differentiability in local fixed-label charts pointwise, and its
almost-everywhere consequence assumes the first map is finite-to-one.

[STATUS.md](STATUS.md) records the evidence and scope. [REUSE-SURVEY.md](REUSE-SURVEY.md)
records the published dependencies and proof references.

The current checked components beyond the fixed-head theorem include
`FiniteLiftReindexing.lean` for the two directions of coordinate
permutation, `AffineMixedDerivative.lean` for the named affine maps,
`PolydiscNormalization.lean` for the maximal-ideal normalization,
`LiftRestriction.lean` for the local Jacobian transfer, and
`ResidueIndependentFibre.lean` for an independent residue tuple after
enlarging the small coefficient substructure. The square open system is
étale and reduced in `OpenSquareSystem.lean`. The inverse variable
can be cleared by `ResidueChartDenominators.lean`. These modules are in
the audited integration boundary.

`NormalizedRVComparison.lean` compiled from source with the explicit
henselized graph-field input. `VolumePairMap.lean`, `GenericVolumePair.lean`
and `UniformRVScaling.lean` also compiled. `IntegrationVolumeAudit.log`
verified the finite-label gluing, discrepancy projection, finite-volume
dimension lemmas and small normalization bases.
`NormalizedComparisonAudit.log` verifies the affine transport to the
original coordinates, and `ArbitraryLiftComparisonAudit.log` verifies
the fixed-value rank argument and the source volume-image exception for
a definable candidate. `PaperLiftComparison.lean` combines the result
with the generic chart value. `PaperRVComparisonAudit.log` checks both
arities, and the positive-arity theorem has the graph-field input as
its remaining reference premise.

The support certificates, open charts, finite support cover of all
scales, and chart output relation compiled. `VolumeCoverAudit.log`
checks the generic selector and the existence of a chart with an input
cut. `VolumeChartAudit.log` checks the definable chart output and its
soundness. `PaperRVComparisonAudit.log` also checks the finite chart
cover and `GenericRVJacobian.lean`'s same-base generic Jacobian.

For 9.16, `PrescribedHeadAudit.log` checks the sign-adjusted head
construction. `PrescribedVolumeAudit.log` checks the lower-dimensional
branch, the small-label repair and the full positive-arity theorem with
its explicit graph-field input. `GenericVolumeChain.lean` compiled the
existence of a point satisfying the chain formula in every same-base
full-dimensional subset of source labels. `RVChainFinalAudit.log` checks
the resulting generic chain rule with a same-base RV-small exception in
the labels and the source volume image. `GammaDescentAudit.log` checks
the intrinsic Gamma theorem for polydiscs with a VF-small exception.
That theorem is in `Section9.Library`, whose updated import compiled.

The final `Section9.Library` and `FinalSection9Audit.log` passed under the
project pin with the ACVF graph adapter included. In Section 10, use the
agreed `RV[n]` scope and instantiate the shared graph premise with
`acvf_henselizedGaussGraphInput_of_finite_extension_reference`. The named
Engler–Prestel finite-extension facts remain the explicit reference
premise. The proposed wording of the generic RV chain rule is recorded in
[RV-CHAIN-ERRATUM.md](RV-CHAIN-ERRATUM.md).
