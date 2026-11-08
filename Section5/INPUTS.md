# Accepted inputs and actual scope

This table describes the interfaces of the published checkpoint.
The local real and named-Gamma `Section5.Paper` exports now construct
the uniform obstacle, dimensional presentation and finite-fibre witnesses.
The named-Gamma proofs also construct the invariant logic, polynomial
support and internal real presentations. See [STATUS.md](STATUS.md)
for the checked headline scopes.

The author explicitly permits all needed material from Sections 2–4 as
given. Its independent verification is outside this Section 5 work. Missing
earlier exports appear as exact theorem hypotheses. No Section 5 conclusion
is authorized as an assumed input.

| Earlier input | Where and how it is used |
| --- | --- |
| Released LRV, ACVF, actual encoded RV equality, compatible valuation | One common VF/RV model; all geometry and comparisons track the reversal between the paper's value order and Mathlib's valuation order |
| Section 4 normalized real-sort presentations, coordinate codes, products, images, composition and inverse maps | Actual full-graph definable maps, growing canonical RV labels, focus maps, chains and contractions |
| Section 3 finite means, strict RV-fibre cardinality drop and polynomial root-factor constancy | Original-base finite root centring and root-count induction; zero polynomials are handled separately |
| `MixedRootFree.mixed_finite_definable_obstacles` | Given uniform unary membership control for arbitrary RV labels; used in the independent unary proof of Lemma 5.2 |
| `UniformVerticalObstacles v S N` in `GeneralAssembly.lean` | Explicit earlier QE/root-free interface: a uniformly bounded definable finite VF-root family over the complementary VF variables controls each presented relation on root-free head balls, uniformly in every RV variable |
| `GammaLogicInput B` in `GammaLogic.lean` | Ordinary embedding of real-base definitions, Boolean operations, complete-graph restriction/composition/swapping, and definable images for the actual invariant Gamma preimages |
| `GammaPolynomialSupportInput B` in `GammaExistence.lean` | Earlier QE occurring-polynomial consequence: finitely many VF polynomials with coefficients in `B.real` control any full invariant graph to an RV tuple, with every RV variable left free |
| `GammaPresentationInput B` in `GammaExistence.lean` | Earlier finite imaginary-parameter specialization: a Gamma-definable set admits an internal real presentation after naming finitely many proper codes whose Gamma values already belong to `B.gamma` |
| Dimensional reduction (`hreduce` in `CategoryLift.lean` and `GammaLift.lean`) | The real-sort presentation consequence after 4.2: a dimension-at-most-k object is originally-base definably bijective to a mixed set with exactly k VF coordinates; includes the coding step after the RV/Gamma-valued injection |
| Finite-RV-fibre invariance (`hfinite` in the category exports) | The zero-fibre-dimension consequence of 4.13: an originally-base definably bijective mixed presentation of a VF[k] object has finite RV fibres |

The uniform vertical input is stronger in parameter uniformity than the
existing unary export, so the two remain distinct. Its type contains finite
obstacles and root-free membership control, not transformations, preparation,
or a Section 5 existence conclusion. The VF-dimension induction and all the
special-bijection constructions are proved in Section 5. The exact input
definition is printed alongside the final theorem types.

The Gamma logic input states ordinary first-order closure laws on
`Section3.GammaParameters.DefinableOverBase`. It is not a substitute
saturation structure. The polynomial-support input contains no foci,
centring, contraction or special bijections. The specialization input
supplies only a presentation, not a deformation. All three definitions are
printed in full in `Library.lean`'s audit.

The original named base is the actual `GammaParameters.Base`. An internal
real presentation may contain codes, but every locus and full centre graph
in the output chain has an invariant certificate over the original base.
The Gamma lift objects likewise carry original-base domain and volume
graphs. Naming a single RV representative alone never proves definability
over the Gamma base.

The category reduction hypotheses supply arbitrary mixed presentations,
not RV-pullbacks and not lifts. Section 5 constructs the RV object, its volume,
the lift bijection and its inverse. The Gamma exports express the
isomorphism as an actual equivalence with its full invariant graph to the
actual Section 4 lift; they do not assume a Section 5 categorical result.

The geometry and contraction arguments need ACVF. Polynomial centring and
the existence theorems use ACVF(0,0). Coefficients belong to the named real
base, as required by the paper's substructure convention. Saturation does
not occur as a new hypothesis of the Section 5 conclusions; any earlier
use of saturation is confined to the accepted earlier interfaces.
The citation to the author's companion paper in Lemma 5.2 is not used as a
proved input: the finite-root deformation is constructed here.

Source and target statements, explicit hypotheses, compiler exits and
headline axioms are separate records. [STATUS.md](STATUS.md) states which
checks have completed. Earlier sources and accepted compiled interfaces
are inventoried under `.scratch/`; this is not an independent certification
of their current source trees.

The November 6 audit accepted the input classifications above under the
author's instruction. It found no Section 5 existence conclusion hidden in
these interfaces. The zero-fibre codomain reconciliation is now proved in Section 5 by
`ZeroNormalization`; it is not an added earlier-section hypothesis. The
normalization preserves the original parameters, functions and full Gamma
graph certificates. STATUS.md records the completed compiler and axiom check.
