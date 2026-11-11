# Section 8 status

## Finite-open-radius consumer verification

The author-approved finite-open-radius correction also reaches
`UnaryBalls.lean`. Its small-ball witness now uses `Balls.OpenRadius` and
`Balls.openRadius` with the proved nonzero radius. The old conditional
singleton presentation is removed from this caller. Both headline statements
are unchanged. Source SHA-256: `37d8f2a735a065d227ad9500557daad04293eb07a11c4304ac4d9845dd7c3b6b`.

The diamond-integral consumer built this module and its differentiation and
RV-local-constancy import boundary under Lean 4.35.0, with pinned ACVF-QE
`939346b0a99899e22a873479364e3cc5d142731c` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The full consumer check
`lake env python3 'section 2/verify.py'` passed with 195 section theorems and
292 selected reuse declarations. It explicitly prints the full types and
axioms of `rawOpenBall_infinite` and
`infinite_definable_contains_small_ball`; only `propext`, `Classical.choice`
and `Quot.sound` occur. The source agrees with the dependency copy, and the
portable finite-radius patch now includes this caller.

Evidence in `/workspace/diamond-integral/section 2/`: `.scratch/r036-verification.log`,
`verification/headline-audit.txt`, `verification/status.json` and
`reuse/manifest.json`. This is a selected consumer import/build and caller
audit, not a fresh verification of the complete Section 8 library. The older
complete-library checkpoint below has its own source and toolchain scope.


## Complete Section 8 verification

On November 7, 2026, all 40 active modules and the combined import of
`ACVFQE` and `Section8.Library` compiled with exit 0. The audit checked
the full headline types, explicit hypotheses, and resolved import
fingerprints. The 47 axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. The certificate is
`.scratch/section8-development/certificate-section8.json`. The exact
checked source, receipts, and compiler output are preserved under
`.scratch/section8-verified-section8/`.

The complete library covers Lemmas 8.1–8.7 and 8.9, Definition 8.8,
and both almost-everywhere definitions. The dimension-drop statements
use positive VF source arity. Lemmas 8.4 and 8.5 retain the explicit
Engler–Prestel henselization hypotheses, and Lemma 8.6 names a
positive Gamma element from the base as in the standing paper scope.

The slope proof applies the authorized reference to the intermediate
field obtained by adjoining a test point to the parameter field.
A value in its henselization already occurs in the intermediate field.
Valuation invariance and the fixed-field theorem put the definable
output in that henselization. This yields integrality of the germ slope.
The inverse has integral reciprocal slope, so the slope is one.
Lemma 8.5 uses this slope step in its local RV difference calculation.
[Engler–Prestel, Theorems 4.1.3, 5.2.2 and 5.2.5](https://link.springer.com/book/10.1007/3-540-30035-X).

Lemma 8.4 is scoped to proper centered balls, with field representatives
of finite radii for both balls. The author excluded the whole-field ball
case from Lemma 8.4 on November 9, 2026.


The library audit replayed all 40 Section 8 modules and 595 declarations
in the pinned Lean kernel against the current earlier imports. This
checks the artifacts against the two updated Section 4 providers,
`CoordinateDimension` and `VFDimensionRank`. The replay exited zero
in `.scratch/section-through8-section8-kernel.log`.

## Lemma 8.1

November 6, 2026. Initial target: Lemma 8.1 of
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1#page=19).

The Lemma 8.1 proof is in `UniformBalls.lean`, `UnaryBalls.lean`,
`SeparatedSets.lean` and `GammaBalls.lean`. It uses the released
open-ball presentation, the checked finite-obstacle theorem for unary VF
sets, and the paper's head/tail induction. The conclusion is finiteness
for every finite VF arity, including arity zero. It treats distinct
centres, uses one fixed ordinary radius, and gives both a VF-representative
statement and a statement with an actual Gamma radius and imaginary base.
The hypotheses of the finiteness theorem are ACVF and definability.

`UniformBalls.lean` compiled with exit 0 and no diagnostics using
`lake env` and Lean 4.33.1 (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).
Its source SHA-256 is
`d3f978c92f875cf1600d51ca57429fcce75bf9c2beea6d249c3afad10401db20`;
the compiler receipt is in `.scratch/section8-development/UniformBalls.json`.
The Mathlib and ACVF-QE pins are unchanged. `UnaryBalls`, `SeparatedSets`,
`GammaBalls`, and `Library` also compiled with exit 0. The five full types
in `.scratch/section8-development/Library.log` were reviewed against
the source. All five axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The combined ACVF-QE and Section 8
import check passed with exit 0. The integration certificate records
the source hashes, compiler and dependency pins, exact command, and
the fingerprints of the imported compiled modules. See
`.scratch/section8-development/certificate-8.1.json` and
`.scratch/section8-development/Integration.log`. Earlier compiled
dependencies were reused. The two statements of Lemma 8.1 are verified.
The registered Lake target is `Section8`, with entry point `Section8.Library`.
The 8.1 sources, compiled artifacts, and audit are also saved in
`.scratch/section8-verified-8.1/` so that the checkpoint survives extensions.

## Lemma 8.2

For Lemma 8.2, define the exceptional set by quantifying the two nonzero
radius representatives and expressing uniqueness in the inverse-image
intersection using the actual definable graph of the map. Establish the
uniform formula before taking any fibres. `NeighbourhoodRelations.lean`
compiled with exit 0. The relation handles simultaneous ball membership
in the centre, point, and radius, and the equal-radius disjointness
criterion. The later drafts `IsolatedGraph` and `IsolationFibres` encode
the two-radius isolation relation and its fixed-radius fibres.

For the dimension argument, look for a full-dimensional fixed-radius
fibre without assuming a global choice of Gamma witnesses. If a full
dimensional exceptional set has a generic VF point, take any two RV
representatives of witnesses there. Adjoining RV names does not enlarge
the VF parameter field. The existing independent-point neighbourhood
result should then supply a polydisc in that same fibre. Shrink it to the
fixed input radius. Its image is injective and uniformly separated by the
fixed output radius, contradicting 8.1 and infinitude of the input
polydisc. `IsolatedGraph`, `IsolationFibres`, `IsolationGeometry`, and
`IsolationDimension` compiled with exit 0. `IsolationDimension` gives the
strict dimension bound for positive arity in the canonical presentation.
Its source SHA-256 is
`e9cd61b5e203361672cb844b168603df681f59e5e6cd34b6785d1c5759ca82f9`.
The combined `ACVFQE` and `IsolationDimension` import passed with exit 0.
The full types of `isolatedInputs_definable`, `mem_isolatedInputs_iff`,
`independent_not_isolated`, and `lemma_8_2` were reviewed in
`.scratch/section8-development/Core-8.2.log`. All four axiom reports list
only `propext`, `Classical.choice`, and `Quot.sound`. The dimension theorem
uses ACVF, canonical presentation, genuine small-parameter saturation,
and the RV code condition on the auxiliary Gamma presentation. Its graph
and exceptional set use the same real parameter base.
The compiler receipts and resolved providers match the current sources
and compiled modules. The record is
`.scratch/section8-development/certificate-8.2-core.json`.
The checked core modules are registered in the `Section8` Lake target.

`IsolationFamilies` and `IsolationGamma` develop the original Gamma-base
interface. `IsolationRadius` identifies the exceptional locus with the
paper's singleton intersection using the actual Gamma radii.
`IsolationFamilies` and `IsolationGamma` compiled with exit 0 and linter
diagnostics only. `IsolationRadius` compiled with exit 0 and no
diagnostics. The full `Section8.Library` audit compiled with exit 0.
The full headline types were reviewed. `lemma_8_2_gamma_base` defines
the exceptional locus over the original real and Gamma parameters and
gives the strict dimension bound via a finite RV representative
presentation of the same graph. The actual Gamma space discharges the
auxiliary RV code condition. `mem_isolatedInputs_iff_gamma` identifies
the locus with the singleton intersection in the paper. The 13 axiom
reports list only `propext`, `Classical.choice`, and `Quot.sound`.
The combined ACVF-QE and Section 8 import passed with exit 0, and the
imported module identities match the successful source checks. See
`.scratch/section8-development/certificate-8.2.json`, `Library.log`,
and `Integration-8.2.log` in the same directory. The complete 8.2
checkpoint is registered in the `Section8` Lake target.

## Lemma 8.3

The draft starts with a polynomial germ at the centre and a finite set of
possible ties between specialized terms at a nonzero root. A second draft
extracts a nonzero polynomial from the definable graph of each scalar
unary fibre, then uses saturation to obtain a finite set of polynomial
shapes for the family. Appending the centre as a VF parameter gives a
definable family of centred output differences over the same base.
The good-locus draft uses 8.2 to bound each exceptional fibre. The draft
algebra bounds the input and output powers by the shape and gives the
positivity argument for a selected tie. `UnaryValueLaws` gives a draft
formula for each tie. `ScalarSlopeGerm` uses the finite cover to select
a single positive power law or a zero germ for one scalar fibre.
`CenteredUnaryGraph` and `UniformSlopeGerm` extend the draft to the
tuple-valued family and supply uniform bounds on both exponents. These
proofs are grouped into `UnaryPolynomial` and `UnaryGerm`.

`GammaPowerGerm` transfers the law to the actual value group and uses
the overlap of two punctured balls and injectivity of positive powers
to fix the intercept. `GammaPuncturedBall` and `DefinableRadius` give the
draft radius selection on a definable upper ray. `GammaLawFormula`
quantifies the VF representatives of the two Gamma variables and
uses the actual graph for the value comparison and power equality.
`UnarySlope` assembles the canonical real-base proof with both
definable constants. The combined development file compiled with exit 0
using the pinned toolchain. Its compiler receipt is
`.scratch/section8-development/Drafts-8.3.json`. The grouped source
modules `UnaryPolynomial`, `UnaryGerm`, and `UnarySlope` compiled
with exit 0. The full `Section8.Library` audit compiled with exit 0.
The canonical headline uses genuine small-parameter saturation and
pure characteristic zero. It defines a good locus over the real base,
with finite complement in each unary fibre, and a common finite set
of positive rational slopes. `unaryLocalSlope` gives both actual Gamma
constants over that base with the centre and VF parameter tuple named.
The local law is constant or the exact powered equality.
The combined ACVF-QE and Section 8 import passed with exit 0 and
matched the compiled module fingerprints. All 24 headline reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.
See `.scratch/section8-development/certificate-8.3-canonical.json`
and the checkpoint under `.scratch/section8-verified-8.3-canonical/`.
`lemma_8_3_gamma_base` in `UnaryGamma` keeps the full invariant
preimages of the graph and the
constant and exact-power witnesses. The good locus is the same
fibrewise complement of the isolated-input sets. The original-base
shift and radius come from uniqueness and the endpoint of the valid
radius ray. The production compiler, full headline audit, and
integration passed in `certificate-8.3-8.4-8.6.json`.

## Lemmas 8.4–8.9 and the intervening definitions

### Lemma 8.4 verified

`ValuedSlopeIntegrality` and `BijectionSlope` compiled with exit 0 in
the pinned environment. Their receipts are in
`.scratch/section8-development/`. For the integrality step, genuine
saturation gives a nonzero value below the old nonzero multiplicative
values. The least supported monomial determines the value of a
polynomial there. The valued-field proof transfers the definable
singleton to the value group of the old field with the input adjoined,
using the two explicit Engler–Prestel henselization facts. The
ball-preserving bijection gives positive slopes in both directions,
whose integrality and reciprocity force slope one. The partial graph
statement derives total extensions of the map and inverse internally.

`lemma_8_4_named_gamma_base` in `CenteredGammaSlope` tests the law on
the original partial graph over the original Gamma base. It selects
the unique actual Gamma intercept and a radius from the closed ray of
valid radii. The full type and the unfolded
`ImmediateHenselianExtension` hypothesis were checked. The latter
records valuation-ring henselianity, the value-group part of
immediacy, and preservation of valuation comparisons under
automorphisms of the algebraic closure over the henselian field. The
compiler, axiom audit, and combined integration passed in
`certificate-8.3-8.4-8.6.json`.

### Lemma 8.5 verified

`PairedDifference` uses the local inverse and the checked Lemma 3.17
to produce a single-centre RV law. It keeps the entire RV witness
fibre and tests the paired law on a ball contained in the domain.
`PairwiseGamma` defines the full witness relation directly from the
partial graph over the original Gamma base. Uniqueness names the
nonzero RV multiplier, and the endpoint of the valid upper ray gives
a named radius. The production compiler and final audit passed for
`lemma_8_5_partial` and `lemma_8_5_partial_gamma_base`. The latter
names the radius and RV multiplier over the original base with the
centre adjoined. Both results and the full witness formula use only
the permitted axioms. See `certificate-section8.json`.

### Lemma 8.6 verified

`PowerEstimateCore` and `PowerEstimateFamily` compiled with exit 0
for the canonical and original Gamma-base 8.6 statements. The unary
denominator bound gives one positive exponent. The induction splices
horizontal and vertical estimates and uses Lemma 8.9 on the entire
RV witness fibre. The original-base result projects the full witness
relation and selects the named shift and radius from their definable
rays. The positive Gamma element used in this selection is supplied
by the paper's nontriviality assumption on `Γ(S)`. The full headline
and integration audit passed in `certificate-8.3-8.4-8.6.json`.

`VFNeighbourhoods` compiled with exit 0 and no diagnostics. Its source
and dependency receipt is in
`.scratch/section8-development/VFNeighbourhoods.json`. The headline
audit and integration passed as part of the canonical 8.3 checkpoint.
`VFDefinableTopology` also compiled
with exit 0 after fixing the transcendence-degree type. Its receipt is
`.scratch/section8-development/VFDefinableTopology.json`.
### Lemma 8.7 verified

`lemma_8_7_canonical` and `lemma_8_7_gamma_base` construct a closed
definable exception of VF dimension below the positive source arity.
The map is continuous on its complement. The Gamma-base theorem
defines the exception over the original base and computes the
dimension of the same set in the actual Gamma space of the normalized
model. The proofs use genuine saturation and smallness of the real
parameter base.

`GenericOutputBall` proves continuity at independent inputs by choosing
a centre in a prescribed output ball that preserves the independence
of the input and naming the radius in RV. `ContinuityFormula` defines
the discontinuity set. `GenericContinuity` closes it and bounds its
dimension. `ContinuityFamilies` and `ContinuityGamma` keep the original
Gamma parameter block fixed in each test. This proof is independent
of Lemma 8.6.

The five continuity modules and the `ACVFQE` and `Section8.Library`
integration compiled with exit 0. The full headline audit reviewed
both versions of 8.7, `continuousAt_of_independent`, and
`normalizedContinuityException_gamma_definable`. All four use only
`propext`, `Classical.choice`, and `Quot.sound`. The certificate is
`.scratch/section8-development/certificate-8.7.json`, with checked
source and receipts preserved under `.scratch/section8-verified-8.7/`.

`AlmostEverywhere` defines the separate VF and RV exceptional-set
conditions. `RVLocalConstancy` implements Definition 8.8. Both compiled
with exit 0 and no diagnostics. Their headline and integration audits
passed as part of the canonical 8.3 checkpoint.

### Lemma 8.9 verified

`lemma_8_9_canonical` and `lemma_8_9_gamma_base` in `RVFibreGeneric`
and `RVFibreGamma` give an open definable locus of local constancy of
the actual RV fibre, with complement of VF dimension below the
positive source arity. The original-base result keeps the original
Gamma names in the definability assertion. It uses finitely many RV
representatives only to present the same complement in the actual
Gamma space for the dimension calculation. Both versions use genuine
saturation and smallness of the real parameter set. The Gamma-base
version also uses an infinite saturation cardinal to name the finite
representative tuple. A compatible valuation supplies the topology.

Well-sorted VF subterms have no RV inputs, so the Section 4 generic
neighbourhood is uniform in every RV fibre coordinate. The definable
locus tests equality of the entire fibre on a neighbourhood. The
dimension argument excludes independent inputs from the complement.

The pinned compiler exited 0 for all five 8.9 modules and the
`ACVFQE` and `Section8.Library` integration. The headline type audit
reviewed both lemmas, `rvFibre_locallyConstant_of_independent`, and
`rvConstantRaw_gamma_definable`. All four depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The verified import paths and
fingerprints are in `.scratch/section8-development/certificate-8.9.json`.
The checked source and receipts are preserved under
`.scratch/section8-verified-8.9/`.
