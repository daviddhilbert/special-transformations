# Section 7 status

Updated November 7, 2026 (America/Los_Angeles).

## November 7 repair of the fixed-degree surjections

`corollary_7_7` and `corollary_7_7_finite` now invoke
`Section5.Paper.corollary_5_7` and its finite form. Both use the actual
Gamma quotient in the definition of dimension. The new source compiles
with exit zero. Uniform obstacles, dimensional presentations, and
finite-fibre invariance are obtained from proofs.

The combined `Section7.Library` check exited zero with 276 permitted
axiom reports. The revised complete headline types were inspected, and
the project root compiled with exit zero. The local receipt is
`.scratch/section5-repair-evidence.json`. This was a targeted rebuild
of the changed modules and their entry points, with earlier checked
compiled imports reused.

The maps act on the positive Grothendieck quotients of objects and
maps definable over `B.real`, with `B` genuinely VF/Gamma-generated.
Section 5 now also proves both named-Gamma representation theorems.
`GammaRVIso.liftIso` constructs the lift of an RV isomorphism over
the original named-Gamma base. The defining label graph remains over
that base, and the VF fibre relation is definable over `B.real`.
The four source checks for this step exited zero in
`.scratch/section5-repair-gamma-lift-source.log`.

`Section7.Paper.corollary_7_7_gamma` and
`Section7.Paper.corollary_7_7_finite_gamma` construct the two positive
quotient homomorphisms with the additional names in `B.gamma`.
The presentations use actual definable objects, actual isomorphisms,
and scissors for unions and intersections in a common arity.
On the RV side they retain the companion graph. Lift respects these
relations and is surjective by the checked named-Gamma forms of 5.7.
The final source, `Section7.Library`, and project root exited zero.
The 277 axiom reports and full named-Gamma headline types are in
`.scratch/section5-repair-gamma-scissors-source.log`. The earlier
conditional checkpoint below records the previous signatures.

## Lemma 7.2 verified in the pinned library

Ordinary multivariate Hensel existence and uniqueness are now implemented
in `MultivariateHensel.lean`, using the actual etale algebra of the square
system and the unramified-diagonal uniqueness theorem. `GeneralizedHensel`
applies that theorem to the constructed valuation-ring system;
`EncodedHensel` gives Lemma 7.2 on the actual published VF/RV sorts, deriving
algebraic closedness from the ACVF model. All seven new module source checks
passed with exit zero. The expanded verifier has now also exited zero:
eighteen fresh module compilations, 90 permitted-axiom audits, unchanged
resolved dependencies, and the combined ACVF-QE import passed. The separate
readable statement check also exited zero. The first 64 types and defining
predicates print identically to the previous reviewed checkpoint, with
matching proof source, axiom and provider identities. The 26 new full types
and their explicit hypotheses were reviewed. The separate project-root check
also exited zero, with no diagnostics and the source unchanged. The complete
checkpoint, including matching sources and output artifacts, is preserved
in `.scratch/section7-hensel-certified/`.

The full Lemma 7.2 verifier certificate SHA-256 is
`f4cd6aecdad58736be77a7b9588e70e3a640a5240be7b117c7b4c6c7f5c909bf`.
It binds the eighteen source identities and integration output; the resolved
10,579-provider external manifest matches the earlier eleven-module run.
The raw full type and axiom log SHA-256 is
`6bf22d1083bdcc48d4644b5f2d4e34d289f6aff2c3fd10ea683cc159e6108ab8`.
`HenselHeadlineReview.log` and `HenselStatementReview.json` in
`.scratch/section7-verified/` bind the complete readable type output and
review to this exact certificate and source set. The statement review's
SHA-256 is `952a005b1993b14dea16e79ec0a827dc7d948422dde434cc14d828e1c8f7a06b`.
The fresh root receipt SHA-256 is
`6aeeb7c545fe6f1a61daccbfa83f3c2129feca9abbe9f9148ecd0f7ac07bf636`;
it records 304.43 seconds, exit zero and the checked root source identity
`4264faf0ac3849b741fc33a51b2ba59557e51ee571b8d7c3a5224c22f94d2b09`.
The archive index SHA-256 is
`e71adb22b473993c4f8f7f6bf935873402ea9a147359ad2d4aeff84627ce3743`.

The eleven-module/64-headline checkpoint described below is preserved,
including matching sources and artifacts, in `.scratch/section7-jacobian-certified/`.
It does not certify the expanded entry point. Development receipts are in
`.scratch/section7-hensel-development/`. Work continues on the later targets;
a verified checkpoint is not a stopping instruction.

## Expanded entry-point verification

Seventeen additional modules have passed selected fresh source compilation
with matching inputs and sources. The expanded `Library.lean` now imports
them, including `ResiduePolynomialProjection` (Definition 7.1),
`ResidueConstructibility` (Remark 7.5), the simultaneous integer determinant
choice, and the checked finite-row, coefficient, normalization and derivative
bridges for Lemma 7.4. The targeted 35-module entry-point check passed:
34 source and artifact receipts were bound, the entry point compiled with
exit zero, and all 137 axiom audits use only the allowed axioms. The first
90 printed types and axioms are a byte-identical prefix of the previous
reviewed log. The 47 additional full types and explicit hypotheses were
reviewed. The fresh project-root import check passed with exit zero, an
unchanged source and no diagnostics.

The targeted certificate SHA-256 is
`2deca6783c908bbf4082eb60075ccd4e1209960354e9b842b4033058d0d3f39f`;
the statement review is
`10488cac61996c01713ae79eed1033016aece648676c38b0f5dc63e99b3b1b3a`
and the root receipt is
`9086dfa5b1e843c334c139d890b3ca8937484f8bb43a6dd123de83400d8b9238`.
The evidence, checked sources and compiled artifacts are preserved in
`.scratch/section7-expansion-certified/` (archive index SHA-256
`a29effdba228efd0f2e0c8e2681f9f8c2f262e540eec4d825efd0af73b86f29a`).
This targeted audit reuses the verified Lemma 7.2 proof modules. The
eighteen-module archive preserves their full fresh verification.

Outside the active import boundary, selected source checks of
`FiniteRVPolynomialPattern` and `GuardedParameterScope` passed with exit
zero and matching input/source hashes. The first checks of
`GuardedLaurentSide` and `WeightedPolynomialTests` exposed an omitted
compatibility binder and an ambiguous subtraction rewrite. Both were
corrected, and both reruns passed.
The common polynomial shift, finite guarded clause and headline are now
one source unit, `AlgebraicResidueRoot`. Its first combined check exposed
rewrite visibility and encoded-zero conversions. The corrected source
passed under pinned Lean with exit zero and unchanged inputs, including
the full `lemma_7_4` assembly. Its source SHA-256 is
`c6e84570811a4f98747cad0019ba826861e47822f79ad1b824df9bb7692e85e5`.
The source log contains four style warnings and no errors. The later
entry-point and project-root checks are recorded below.

Theorem 7.6 and Corollary 7.7 were developed in separately checked modules.
They use actual partial residue Jacobians, two directions
of Lemma 7.2, finite definable gluing, the matched zero-coordinate cases,
the full labelled graph, and the Section 4 positive scissors quotients.
The surjectivity argument invokes the precise Section 5 representation
exports with the uniform obstacle hypothesis visible in both variants.
The general variant retains the dimensional presentation hypothesis;
the finite variant proves that presentation and finite-fibre invariance
in `LiftingPresentations.lean`, using the checked Section 4 finite-map and
refinement theorems. This module was checked separately. The
supporting `PolynomialCoordinateMaps` and `TupleCoordinates` source checks
passed with unchanged source and input hashes.

`PullbackLiftRelations` (the arbitrary-ambient version of Definition 7.3)
and `DefinableTupleQuantifiers` also passed pinned source compilation with
unchanged source and inputs. The pullback module is included in the 41-module
audit below. The tuple quantifier module supports the separate
`LiftingDefinability` check for Theorem 7.6.

## Lemma 7.4 and Definition 7.3 ambient extension verified

The 41-module entry-point check passed with 40 bound proof-module receipts
and 168 permitted axiom audits. The 137 earlier printed headlines are a
byte-identical prefix of the new log. The 31 added types and printed
definitions were reviewed in full. The fresh project-root check exited
zero with unchanged sources and inputs and no diagnostics.

`lemma_7_4` constructs the residue polynomial over the VF definable-closure
field of the original generated base. Its hypotheses are ACVF(0,0),
smallness in the saturated model, VF/Gamma generation, compatibility of
the valuation, nonzero coordinates, and algebraicity of the last RV
coordinate over the base and preceding coordinates. The conclusion includes
the failure of the last derivative to have a residue root at the shifted
residue value. The ambient extension of Definition 7.3 gives actual
bijections on specified fibres and identifies the canonical lift with the
preimage of its labelled companion.

The checkpoint is preserved in `.scratch/section7-74-certified/`.

- Certificate SHA-256 `b1027e66baf8bc2365df8127e07693749c6b55656750ad4701c4a6bc04c9c7d8`
- Statement review SHA-256 `5a4b093b03b548a3378c4edd21dd73a32c6c24e8c577b60601eaf60616940af8`
- Root receipt SHA-256 `0cfb52917a075a9a31951831cc68234c76a3e2f0dcf7512bc9416371e8be36d7`
- Archive index SHA-256 `6c6ffc29d8eecbaaec79f448beee8e91b22b1b4e178fe2bafc9592a37903bbc2`

## Theorem 7.6 verified

The 47-module entry-point check passed with 46 bound proof-module receipts
and 233 permitted axiom audits. The 168 earlier printed headlines are a
byte-identical prefix. All 65 added headline types and 15 printed
definitions were reviewed. The fresh project-root check exited zero with
unchanged source and inputs and no diagnostics.

`theorem_7_6` gives a VF-sorted lift definable over the real part of the
original small VF/Gamma-generated base in ACVF(0,0). Both directions of
the nonzero RV correspondence have finite fibres. The theorem supplies
actual bijections on the specified VF fibres. Its sorted companion
retains the explicit canonical-structure hypothesis. The local systems
use coefficients over the original VF base. Temporary Gamma codes occur
only in the finite-cover argument.

The checkpoint is preserved in `.scratch/section7-76-certified/`.

- Certificate SHA-256 `f138034696bdf5edcac392e2541121eec5094698200d100a26dd52570a52e2f3`
- Statement review SHA-256 `a2a8698edab3e11f3514b940b514705e5950c6f177f597c3b0de22e4f243c660`
- Root receipt SHA-256 `9bf3d99e7b8bd4d30df785ebd173d05932c124a41cfaba902dc5cb9c7687ff8c`
- Archive index SHA-256 `d28a2107c2327663e0abd04a9bbea4172842c30185d95b43b4441ba8ad484bef`

## Earlier Corollary 7.7 checkpoint with explicit surjectivity hypotheses

The final entry-point check covers 53 modules, including the reused
functional-relation constructor and the entry point itself. The audit
bound 52 proof-module receipts and passed all 276 axiom checks. The 233
earlier printed headlines are a byte-identical prefix. All 43 added
headline types and 13 printed definitions were reviewed. The final
project-root check exited zero with unchanged source and inputs and no
diagnostics.

The actual lift isomorphism preserves the original RV labels and is an
ambient lift of the companion graph. The positive quotient maps preserve
the canonical lift class. Both surjectivity statements are on the
normalized, fixed-degree positive Grothendieck quotients and retain the
previously accepted `UniformVerticalObstacles` input. The general statement
also retains the earlier dimensional presentation input. The finite
statement proves the required presentation and finite-fibre invariance.
The exact hypotheses are printed in the audit.

The final checkpoint is preserved in `.scratch/section7-77-certified/`.

- Certificate SHA-256 `3a7fddf5e4f202f4e7a80fcd4696356326ee995d2775c4b03d4fb51a493bbc92`
- Statement review SHA-256 `d6b6884c1c2f5fe91eec728613cf44723f33a75601ba5033dccc13a6c52474a6`
- Root receipt SHA-256 `10ab8839a11402dba4963d04ca3cb1f4e3ea65bc977852235d28e6abee11390b`
- Archive index SHA-256 `c1275800f543cb4e0ce5d353277779d5c3d33c821b142dee91f63c4971c5425b`

## Earlier verified RV/Jacobian bridge

Four new modules have passed the full pinned source/type/axiom verification:
`GammaPolynomialAlgebra`, `JacobianNormalization`, `SimpleRootNormalization`
and `IntegralNormalization`. They prove derivative/determinant closure,
the genuine simple-common-root predicate and its all-representative Jacobian
value, diagonal chain rule and scaling, simple-root and exact-solution
transport, and construction of the ordinary valuation-ring system with
zero residue and a unit Jacobian at the all-one point.

The expanded entry point passed eleven fresh module compilations and 64
headline type/axiom audits, with stable resolved imports and a combined
ACVF-QE import check. The separately compiled full-type review passed and
was inspected. The fresh project-root compatibility check also passed.
The previous seven-module/25-headline checkpoint is preserved with matching
sources in `.scratch/section7-before-jacobian-20261106/`. The four development
receipts are preserved in `.scratch/section7-jacobian-development/`.

## Assessment of the initial tree

Section 7 contained only relocated legacy files, without an integrated
library, a current section status, or a verifier. The old Hensel reduction
assumed its normalized Hensel conclusion; the old lifting reduction assumed
the key local lift; and the old Corollary 7.7 used underlying isomorphisms
and free monoids. None establishes the corresponding complete paper result
in the current shared-language library.

## Checked mathematical scope

| Module | Implemented scope | Verification state |
| --- | --- | --- |
| `GammaPolynomial.lean` | Finite monomial presentations, finite residue-value predicates, actual quotient RV fibres, power/product estimates, polynomial bounds and "some (hence all)" | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `PolynomialNormalization.lean` | Diagonal and scalar normalization, existence of a scalar from a nonzero polynomial term, equivalence of the original and normalized residue-root predicates | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `EncodedResidueRoots.lean` | Transport to the actual VF/RV sorts through the released `CanonicalRV.equiv` | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `LiftRelations.lean` | Definition 7.3 for full ambient VF powers, a genuine equivalence of each pair of fibres, its exact graph, restriction and the diagonal case | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `ValuationHenselian.lean` | Bridge from released monic root lifting over an algebraically closed field to the actual Mathlib henselian valuation ring | Fresh pinned compilation exit 0; full type reviewed and headline axioms allowed. |
| `Imported/EtaleLifting.lean` | Attributed Tau Ceti proof of existence of lifts of residue points of an etale algebra over a henselian local ring | Adapted source compiled freshly with exit 0; full type reviewed and headline axioms allowed. |
| `GammaPolynomialAlgebra.lean` | Closure under finite sums/products, signs, natural multiplicities and partial derivatives, retaining repeated monomials | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `JacobianNormalization.lean` | Genuine polynomial Jacobian, its residue value and exact value at every representative, row nonzeroness, diagonal chain rule and determinant scaling | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `SimpleRootNormalization.lean` | Common representatives and row scalars constructed in the field; simple-root iff, normalized Jacobian value one, and exact RV-fibre solution transport | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `IntegralNormalization.lean` | Actual valuation-ring polynomial system, coefficient bounds after cancellation, zero residue and unit Jacobian at the all-one point | Fresh pinned compilation exit 0; full types reviewed and headline axioms allowed. |
| `Imported/JacobianEtale.lean`, `PolynomialSystemEtale.lean` | Jacobian localization, the actual square-system quotient and etale algebra, exact points and coordinate evaluation | Fresh pinned compilation, type review and permitted axioms passed. |
| `Imported/UnramifiedUniqueness.lean`, `EtaleSections.lean` | Unramified diagonal uniqueness and the bijection of etale residue points with sections over a henselian local ring | Fresh pinned compilation, type review and permitted axioms passed. |
| `MultivariateHensel.lean` | A unique simultaneous zero in the given maximal-ideal congruence class | Fresh pinned compilation, type review and permitted axioms passed. |
| `GeneralizedHensel.lean`, `EncodedHensel.lean` | Lemma 7.2 on actual RV fibres and on the published VF/RV sorts | Fresh pinned compilation, type review and permitted axioms passed. |
| `Library.lean`, `verify.py` | Entry point, definition printing, fresh source compilation and complete resolved-import provenance | Full verifier exit 0: eighteen modules, 90 headline audits, stable import closure and combined ACVF-QE import. |

Lemma 7.2 is verified at the Section 7 and ACVF-QE library boundary.
The expanded entry-point and root checks verify Definition 7.1's residue
polynomial projection, the ambient and labelled instances of Definition 7.3,
Lemma 7.4, Remark 7.5, Theorem 7.6 and both Corollary 7.7 statements in the
scope above.

## Scope and hypotheses

The new elementary mathematics is over arbitrary fields with a Mathlib
valuation into a linearly ordered commutative group with zero. It retains
arbitrary finite tuple arities, including zero. Nonzero RV coordinates and
finite residue values are explicit. The scalar-existence theorem requires
a nonzero polynomial; the scalar-transport theorem displays its exact
valuation equation. No ambient value-group surjectivity is assumed.

The encoded bridge uses the actual released ACVF model, its VF/RV sorts and
a valuation realizing `VFValued.predV`, with the order reversal displayed.
It does not use a replacement language or a saturation assumption. Later
Section 7 results must retain the paper's pure-characteristic-zero, genuine
small-base saturation and (VF,Gamma)-generation hypotheses as applicable.
`valuationRing_henselian` assumes `IsAlgClosed K` and proves the actual
Mathlib `HenselianLocalRing` on the valuation ring. `residuePoint_lifts`
assumes the ordinary predicates `HenselianLocalRing R` and `Algebra.Etale R S`;
it is a generic existence result, with no RV or definable-lifting conclusion.
These predicates and the exported theorem hypotheses were inspected.
No new external mathematical hypothesis has been adopted.

The new Jacobian bridge requires no characteristic-zero, algebraic-closure,
henselian or saturation premise. Derivative multiplicities are repeated
summands; no integer valuation is assumed to equal one. The determinant's
gamma-polynomial structure and exact value at all representatives are proved
from the genuine simple-root predicate. All row nonzeroness and scalar
choices are derived. Collected normalized coefficients are only asserted
to have valuation at most one, preserving cancellation. The constructed
system belongs to the actual valuation ring, with its actual maximal ideal
and genuine ring-unit predicate. `multivariate_simpleRoot_lift` uses the
ordinary `HenselianLocalRing` instance and proves existence and uniqueness.
`generalized_hensel` derives that instance from algebraic closedness. The
encoded theorem derives algebraic closedness from the released ACVF model.

## Historical eleven-module verification evidence

The completed run freshly compiled ten proof modules and the audit entry
point under Lean 4.33.1. Every source compiler exit is zero, and all 64
exported headline types, explicit hypotheses and defining predicates were
reviewed. Their axiom lists contain only `propext`, `Classical.choice` and
`Quot.sound`. Four style-linter warnings remain in the polynomial and
normalization modules; complete diagnostics were inspected.

The portable command is `lake env python3 Section7/verify.py`, with earlier
compiled imports available on LEAN_PATH. This local invocation uses
`.scratch/section7-wait-run.py` and `.scratch/section7-env-run.py` to wait
for other checks and select the existing attested import copies. It does
not rebuild QE or re-certify earlier source proofs. The toolchain and
actual checkouts match Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
and ACVF-QE `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

The matching historical sources and evidence are preserved in
`.scratch/section7-jacobian-certified/`. In that checkpoint:

- `results.json` records fresh compiler commands, exits, source/log hashes
  and all split output artifact hashes. Adjacent per-module logs contain
  complete diagnostics; `Section7.Library.log` prints the full explicit types,
  defining predicates and all 64 axiom lists.
- `JacobianHeadlineReview.log` is the separately compiled readable full-type review;
  its receipt records exit zero. `JacobianStatementReview.json` binds the manual
  hypothesis and scope review to the exact source hashes.
- `import-providers.json` records Lean's resolved complete external compiled
  import closure (10,579 providers), including split artifacts. The before/after closure
  comparison passed. `integration.log` and `certificate.json` record the
  ACVF-QE + Section7 import check, exit zero, and its exact source/log hashes.
- `RootIntegration.json` and its empty `.log` record the expanded library's
  fresh project-root check: compiler exit zero, source unchanged, with actual
  LEAN_PATH and toolchain/manifest/Lake configuration hashes. It uses accepted
  compiled Section 3/4/5 libraries and does not re-certify their source proofs
  or claim a complete project source rebuild.
  Section 7 is registered explicitly in Lake and imported by the root;
  legacy Section 7 files are excluded. CI now has a separate Section 7 audit
  step and evidence retention, but no remote run is claimed.

An earlier seven-module run compiled successfully but its parser rejected
universe annotations in printed *allowed* axiom names. That run is preserved
in `.scratch/section7-first-full-run/`. The corrected seven-module checkpoint
and matching sources are archived separately. The current eleven-module
run passed independently with fresh source compilation. The parser removes
only universe instantiations before comparing exact constant names against
the unchanged three-axiom allowlist.

The successful certificate's SHA-256 is
`27cf034546a5095741101325944282f195d8920495d82d493f3e83a81ea03ad5`.
It binds the exact eleven source identities, compiled output hashes, import
manifest, per-module results, full headline log, integration check and
verifier identity. The headline log's SHA-256 is
`ae0347f36d37008bcad28d355b7ad8c2503fae8fe1c0ab837be48bcd28e035ef`.
The fresh root receipt's SHA-256 is
`5df6073f5b8a02e58501d208b5488c60486f3b601802c8554f78d362e6314276`;
its checked root source identity is
`4264faf0ac3849b741fc33a51b2ba59557e51ee571b8d7c3a5224c22f94d2b09`.

The earlier WSL connection timeout recovered without intervention. Read-only
evidence is in `.scratch/wsl-diagnostics-2026-11-06/`: VMBus high-order
allocation failures preceded socket-accept timeouts while existing jobs
continued. No Linux service or proof job was stopped or restarted. The
Section 4/6 heavy checks finished naturally before these compiler runs;
the launcher waited for their complete runners, including gaps between jobs.

The numbered targets in TARGETS.md are verified in the recorded scope.
PLAN.md and REUSE-SURVEY.md record the mathematical route and earlier
interfaces.

Existing edits and all legacy files have been preserved. No commit or push
has been performed.
