# Section 5 handoff

The November 7 real-parameter repair is in [Surjectivity.lean](Surjectivity.lean).
It discharges the three premises of the published Corollary 5.7 with
the checked vertical-obstacle relation, dimensional presentation and
finite-fibre transport. It uses the actual Gamma quotient in the
dimension definition. [GammaSurjectivity.lean](GammaSurjectivity.lean)
proves the general and finite versions over the original base with named
Gamma values. It uses the paper's VF coefficient-field convention.
`GammaDimension` starts from the graph of an actual finite-to-one map
to VF, RV and Gamma coordinates. `GammaDimensionalPresentation` uses
its rank bound to obtain a same-base mixed presentation.
`GammaFiniteFibres` transports finite fibres along a same-base
isomorphism. The full types and axioms are in
`.scratch/section5-repair-gamma-final-root.log`.
See [STATUS.md](STATUS.md) and the [publication audit](../PUBLICATION-AUDIT.md).

The published Section 5 checkpoint verifies conditional Lean statements.
Corollary 5.7 still assumes uniform vertical obstacles and a dimensional
presentation. Its published finite variant also assumes finite-RV-fibre
invariance. These are formalization obligations needed to recover the
paper's statement. See [STATUS.md](STATUS.md) and [INPUTS.md](INPUTS.md).

The November 6, 2026 checkpoint is published in
[`21cff13`](https://github.com/daviddhilbert/special-transformations/commit/21cff13d8f9beb28e6ed84e04242e9deae875cb6),
so Section 6's dependency is available remotely. Its passing CI is recorded below.
The active entry point is Section5.Library; Sec5.lean and LegacyScaffold
remain unimported historical references.

The author confirmed on November 6, 2026 that all material through Section 6
has been pushed. Continue with Section 7 using the published earlier sections.

## Scope and inputs

The library constructs RV-pullbacks, canonical maps, focus transformations,
alternating special bijections, contractions, finite-root and VF-dimension
inductions, Theorems 5.4–5.5 and Corollaries 5.6–5.7. It retains arbitrary
finite mixed arities, initial chains and original real or named-Gamma bases.
The category results use actual Section 4 objects and lifts.

ZeroNormalization supplies equivalent nonzero-active representatives with
the same maps, inverses, endpoints, length, alternation and parameters. It
proves the printed disjoint C-sharp target for those representatives; it
does not claim the old zero-active printed clause is true.

The explicit earlier inputs include uniform vertical obstacles, invariant
Gamma logic, finite polynomial support and finite presentation
specialization, and the earlier dimensional-reduction and finite-fibre
consequences used in the category exports. Their precise scopes are in
INPUTS.md and the printed library audit. No Section 5 existence theorem,
normalization conclusion or special-bijection construction is assumed.

## Verification

The completed pinned Lean 4.33.1 check passed 28 modules and 282 full
headline type/axiom audits. Twenty-six unchanged source-compiled modules
were re-certified by an ordered kernel replay of 1,186 declarations against
the accepted earlier environment. ZeroNormalization and Library were
freshly compiled. A separate consumer check constructed normalized real
and Gamma Corollary 5.6 witnesses and passed 39 audits with compiler exit 0.
Only propext, Classical.choice and Quot.sound occur in the headline axioms.
This is not a claim that all 28 modules were freshly elaborated together.

The immutable local checkpoint is `.scratch/section5-checkpoint282/`.
It preserves exact sources, original compiler receipts, replay evidence,
provider/cache identities, full types and axioms, and consumer results.
The publication checks that its Lean source bytes match that certificate.
Section 6's completed 78-module/444-headline combined check also imported
this Section5.Library. Earlier sections were accepted as given, not rebuilt.

The publication additionally checked the updated coordination-root import
with compiler exit 0 using the accepted earlier compiled artifacts. All 28
published Lean source bytes and 77 earlier source identities matched their
records; the four shared cache tests passed for both Sections 4 and 5.

## Published checkpoint and passing CI

The [main-branch verification run 42303485856](https://github.com/daviddhilbert/special-transformations/actions/runs/42303485856)
for published commit `21cff13d8f9beb28e6ed84e04242e9deae875cb6`
completed **successfully on November 6, 2026** (America/Los_Angeles).
The pinned project source build, compiled-import cache provenance checks,
published QE headline audit, and Section 3, Section 4 and Section 5 verifiers
all ran and passed. Compiler logs, provider manifests and headline audits
are retained in the run's verification artifact.

All 28 published Section 5 Lean source files match the local certificate
byte for byte. This supplies passing CI source-build and Section 5 audit
evidence alongside the local replay and consumer checks above. The CI result
applies to the named published commit; later documentation updates require
their own run when published.

That checkpoint supplies the published conditional `Section5.Library`
used by Section 7. The current real-parameter repair and the remaining
named-Gamma work are recorded above.

## Reuse and publication

Use `lake env python3 Section5/verify.py` with the accepted earlier compiled
interfaces on the import path. The verifier records actual resolved compiled
providers, source and artifact identities, cache/replay provenance and full
headline audits. The repository workflow includes the Section 5 audit and
preserves the existing Section 4 and Section 5 cache-regression coverage.
The passing remote run is linked above; local workflow checks are recorded
separately in STATUS.md.

Section 6's earlier separate publication is commit 4f93a69. The published
Section 5 checkpoint supplies its source dependency. Preserve unrelated
workspace edits. Further publication requires a new explicit instruction.
