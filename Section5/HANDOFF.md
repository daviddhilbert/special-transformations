# Section 5 handoff

Updated November 6, 2026. Section 5 is complete within the explicit accepted
Sections 2–4 inputs in INPUTS.md. The author authorized committing and
pushing this checkpoint so Section 6's dependency is available remotely.
The active entry point is Section5.Library; Sec5.lean and LegacyScaffold
remain unimported historical references.

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

## Reuse and publication

Use `lake env python3 Section5/verify.py` with the accepted earlier compiled
interfaces on the import path. The verifier records actual resolved compiled
providers, source and artifact identities, cache/replay provenance and full
headline audits. The repository workflow includes the Section 5 audit and
preserves the existing Section 4 and Section 5 cache-regression coverage.
Local workflow checks do not imply a completed remote Actions run.

Section 6's earlier separate publication is commit 4f93a69. This Section 5
publication supplies its missing source dependency. There is no remaining
Section 5 proof obligation within the displayed accepted-input scope.
Preserve unrelated workspace edits; further publication requires its own
authorization.
