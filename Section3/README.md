# Section 3 and remaining Section 2 preliminaries

Start with [STATUS.md](STATUS.md), then [TARGETS.md](TARGETS.md).
The original [HANDOFF.md](HANDOFF.md) records the starting constraints.

This is a subdirectory of `special-transformations`, not a separate repository.
The scope is all of Section 3 plus everything in Section 2 after
the QE statement. QE is complete in the pinned ACVF-QE dependency.

Existing section-related Lean files have been moved here from `QE/`;
`Balls.lean` came from `Milestone0/`. `LegacyScaffold/` contains earlier stubs.
The initial relocation preserved their contents byte for byte. A subsequent
audit compiled the 24 top-level legacy snapshots and their nine local
dependencies under their historical staging names. Eight misleading legacy
comment blocks have since been corrected without changing proof code.

The new checked library starts at [Library.lean](Library.lean), which imports
only new audited modules and the pinned ACVF-QE definitions. It includes
base-relative closure and compactness infrastructure, exact C-minimality,
sorted tuple descent, ball and coordinate interfaces, results 3.8–3.12, 3.15, 3.18(1), the closed-ball alternative of 3.18(2), and
quotient-family notation. Finite coding preserves the original parameter base
and includes its complete graph in all VF tuple arities. Closed-ball centers
are defined on the actual ball quotient over the same original base. Definable
points use a nonempty proper subset without naming the containing ball.
Uniform polynomial support also proves finite RV-fibre exceptions. Lemma 3.15
uses the actual Gamma quotient and preserves the original base. A separate audit
records the {1,-1} obstruction to the unrestricted classification in Remark 3.19;
the author has [retracted the whole remark](RETRACTIONS.md), which is excluded
from the remaining proof obligations. Additive subgroups are proved to be balls,
and the uniform root set gives the finite exceptional additive cosets in 3.18(1).
The closed-ball alternative of 3.18(2) includes the complete original-base
quotient graph and a realizing representative in every class. The entry point
does not certify every item in the section. See [STATUS.md](STATUS.md) for the
exact hypotheses and the remaining work.

After building dependencies, run `lake env python3 Section3/verify.py` for the
new library or `lake env python3 Archive/audit_section3.py` for the isolated
legacy compiler audit. Neither script pushes anything.

See [LEGACY.md](LEGACY.md) for reuse candidates and pitfalls, and
`../Archive/MOVE-INDEX.json` for the complete old-to-new path map.
