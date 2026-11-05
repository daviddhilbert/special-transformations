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
dependencies under their historical staging names. Four misleading legacy
headers have since been corrected without changing proof code.

The new checked library starts at [Library.lean](Library.lean), which imports
only new audited modules and the pinned ACVF-QE definitions. It includes
base-relative closure and compactness infrastructure, sorted tuple descent,
ball and coordinate interfaces, Lemma 3.8 and quotient-family notation. It
does not certify every item in the section. See [STATUS.md](STATUS.md) for the
exact hypotheses and the remaining work.

After building dependencies, run `lake env python3 Section3/verify.py` for the
new library or `lake env python3 Archive/audit_section3.py` for the isolated
legacy compiler audit. Neither script pushes anything.

See [LEGACY.md](LEGACY.md) for reuse candidates and pitfalls, and
`../Archive/MOVE-INDEX.json` for the complete old-to-new path map.
