# Section 3 and remaining Section 2 preliminaries

Start with [HANDOFF.md](HANDOFF.md), then [TARGETS.md](TARGETS.md).

This is a subdirectory of `special-transformations`, not a separate repository.
The next session's scope is all of Section 3 plus everything in Section 2 after
the QE statement. QE is complete in the pinned ACVF-QE dependency.

Existing section-related Lean files have been moved here from `QE/`;
`Balls.lean` came from `Milestone0/`. `LegacyScaffold/` contains earlier stubs.
All moved contents were preserved byte for byte. Their old headers are historical
and their imports still use the old staging names. They have not been freshly
compiled or integrated as a Section 3 library during this cleanup.

See [LEGACY.md](LEGACY.md) for reuse candidates and pitfalls, and
`../Archive/MOVE-INDEX.json` for the complete old-to-new path map.
