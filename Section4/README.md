# Section 4: dimensions and categories

Existing files have been moved here from `QE/`, unchanged:

- `Sec4Dim`, `Sec4DimACFModel`, `Sec4FibreDim`, `Sec4Polydisc`, `M6Polydisc`:
  dimension and polydisc candidates and test models.
- `Sec4Categories`, `Sec42Morphism`, `Sec4EK`, `Sec4Pair`, `Sec4Rename`:
  category, morphism, embedding-functor and definable-pairing candidates.
- `Compose`, `Fibre`, `Proj`: definable-function composition, fibre transport,
  and projection infrastructure, also potentially useful to other sections.
- `LegacyScaffold/`: the earlier Dimension and Categories stubs.

These are legacy source snapshots, not a new verified Section 4 library.
Their imports retain the historical staging names, and their hypotheses and
historical headers must be audited before reuse. In particular, do not replace
definable functions by arbitrary functions in dimension witnesses, or infer
that a conditional decomposition/straightening statement has been proved.

The next active task is [Section 3 plus the Section 2 remainder](../Section3/HANDOFF.md).
Read that handoff first; Section 4 work will follow. QE is already provided by
the pinned ACVF-QE dependency. The whole-section acceptance checklist and fresh
proof integration remain for a later Section 4 session.

Old paths and exact initial content hashes: `../Archive/MOVE-INDEX.json`.
Static imports/placeholders: `python3 Archive/inspect_legacy.py --inventory`.
