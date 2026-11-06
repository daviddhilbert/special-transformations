# Section 4: dimensions and categories

The active entry point is [Library.lean](Library.lean). The library covers VF
and RV dimensions, definable categories, canonical lifts, positive scissor
quotients, and their Grothendieck group and ring constructions. The exact
checked scope, standing premises and verification record are in
[STATUS.md](STATUS.md).

Sections 2--3 are completed in the scope recorded by the
[Section 3 handoff](../Section3/HANDOFF.md). Section 4 uses those checked
interfaces without rebuilding their proofs. QE and
the common language are supplied by the pinned ACVF-QE dependency. See the
[target checklist](TARGETS.md), [plan](PLAN.md), [accepted inputs](INPUTS.md),
and [reuse survey](REUSE-SURVEY.md). The shared
[Section 3 handoff](../Section3/HANDOFF.md) records earlier context.

With the accepted earlier-section artifacts available in the Lean import
path, run `lake env python3 Section4/verify.py` in the pinned Lake project.
The verifier builds the active Section 4 sources, records full headline
types and axiom lists, and checks the QE import and project root. Explicit
hypotheses must also be inspected; a clean axiom list does not discharge
them. Earlier sections are neither rebuilt nor audited by this verifier.
The published coordination root imports the completed QE, Section 3 and
Section 4 libraries. Compiled caches are bound to the actual import providers,
including split module parts and interpreter code.

## Legacy snapshots

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

The legacy snapshots are excluded from the active entry point. The plan
records the proof milestones and acceptance criteria for the new library.

Old paths and exact initial content hashes: `../Archive/MOVE-INDEX.json`.
Static imports/placeholders: `python3 Archive/inspect_legacy.py --inventory`.
