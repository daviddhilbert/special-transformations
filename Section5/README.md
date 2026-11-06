# Section 5: RV-pullbacks and special bijections

The active shared-language library is [Library.lean](Library.lean).
Its paper coverage and compiler evidence are recorded in [STATUS.md](STATUS.md),
with the [target checklist](TARGETS.md), [accepted earlier inputs](INPUTS.md)
and [reuse survey](REUSE-SURVEY.md). The [handoff](HANDOFF.md) records the
completed scope and how to use this dependency from later sections.

The November 6 normalization resolves the zero-fibre codomain issue in
Definition 5.1. Every transformation has a representative with nonzero active
loci and the same endpoints, maps, inverses, length, alternation and parameters.
The printed C-sharp target and disjointness are proved for those representatives.
CI now runs the Section 5 audit, and cache reuse binds the actual compiled import
providers and their identities. See STATUS.md for the completed checks and scope.

The author permits all needed material from Sections 2–4 as given.
The new library keeps unfinished earlier interfaces explicit and constructs
Section 5's transformations and existence proofs. It includes the finite
VF-dimension induction, exact polynomial theorems, both lift variants,
and full invariant graphs over actual named-Gamma bases. The 28-module checkpoint
and all 282 headline audits passed. It combines 26 kernel-recertified matching
source-compiled modules with fresh normalization and library compilations; see
STATUS.md for the exact scope and evidence.

The standalone `Sec5.lean` and `LegacyScaffold/` remain reference snapshots.
They are not imported. Their duplicate RV implementation, identity canonical
map and statement-only main results are not the foundation of this library.
The active code uses the pinned ACVF-QE language and shared sorts, canonical
maps that append labels, and full original-base definability.

See `../Archive/MOVE-INDEX.json` for historical paths and initial hashes.
