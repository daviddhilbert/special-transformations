# v1.2: Shared foundation and Gamma lifts

This release includes checked proof commit
`932a5075ad91a825d4b8c1bf1396b2063e44fe40` and the accompanying blueprint,
source-link, errata, verification-script pin and release-record updates. The
release commits change no Lean source or dependency pin relative to that proof
commit. It covers the 15 commits after v1.1 (`25852c8`).

## Changes since v1.1

**Shared foundation.** The project now consumes 22 shared modules and 35
generic helpers from the pinned
[hilbert-mathlib](https://github.com/daviddhilbert/hilbert-mathlib) dependency.
Fifty-seven original module paths remain as compatibility imports; declaration
names, universes and mathematical statements are unchanged. [SHARED-FOUNDATION.json](../SHARED-FOUNDATION.json)
records the providers and source fingerprints. The Gamma QE prerequisites are
published through the additional default target `SpecialTransformationsGammaQE`
with preserved public types; [PROMOTED-FOUNDATIONS.json](../PROMOTED-FOUNDATIONS.json)
records their original statements and axiom inventories. ACVF-QE is now pinned
at `173708265d7959e031bf9552ee884501fc21f2cb`. A CI bootstrap fix downloads Lean
from the official release URL, with the same checksum.

**Input-free Theorems 5.4/5.5 over a Gamma-named base.**
`Section5.Paper.theorem_5_4_gamma`, `theorem_5_5_gamma` and
`theorem_5_5_finite_gamma` in [GammaPaper.lean](../Section5/GammaPaper.lean)
assume only saturation, a small real base and the paper's VF/Gamma-generated
base. The `*_of_fieldBase` forms assume instead that the VF part of the real
base is a field. They discharge the three inputs of the conditional forms in
`Section5/GammaExistence.lean`.

**Gamma lift layer (additive).** Over a VF/Gamma-generated base:

- Gamma-definable total mixed Jacobians:
  `gamma_total_mixed_jacobian_graph` and `gamma_exists_totalMixedJacobianMap`.
- The Gamma-definable lift Jacobian discrepancy (Lemma L):
  `GammaLift.gamma_liftJacobian_discrepancy`.
- Gamma certificates for RV objects and the Gamma weighted lift; Gamma
  restriction, gluing, label representatives and affine lifts.
- Finite-head and reindexed-head prescribed lifts, the Gamma rank bound
  `GammaLift.gamma_rank_le_rvDim`, head covers and disjoint refinements.
- Gamma Theorem 9.16, `GammaLift.gamma_theorem_9_16_finite_volume`: when the
  volume maps, isomorphism and prescribed form have Gamma graphs, the
  prescribed-Jacobian lift can be chosen with a Gamma graph. It takes the same
  `HenselizedGaussGraphInput` as the real-parameter positive-arity theorem.

Existing statements are unchanged. integration-in-ACVF's Gamma-named Section 7
uses this layer without its former `hNames` hypothesis.

**Records.** The provider audit of November 18, 2026 corrected stale records
and documented statement scope; the author confirmed that the trivially valued
case of Theorem 2.8 is out of scope. These are now in the
[errata and deviations record](ERRATA-AND-DEVIATIONS.md) (Deviations 5 and 7)
and the [README notes on statements](../README.md#notes-on-statements). The
grouped counts remain 6 errata and 7 deviations.

## Verification

The proof and release sources use Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, ACVF-QE
`173708265d7959e031bf9552ee884501fc21f2cb` and hilbert-mathlib
`88bb3386f616779bfd87eb453d8a7c899ad63961`. All eleven dependency checkouts
match the manifest and have clean tracked source trees.

The complete project root build (`lake -R build`, both default targets)
completed successfully with 10,140 jobs and no `sorry` warning. It was an
up-to-date build: Lake replayed existing local artifacts whose traces match the
checked sources, rather than recompiling them. The independent section source
verifiers below compile their modules afresh.

Every configured suite passed using `lake env python3 scripts/verify_ci.py all`:
QE and Sections 3–10, with **3,607 headline axiom reports**: QE 8, Section 3
1,393, Section 4 968, Section 5 307, Section 6 483, Section 7 279, Section 8 47,
Section 9 54 and Section 10 68. Relative to v1.1's 3,582, the additions are
`Section4.Paper.lemma_4_13` (1), the six input-free Section 5 forms (6) and the
Gamma lift layer in Section 9 (18). The available independent source verifiers
for Sections 3, 4, 5 and 7 passed with 199, 237, 41 and 55 fresh compilation
receipts respectively, including their generated integration/audit modules.
No receipt was reused. Before this run, the Section 6 and Section 7 verifiers
were updated to expect the current ACVF-QE pin; they had still named the v1.1
revision. That release-time commit changes no Lean source. GitHub Actions also
passed the pinned build and CI audits at the proof commit
([run 44603383165](https://github.com/daviddhilbert/special-transformations/actions/runs/44603383165)).
The final results and counts are recorded in
[verification/v1.2.json](verification/v1.2.json).

`scripts/verify_promoted_foundations.py` confirms 48 unchanged promoted public
types and their axioms in 10 modules. The shared-foundation check confirms the
exact provider pin and source provenance of the 57 compatibility imports.

The active project closure from the two default roots has 932 source modules
(921 from `SpecialTransformations`), is acyclic, and contains no `sorry`,
`admit` or custom `axiom` declarations. Its fingerprints are in
[source-manifest-v1.2.json](verification/source-manifest-v1.2.json). The axiom
allowlist is `{propext, Classical.choice, Quot.sound}`. The cache-provenance
regression tests (4), the QE module-registration check (85 modules) and the
archive move/hash integrity check also pass. Existing import-style, tactic and
deprecation warnings are distinguished from compiler errors and proof
placeholders.

No new independent automated review was produced for this release. The v1.1
[review](verification/independent-review-v1.1.md) was an automated agent
review with no scripted procedure in the repository, so it cannot be
repeated mechanically. The v1.2 record keeps the six errata and seven
deviations reviewed there and adds the scope notes above; those additions have
not been independently re-reviewed. The build and axiom audits do not remove
explicit mathematical hypotheses or certify inactive legacy snapshots.

## Blueprint

The blueprint now has 63 nodes and 158 distinct linked Lean declarations.
New nodes cover the input-free named-Gamma Theorems 5.4/5.5, the Gamma total
mixed Jacobian, the Gamma lift Jacobian discrepancy, the Gamma weighted lift
and gluing, the Gamma rank bound, head covers and prescribed lifts, and Gamma
Theorem 9.16. The Theorem 5.4 node now links only the paper form; the
conditional named-Gamma form is replaced by the input-free node.

All 158 linked types and axiom reports pass a fresh check, and the dependency
graph is acyclic. Every source anchor was regenerated and then checked to point
to its declaration line: 156 in this repository at the proof commit, one in
ACVF-QE and one in hilbert-mathlib (`Section4.lemma_4_23`, whose implementation
moved there). The v1.1 anchors had drifted: 124 of 137 pointed a few lines
before or after their declaration, because the v1.1 refresh stripped block
comments without keeping line breaks. Repository-document links use the
immutable release tag `v1.2`.

The web blueprint was not rendered locally: `leanblueprint`, plasTeX and
Graphviz are not installed on the release machine. The blueprint workflow
builds and publishes it on push to `main`. No PDF-build certificate is claimed.

The release verification asset contains source fingerprints and the selected
build, type/axiom, provenance and blueprint-audit evidence. It contains no
compiled build cache, authentication material or private machine paths.

## Reproduce

Use Python 3.11 or newer for `scripts/prepare_ci.py`, and the pinned Lean/Lake
environment. Follow the repository setup and blueprint instructions, then run:

```sh
lake exe cache get
python3 scripts/prepare_ci.py
python3 scripts/check_shared_foundation.py
python3 scripts/test_lean_provenance.py
lake -R build
lake env python3 scripts/verify_ci.py all
python3 scripts/verify_promoted_foundations.py
python3 Archive/inspect_legacy.py --check-moves
leanblueprint web
```

The historical v1.0 and v1.1 releases remain intact. RES, pure value-group
measured categories, tensor decompositions, and the sequel's integration
kernel, normalization and function integration remain outside this
repository's agreed scope.
