# v1.1: Weighted measured degree zero

This release includes checked proof commit
`d7d74197031665b4c1e9ea4486c1898ff32f2d50` and the accompanying blueprint,
source-link, verification and release-record updates. The release documentation
changes no Lean source or dependency pin relative to that proof commit.

## Mathematical change

The corrected zero categories retain actual same-base nonzero RV forms or
actual Gamma forms. Zero isomorphisms preserve the exact weight at every point;
the empty-coordinate determinant is one. The VF zero category retains the full
ordinary dimension-zero family, including arbitrary mixed presentations.
The ordinary zero categories remain available separately.

The RV and Gamma zero versions of 10.4–10.6, form-preserving lift, restrictions,
weighted scissors, additive generator formula and surjectivity are implemented.
Neutral forms recover ordinary zero **isomorphisms**, and product formulas
retain both densities, including zero-degree factors. The all-degree categories
now use the appropriate weighted zero family.

Positive-degree indices still mean degree `k + 1`. Their existing APIs and
hypotheses are preserved. The generic `RVInDegree`/`RVDegreeCoproduct` assembly
now takes an explicit zero object family; downstream code using that assembly
must supply the correct RV, Gamma or neutral-form zero category.
See the [exported interfaces](../Section10/HANDOFF.md).

This is the adopted HK measured-zero convention within the existing
finite-volume scope. No HK theorem or definable Gamma-to-RV section is assumed.
The existing positive-degree `FiniteHenselianExtensionReference` and the
separate Section 8 reference package remain explicit. The new zero results add
no such reference premise.

## Verification

The proof and release sources use Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and ACVF-QE
`939346b0a99899e22a873479364e3cc5d142731c`. All ten dependency checkouts match
the manifest and have clean tracked source trees.

The complete project root build and the Section 10 build passed. The Section 10
suite checks 68 paired full headline types/axiom reports, with a separate
explicit-type/definition inspection. Every configured suite passed using
`scripts/verify_ci.py all`: QE and Sections 3–10, with 3,582 headline axiom
reports. The available independent source verifiers for Sections 3, 4, 5 and 7
passed with 199, 237, 40 and 55 fresh compilation receipts respectively,
including their generated integration/audit modules. No receipt was reused.
The final results and counts are recorded in
[verification/v1.1.json](verification/v1.1.json).

The complete active project closure has 902 source modules, is acyclic, and
contains no `sorry`, `admit` or custom `axiom` declarations. The axiom allowlist
is `{propext, Classical.choice, Quot.sound}`. The cache-provenance regression
tests, QE module-registration check and archive move/hash integrity check also
pass. Existing import-style, tactic and deprecation warnings are distinguished
from compiler errors and proof placeholders.

An [independent automated source/statement review](verification/independent-review-v1.1.md) confirms all six grouped
errata and seven deviations in the
[release record](ERRATA-AND-DEVIATIONS.md), including its links, actual Lean
certificates, documented counterexamples and their limits. That review is not
an exhaustive semantic re-reading of every theorem in the project. The full
build and axiom audits likewise do not remove explicit mathematical hypotheses
or certify inactive legacy snapshots.

## Blueprint

The updated web blueprint has 57 nodes and 136 distinct linked Lean declarations.
All linked types and axiom reports pass a fresh check, all source-line anchors
are refreshed against the checked proof tree, and the dependency graph is
acyclic. The web HTML and 57-node clickable SVG render successfully and the
Section 10 page has been visually inspected. Optional local LaTeX/image-tool
warnings do not affect this images-disabled MathJax web build; no new PDF-build
certificate is claimed. Lean source links pin the proof commit above;
repository-document links use the immutable release tag `v1.1`.

The release verification asset contains source fingerprints and the selected
build, type/axiom, provenance and independent-review evidence. It contains no
compiled build cache, authentication material or private machine paths.

## Reproduce

Use Python 3.11 or newer for `scripts/prepare_ci.py`, and the pinned Lean/Lake
environment. Follow the repository setup and blueprint instructions, then run:

```sh
lake exe cache get
python3 scripts/prepare_ci.py
python3 scripts/test_lean_provenance.py
lake -R build
lake env python3 scripts/verify_ci.py all
python3 Archive/inspect_legacy.py --check-moves
leanblueprint web
```

The historical v1.0 release remains intact. No sequel dependency pin or
integration implementation is changed by this release. RES, pure value-group
measured categories, tensor decompositions, and the sequel's integration
kernel, normalization and function integration remain outside this repository's
agreed scope.
