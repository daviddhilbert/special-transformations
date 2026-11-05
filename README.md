# Special transformations in algebraically closed valued fields

Yimu Yin, APAL (2010), [arXiv:1006.2467](https://arxiv.org/abs/1006.2467).

This repository is now a thin coordination project for formalizing the paper
section by section. The completed ACF/ACVF/RV quantifier-elimination proofs
live in [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE), pinned here at
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

## Continue here

Read [Section3/HANDOFF.md](Section3/HANDOFF.md) in the next session. Its scope
is **all of Section 3 and the material in Section 2 after Theorem 2.3**.
QE is finished and is a dependency of this work.

| Folder | Scope |
| --- | --- |
| [Section3/](Section3/README.md) | Next task; structural properties and remaining Section 2 preliminaries |
| [Section4/](Section4/README.md) | Dimensions, definable categories, and Grothendieck constructions |
| Section5/ | RV-pullbacks and special bijections |
| Section6/ | Henselian-field QE and descent |
| Section7/ | Lifting functions |
| Section8/ | Further structural properties |
| Section9/ | Differentiation |
| Section10/ | Categories with volume forms |
| [Archive/](Archive/README.md) | Older QE campaign, model-building snapshots, scaffolds, and historical notes |

The relocated section files are **legacy candidates**, not a new verified
section library. Their proofs, hypotheses, and old headers need auditing
against the paper. No Section 3 or Section 4 completion is claimed.

## Build and inspect

Lean 4.33.1 and the matching Mathlib revision are pinned. `lake build` builds
the coordination root, which imports the completed `ACVFQE` library. Legacy
section snapshots are deliberately not imported into that root automatically.

```sh
lake exe cache get
lake build
python3 Archive/inspect_legacy.py --check-moves
python3 Archive/inspect_legacy.py --plan Section3/Sec3Fibre.lean
```

[Archive/MOVE-INDEX.json](Archive/MOVE-INDEX.json) records original paths,
new paths, and SHA-256 hashes. The reorganization preserved every moved file
byte for byte. Old paths and build instructions inside historical comments
can be resolved through that index. The earlier Makefile and project config
are preserved under `Archive/History/`.

The new root import and QE headline audits passed under the pinned Lake
environment using existing checked dependency artifacts. See
[cleanup checks](Archive/REORGANIZATION-CHECK.json) for the precise scope;
the legacy section proofs were not recompiled during this reorganization.

The section folders are ordinary subdirectories of this repository. No nested
Git repository or submodule was added. The author chose this layout over the
newer OpenMathOS changes; the pre-cleanup remote tip is retained on
`codex/pre-section-layout-06c840f` and in the merge history.

## License

Project code retains the MIT license declared by the original project.
External code retains its own notices; ACVF-QE includes an attributed
Apache-2.0 ultrapower adaptation. Preserve those notices when reusing it.
