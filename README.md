# Special transformations in algebraically closed valued fields

Yimu Yin, APAL (2010), [arXiv:1006.2467](https://arxiv.org/abs/1006.2467).

This repository is now a thin coordination project for formalizing the paper
section by section. The completed ACF/ACVF/RV quantifier-elimination proofs
live in [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE), pinned here at
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

The RV QE result uses the corrected language with a named RV inverse. The
author confirmed that the omission of inverse symbols before Convention 2.5
requires this correction to the paper's language specification; it was not
only a Lean transcription error. See [language erratum](LANGUAGE-ERRATA.md).
This affects the QE formulation, not the later definable-set theory: inverse
is already definable, so naming it does not change the definable sets.

## Continue here

Read [Section3/HANDOFF.md](Section3/HANDOFF.md) in the next session. Its scope
is **all of Section 3 and the material in Section 2 after Theorem 2.3**.
QE is finished and is a dependency of this work.

| Folder | Scope |
| --- | --- |
| [Section3/](Section3/README.md) | Next task; structural properties and remaining Section 2 preliminaries |
| [Section4/](Section4/README.md) | Dimensions, definable categories, and Grothendieck constructions |
| [Section5/](Section5/README.md) | RV-pullbacks and special bijections |
| [Section6/](Section6/README.md) | Henselian-field QE and descent |
| [Section7/](Section7/README.md) | Lifting functions; checked foundations, main lifting results open |
| Section8/ | Further structural properties |
| Section9/ | Differentiation |
| Section10/ | Categories with volume forms |
| [Shared/](Shared/README.md) | Seven syntax/parameter helpers required by the section code |
| [Archive/](Archive/README.md) | Remaining model-building snapshots and limited historical evidence |

The active Section 3 and Section 4 libraries have their own
[Section 3 entry point](Section3/Library.lean), [Section 3 status](Section3/STATUS.md),
[Section 4 entry point](Section4/Library.lean) and [Section 4 status](Section4/STATUS.md).
Their status records distinguish the paper statements, standing premises
and verified scope from the legacy snapshots.

Section 5 has a shared-language [entry point](Section5/Library.lean),
[coverage and verification record](Section5/STATUS.md), and explicit
[earlier inputs](Section5/INPUTS.md). It includes both real and named-Gamma
forms of Corollary 5.7.

Section 6 has a separate [entry point](Section6/Library.lean) and
[status](Section6/STATUS.md). The [paper exports](Section6/PaperResults.lean)
give named-base Proposition 6.4 and Denef–Pas Corollary 6.5 with the
representation and saturation arguments supplied by proofs.

Section 7's [entry point](Section7/Library.lean) includes the RV/Jacobian
bridge and the lifting results through Corollary 7.7. The general and
finite surjections include named-Gamma forms. See [Section 7 status](Section7/STATUS.md).

Section 8 has a separate [entry point](Section8/Library.lean) and
[status](Section8/STATUS.md) covering its structural results and recording
their exact scope, including the explicit henselization inputs.

## Build and inspect

Lean 4.33.1 and the matching Mathlib revision are pinned. `lake build` builds
the coordination root, which imports the completed `ACVFQE` library and the
Section 3 through Section 8 entry points. Legacy
section snapshots are deliberately not imported into that root automatically.

```sh
lake exe cache get
lake build
python3 Archive/inspect_legacy.py --check-moves
python3 Archive/inspect_legacy.py --plan Section3/Sec3Fibre.lean
```

[Archive/MOVE-INDEX.json](Archive/MOVE-INDEX.json) records original paths,
new paths, SHA-256 hashes, and retention/removal status. After the initial
reorganization, the author requested deletion of the obsolete QE campaign.
Of the 93 retained entries, 85 still match their original bytes and eight have
documented comment-only corrections in `Archive/LEGACY-REVISIONS.json`; 243 obsolete entries
were removed, including the duplicate encoding and old QE planning material.
Seven required legacy helpers are retained in `Shared/`. Completed QE code is supplied
by the pinned ACVF-QE dependency, rather than duplicated in this repository.

The new root import and QE headline audits passed under the pinned Lake
environment using existing checked dependency artifacts. See
[cleanup checks](Archive/REORGANIZATION-CHECK.json) for the precise scope;
the legacy section proofs were not recompiled during this reorganization.

The section folders are ordinary subdirectories of this repository. No nested
Git repository or submodule was added. The author chose this layout over the
newer OpenMathOS changes. Earlier commits remain recoverable from Git history;
their obsolete QE files are not part of the current source tree.

## License

Project code retains the MIT license declared by the original project.
External code retains its own notices; ACVF-QE includes an attributed
Apache-2.0 ultrapower adaptation. Preserve those notices when reusing it.
