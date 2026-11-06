# Special transformations in algebraically closed valued fields

Yimu Yin, APAL (2010), [arXiv:1006.2467](https://arxiv.org/abs/1006.2467).

This repository is now a thin coordination project for formalizing the paper
section by section. The completed ACF/ACVF/RV quantifier-elimination proofs
live in [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE), pinned here at
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

## Continue here

Sections 2--3 are complete in the approved scope recorded in
[Section3/HANDOFF.md](Section3/HANDOFF.md). Section 4 has a checked
[entry point](Section4/Library.lean) and [verification record](Section4/STATUS.md).
QE is finished and is a dependency of this work.

| Folder | Scope |
| --- | --- |
| [Section3/](Section3/README.md) | Completed structural properties and remaining Section 2 preliminaries |
| [Section4/](Section4/README.md) | Dimensions, definable categories, and Grothendieck constructions |
| Section5/ | RV-pullbacks and special bijections |
| [Section6/](Section6/README.md) | Henselian-field QE and descent |
| Section7/ | Lifting functions |
| Section8/ | Further structural properties |
| Section9/ | Differentiation |
| Section10/ | Categories with volume forms |
| [Shared/](Shared/README.md) | Seven syntax/parameter helpers required by the section code |
| [Archive/](Archive/README.md) | Remaining model-building snapshots and limited historical evidence |

The relocated section files are **legacy candidates**. The new Section 3
library has a separate [entry point](Section3/Library.lean) and
[precise status](Section3/STATUS.md). The legacy snapshots are excluded from
that entry point. Sections 2--3 are complete in the approved scope recorded
in [their handoff](Section3/HANDOFF.md). The new
[Section 4 library](Section4/Library.lean) and [status](Section4/STATUS.md)
cover dimensions, categories and the Grothendieck constructions.

Section 6 has a separate [entry point](Section6/Library.lean),
[status](Section6/STATUS.md) and [handoff](Section6/HANDOFF.md). It proves
syntactic Lemma 6.3, named-base Proposition 6.4 and Denef–Pas Corollary 6.5
with the explicit accepted earlier/standard inputs. Its pinned local check
passed 78 modules, 444 headline audits and the combined import. Reproducing
that check requires the accepted Section 5 interfaces, maintained separately
from this Section 6 publication.

## Build and inspect

Lean 4.33.1 and the matching Mathlib revision are pinned. `lake build` builds
the coordination root, which imports the completed `ACVFQE` library and the
Section 3 and Section 4 entry points. Legacy
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
