# Section 4 publication audit

`AUDIT.json` is a curated record of the November 6, 2026 local audit,
separate from mathematical hypotheses in `../STATUS.md` and `../INPUTS.md`.
It identifies the checked sources, pins, compiler results, full-type review
and headline axioms. Raw compiler output and generated scratch harnesses
remain in `.scratch/section4-publication/.scratch/section4-verified/`.

The audit first matched the actual completed Section 3 providers to its
published source and successful compiler receipts. It preserved the prior
successful source compilations and rechecked all 234 Section 4 modules with
Lean's kernel replay against that completed boundary. The replay rejects new
axioms, explicit unsafe or partial source declarations, unexpected unsafe or
partial constants, and non-identical preloaded declarations. An already
loaded theorem is reused only if its complete type, proof, universe parameters
and mutual-theorem group match exactly. It excludes generated
executable `_unsafe_rec` helpers only when their safe parent is present. All
mathematical declarations must kernel-check without those helpers.
The final run used a temporary Linux copy of the publication project, with
all 653 source and support files matched byte for byte. Its actual exit-zero
compiler records were preserved without changing their recorded paths.
Mounted-file access was stabilized with workspace-owned aliases to existing,
read-only, SHA256-matched native compiled inputs. After verification, those
individual artifact aliases were restored as ordinary files with the same
bytes. Shared-library directory aliases remain local scratch infrastructure.
Its harness adapts pinned Lean's `src/LeanChecker.lean` by Kim Morrison and
Sebastian Ullrich; the Apache-2.0 license is retained in `../Imported/Lean-LICENSE`.
The library entry point, all 967 headline types and axiom lists, combined QE
import, and published project root were then checked afresh with exit zero.

For a reproducible independent source build, use the pinned Lake project:

```sh
python3 scripts/prepare_ci.py
lake -R build
lake env python3 Section4/verify.py
python3 -m unittest discover -s scripts -p test_lean_provenance.py -v
```

The public verifier rejects old source-only caches. Reuse requires the exact
resolved compiled provider closure, lookup order, own dependency artifacts,
source, compiler, pins, output parts and logs. Recorded replay evidence is
also hashed when a cache entry relies on it. A clean build compiles sources
instead. The GitHub workflow retains complete compiler and headline logs;
this local audit record does not claim a future CI run has passed.
