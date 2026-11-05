# Historical material

This directory preserves the older QE campaign, model-building snapshots,
blueprint, and earlier project documentation. The active completed QE project
is [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE), commit
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

No archived file was deleted to make the top level smaller. `MOVE-INDEX.json`
records all 336 moves, including those into the active section folders, with
byte-preserving SHA-256 checks. Copies of the previous top-level instructions,
README, Makefile, configuration and root module are in `History/`.

Archived notes and source headers describe earlier states and may contain
superseded proof claims, missing hypotheses, obsolete paths, or incorrect
interpretations of the paper. They are evidence for reuse, not current status.
`QE/LocalQE` and `QE/LocalJohnson` retain the earlier successful QE proof graph
and its historical records. New section work should use the published dependency.

Current cleanup evidence is in `REORGANIZATION-CHECK.json` and
`ROOT-IMPORT-AUDIT.txt`: all moved bytes were preserved, all 42 Section 3/4
static dependency plans resolved, and the new root import/audit passed under
the pinned Lake environment using previously checked dependency artifacts.
This does not certify the legacy section proofs or a full clean Lake build.

The relocation leaves legacy import statements unchanged. Many rely on staged
names such as `Enc`, `Sat`, `Sec3Frozen` and `Sec3Sat`, rather than on their
physical source filenames. `inspect_legacy.py --plan PATH` resolves these
historical aliases for inspection and reports missing dependencies or cycles;
it does not compile the files or certify a combined legacy import.

```sh
python3 Archive/inspect_legacy.py --check-moves
python3 Archive/inspect_legacy.py --inventory
python3 Archive/inspect_legacy.py --plan Section3/Sec3Count.lean
```

After intentional source edits, the move check will report differences from
the initial snapshot. Keep the original hashes as provenance rather than
rewriting them to hide later modifications.
