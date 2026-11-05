# Remaining historical material

The obsolete QE campaign, its duplicate language encoding, and the old QE
planning/history folder have been removed at the author's request. Completed
proofs belong in [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE), pinned at
`f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.

Remaining material consists of older model-building snapshots, the generic
saturation interface, the blueprint, an earlier status scaffold, and cleanup
evidence. Earlier source/plan versions are recoverable from Git history.
Seven shared helpers needed by the section files are retained in `../Shared/`.

`MOVE-INDEX.json` records the initial 336 relocations, including current paths
for retained helpers and explicit `removed_obsolete_qe` status for deleted
entries. There are 93 retained entries and 243 intentionally removed entries.
The checks require retained files to match their original hashes and removed
entries to be absent. Original hashes are provenance, not proof certificates.

```sh
python3 Archive/inspect_legacy.py --check-moves
python3 Archive/inspect_legacy.py --inventory
python3 Archive/inspect_legacy.py --plan Section3/Sec3Count.lean
```

The static planner resolves retained legacy aliases and identifies modules
supplied by pinned ACVF-QE. It does not compile the files or certify their
paper statements. Historical headers may contain superseded claims or paths.

`REORGANIZATION-CHECK.json` and `ROOT-IMPORT-AUDIT.txt` state the exact scope
of the cleanup checks and root import audit. They do not certify the legacy
section proofs or a full clean Lake build.
