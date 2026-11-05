# Shared helpers for the section code

The obsolete QE campaign was deleted at the author's request. These seven
files are retained because the existing section sources depend on them:
`ExSortedG`, `JunkTrue`, `MulNormalForm`, `ParamBridgeRelabel`,
`ParamBridgeShift`, `SubstParam`, and `SubstVar`.

They were moved unchanged from the old campaign. Their original hashes and
paths are recorded in `../Archive/MOVE-INDEX.json`. Their legacy import names
remain unchanged; they are candidates for integration, not freshly verified
components of the active library.

The common `Enc`, `RVCalc`, `VFField`, and `VFValued` modules are supplied by
the pinned [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE) dependency.
`ACVF-QE-MODULES.json` records its module names and exact revision for the
static dependency planner. Do not recreate the completed QE proofs here.
