# Shared helpers for the section code

The obsolete QE campaign was deleted at the author's request. These seven
files are retained because the existing section sources depend on them:
`ExSortedG`, `JunkTrue`, `MulNormalForm`, `ParamBridgeRelabel`,
`ParamBridgeShift`, `SubstParam`, and `SubstVar`.

They were moved unchanged from the old campaign. Their original hashes and
paths are recorded in `../Archive/MOVE-INDEX.json`. Lake builds
`ParamBridgeShift` and `ParamBridgeRelabel` as `SharedParameterBridges`
for Section 6. The other five helpers remain available to historical
sources under their existing import names.

The common `Enc`, `RVCalc`, `VFField`, and `VFValued` modules are supplied by
the pinned [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE) dependency.
`ACVF-QE-MODULES.json` records its module names and exact revision for the
static dependency planner. Do not recreate the completed QE proofs here.
