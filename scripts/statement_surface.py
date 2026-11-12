"""Inventory the custom declaration closure needed by the proposed statements.

Read-only environment inspection, not a proof or Comparator result.
Run after `lake build` in the pinned project environment.
"""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parent.parent
out=root/'.scratch/ci-verified'
out.mkdir(parents=True,exist_ok=True)
qe=[p.stem for p in (root/'.lake/packages/acvf_qe/Proofs').glob('*.lean')]
source='''module
IMPORT_STATEMENT_MODULES
import Lean
import Lean.Util.FoldConsts
open Lean in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `SpecialTransformations.Section5.Paper.theorem_5_5,
    `SpecialTransformations.Section5.Paper.corollary_5_6,
    `SpecialTransformations.Section9.theorem_9_16_finite_volume_of_reference_input,
    `SpecialTransformations.Section10.theorem_10_5_rv_volume,
    `SpecialTransformations.Section10.theorem_10_5_gamma_volume]
  let qeModules : Array String := QE_MODULES
  let mut todo : Array Name := #[]
  for name in roots do
    let some info := env.find? name | throwError "Missing headline {name}"
    for dependency in info.type.getUsedConstants do
      todo := todo.push dependency
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!.toString
    unless modName.startsWith "Section" || modName.startsWith "Shared" ||
        modName.startsWith "Archive" || qeModules.contains modName do continue
    for dependency in info.type.getUsedConstants do
      todo := todo.push dependency
    let (kind, value) := match info with
      | .defnInfo val => ("definition", some val.value)
      | .thmInfo _ => ("theorem", none)
      | .inductInfo val => ("inductive", none)
      | .ctorInfo _ => ("constructor", none)
      | .recInfo _ => ("recursor", none)
      | _ => ("other", none)
    if let some value := value then
      for dependency in value.getUsedConstants do
        todo := todo.push dependency
    if let .inductInfo val := info then
      for constructor in val.ctors do
        todo := todo.push constructor
    let mut sourceRange := Json.null
    let mut selectionRange := Json.null
    if let some ranges ← findDeclarationRanges? name then
      sourceRange := toJson #[ranges.range.pos.line, ranges.range.pos.column,
        ranges.range.endPos.line, ranges.range.endPos.column]
      selectionRange := toJson #[ranges.selectionRange.pos.line, ranges.selectionRange.pos.column,
        ranges.selectionRange.endPos.line, ranges.selectionRange.endPos.column]
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson modName), ("kind", toJson kind),
      ("source_range", sourceRange), ("selection_range", selectionRange)]
  liftM <| IO.FS.writeFile ".scratch/ci-verified/StatementSurface.json"
    (Json.pretty <| Json.mkObj [("declarations", Json.arr rows),
      ("count", toJson rows.size), ("status", toJson "inventory only; not verification")])
'''
import json
source=source.replace('QE_MODULES','#['+', '.join(json.dumps(x) for x in qe)+']')
modules=json.loads((root/'scripts/palomar_statement_modules.json').read_text(encoding='utf-8'))
source=source.replace('IMPORT_STATEMENT_MODULES','\n'.join('import all '+m for m in modules))
path=out/'StatementSurface.lean'
path.write_text(source,encoding='utf-8')
result=subprocess.run(['lean',str(path)],cwd=root,capture_output=True,text=True,encoding='utf-8',errors='replace')
(out/'StatementSurface.log').write_text(result.stdout+result.stderr,encoding='utf-8')
print(result.stdout+result.stderr,end='')
raise SystemExit(result.returncode)
