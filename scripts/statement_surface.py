"""Inventory the custom declaration closure needed by the proposed statements.

Read-only environment inspection, not a proof or Comparator result.
Run after `lake build` in the pinned project environment.
"""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parent.parent
out=root/'.scratch/ci-verified'
out.mkdir(parents=True,exist_ok=True)
# The semantic equations are checked on the proof side and provide the
# data dependencies of the two deliberately abstracted map implementations.
built=subprocess.run(['lake','build','PalomarPaperSolution'],cwd=root,capture_output=True,
                     text=True,encoding='utf-8',errors='replace')
(out/'StatementSolutionBuild.log').write_text(built.stdout+built.stderr,encoding='utf-8')
if built.returncode:
 print((built.stdout+built.stderr)[-12000:]);raise SystemExit(built.returncode)
qe=[p.stem for p in (root/'.lake/packages/acvf_qe/Proofs').glob('*.lean')]
source='''module
IMPORT_STATEMENT_MODULES
import Lean
meta import Lean
import Lean.Util.FoldConsts
open Lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
private meta partial def statementProofStart (stx : Syntax) : Option String.Pos.Raw :=
  if stx.isOfKind ``Parser.Command.declValSimple ||
      stx.isOfKind ``Parser.Command.declValEqns ||
      stx.isOfKind ``Parser.Command.whereStructInst then
    stx.getPos?
  else
    stx.getArgs.findSome? statementProofStart
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `SpecialTransformations.Section5.Paper.theorem_5_5,
    `SpecialTransformations.Section5.Paper.corollary_5_6]
  let extraRoots : Array Name := #[
    `SpecialTransformations.Section5.canonicalMap_value,
    `SpecialTransformations.Section5.Focus.etaMap_value]
  let definitionHoles : Array Name := #[
    `SpecialTransformations.Section5.canonicalMap,
    `SpecialTransformations.Section5.Focus.etaMap]
  let qeModules : Array String := QE_MODULES
  let mut todo : Array Name := roots ++ extraRoots
  for name in roots ++ extraRoots do
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
      | .defnInfo val => ("definition", if definitionHoles.contains name then none else some val.value)
      | .thmInfo val =>
          ("theorem", if (name.toString.splitOn "._proof_").length > 1 then some val.value else none)
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
    let mut proofStart := Json.null
    let mut parseError := Json.null
    let mut formattedSource := Json.null
    let mut formattedHole := Json.null
    if let some ranges ← findDeclarationRanges? name then
      sourceRange := toJson #[ranges.range.pos.line, ranges.range.pos.column,
        ranges.range.endPos.line, ranges.range.endPos.column]
      selectionRange := toJson #[ranges.selectionRange.pos.line, ranges.selectionRange.pos.column,
        ranges.selectionRange.endPos.line, ranges.selectionRange.endPos.column]
      if kind == "theorem" || kind == "definition" || kind == "inductive" then
        let path := if qeModules.contains modName then
          ".lake/packages/acvf_qe/Proofs/" ++ modName ++ ".lean"
        else modName.replace "." "/" ++ ".lean"
        let text ← liftM <| IO.FS.readFile path
        let fileMap := FileMap.ofString text
        let fragment := text.extract (text.pos! (fileMap.ofPosition ranges.range.pos))
          (text.pos! (fileMap.ofPosition ranges.range.endPos))
        match Parser.runParserCategory env `command fragment path with
        | .ok stx =>
          try
            let format ← Elab.Command.liftCoreM <| PrettyPrinter.ppCategory `command stx
            formattedSource := toJson (format.pretty 1000)
          catch _ => formattedSource := toJson fragment
          if kind == "theorem" then
            let start? := statementProofStart stx
            proofStart := toJson (start?.map (fun p => p.byteIdx))
            if let some start := start? then
              let hole := fragment.extract (fragment.pos! 0) (fragment.pos! start) ++ " := by sorry"
              match Parser.runParserCategory env `command hole path with
              | .ok holeStx =>
                try
                  let format ← Elab.Command.liftCoreM <| PrettyPrinter.ppCategory `command holeStx
                  formattedHole := toJson (format.pretty 1000)
                catch _ => formattedHole := toJson hole
              | .error message => parseError := toJson message
        | .error message => parseError := toJson message
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson modName), ("kind", toJson kind),
      ("source_range", sourceRange), ("selection_range", selectionRange),
      ("proof_start_byte", proofStart), ("parse_error", parseError),
      ("headline", toJson (roots.contains name)),
      ("formatted_source", formattedSource), ("formatted_hole_source", formattedHole)]
  liftM <| IO.FS.writeFile ".scratch/ci-verified/StatementSurface.json"
    (Json.pretty <| Json.mkObj [("declarations", Json.arr rows),
      ("count", toJson rows.size), ("status", toJson "inventory only; not verification")])
'''
import json
source=source.replace('QE_MODULES','#['+', '.join(json.dumps(x) for x in qe)+']')
modules=json.loads((root/'scripts/palomar_statement_modules.json').read_text(encoding='utf-8'))
source=source.replace('IMPORT_STATEMENT_MODULES','\n'.join('import all '+m for m in modules)+'\nimport PalomarPaperSolution')
path=out/'StatementSurface.lean'
path.write_text(source,encoding='utf-8')
result=subprocess.run(['lean',str(path)],cwd=root,capture_output=True,text=True,encoding='utf-8',errors='replace')
(out/'StatementSurface.log').write_text(result.stdout+result.stderr,encoding='utf-8')
print(result.stdout+result.stderr,end='')
raise SystemExit(result.returncode)
