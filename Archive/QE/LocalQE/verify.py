#!/usr/bin/env python3
"""Check the local QE proof against the author's corrected RV-group Encoding.

Run with the pinned Lean on PATH and Mathlib's package paths in LEAN_PATH:
    python3 QE/LocalQE/verify.py

This does not use the repository's machine-specific Lake configuration.
All generated sources, oleans, and logs are confined to .scratch/local-qe-check.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FOCUSED = os.environ.get("LOCAL_QE_FOCUSED") == "1"
BUILD = ROOT / ".scratch" / ("local-qe-check-focused" if FOCUSED else "local-qe-check")
SRC, LIB, LOG = (BUILD / name for name in ("src", "lib", "logs"))
for directory in (SRC, LIB, LOG):
    directory.mkdir(parents=True, exist_ok=True)
(BUILD / "status.txt").write_text("RUNNING\n", encoding="utf-8")

sources = {p.stem: p for p in HERE.glob("*.lean")}
for path in (ROOT / "QE" / "LocalJohnson").glob("*.lean"):
    if path.stem in sources:
        raise RuntimeError("Duplicate local module name: " + path.stem)
    sources[path.stem] = path
sources["Enc"] = ROOT / "Milestone0" / "Encoding.lean"
for name in ("QF2Fragment", "FragmentTransfer", "RVCalc", "VFField", "VFValued"):
    sources[name] = ROOT / "QE" / (name + ".lean")
sources["VFAlgClosed"] = HERE / "dependencies" / "VFAlgClosed.lean"

texts = {name: path.read_text(encoding="utf-8-sig") for name, path in sources.items()}
if FOCUSED:
    imports = ["ModelTheory.Definability", "ModelTheory.Complexity", "ModelTheory.Substructures",
               "ModelTheory.Bundled", "RingTheory.Valuation.ValuationSubring",
               "GroupTheory.QuotientGroup.Basic", "Tactic.FinCases", "Tactic.Ring"]
    texts["Enc"] = re.sub(r"^import Mathlib$", "\n".join("import Mathlib." + p for p in imports),
                          texts["Enc"], flags=re.M)
    texts["VFField"] = "import Mathlib.Algebra.Field.MinimalAxioms\n" + texts["VFField"]
    texts["VFValued"] = "import Mathlib.RingTheory.Valuation.ValuativeRel.Basic\n" + texts["VFValued"]
dependencies = {
    name: [dep for dep in re.findall(r"^import\s+(\S+)", text, re.M) if dep in sources]
    for name, text in texts.items()
}
ordered, active = [], set()
def visit(name):
    if name in ordered:
        return
    if name in active:
        raise RuntimeError("Cyclic imports at " + name)
    active.add(name)
    for dep in dependencies[name]:
        visit(dep)
    active.remove(name)
    ordered.append(name)
targets = os.environ.get("LOCAL_QE_TARGETS", "").split(",")
for name in (targets if targets != [""] else sorted(sources)):
    visit(name)

version = subprocess.check_output(["lean", "--version"], text=True).strip()
if "4.33.1" not in version:
    raise RuntimeError("Expected the repository's pinned Lean 4.33.1: " + version)
env = os.environ.copy()
env["LEAN_PATH"] = str(LIB) + os.pathsep + env.get("LEAN_PATH", "")
manifest_path = BUILD / "manifest.json"
manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
fingerprints = {}
report = []
for name in ordered:
    text = texts[name]
    fingerprint = hashlib.sha256((version + text + "".join(
        fingerprints[dep] for dep in dependencies[name])).encode()).hexdigest()
    fingerprints[name] = fingerprint
    source, olean, log = SRC / (name + ".lean"), LIB / (name + ".olean"), LOG / (name + ".log")
    source.write_text(text, encoding="utf-8")
    cached = manifest.get(name) == fingerprint and olean.exists() and log.exists()
    if cached:
        result = 0
    else:
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(["lean", "-R", str(SRC), "-o", str(olean), str(source)],
                                    env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    output = log.read_text(encoding="utf-8")
    bad_axioms = [a.strip() for block in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
                  for a in block.split(",") if a.strip() not in
                  {"", "propext", "Classical.choice", "choice", "Quot.sound"}]
    # Enc retains only the separate C-minimality placeholder. QE may not depend on it.
    failed = result != 0 or bool(re.search(r"\berror\b", output)) or bool(bad_axioms)
    report.append(f"{name}\t{result}\t{'FAIL' if failed else 'PASS'}\t{'cached' if cached else 'checked'}")
    (BUILD / "results.tsv").write_text("\n".join(report) + "\n", encoding="utf-8")
    print(report[-1], flush=True)
    if failed:
        print(output, file=sys.stderr)
        (BUILD / "status.txt").write_text("1\n", encoding="utf-8")
        sys.exit(1)
    manifest[name] = fingerprint
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

# Import everything together to detect namespace and dependency collisions.
combined = SRC / "CombinedLocalQE.lean"
audit = ""
if "Theorem23" in ordered:
    audit = "\n".join([
        "#check @JohnsonACF.hasQEb",
        "#print axioms JohnsonACF.hasQEb",
        "#check @ProvedResidueClosure.provedResidueClosure",
        "#print axioms ProvedResidueClosure.provedResidueClosure",
        "#check @ProvedACFExtension.markerACFSaturatedEmbeddingExtension",
        "#print axioms ProvedACFExtension.markerACFSaturatedEmbeddingExtension",
        "#check @JohnsonValuedExtension.markerNotesProposition45",
        "#print axioms JohnsonValuedExtension.markerNotesProposition45",
        "#check @CountableSaturatedExtension.exists_saturated_elementary_extension",
        "#print axioms CountableSaturatedExtension.exists_saturated_elementary_extension",
        "#check @CountableQECriterion.fullQE_of_saturatedExtension",
        "#print axioms CountableQECriterion.fullQE_of_saturatedExtension",
        "#check @SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination",
        "#print axioms SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination",
        "",
    ])
combined.write_text("".join("import " + name + "\n" for name in ordered) + audit,
                    encoding="utf-8")
with (LOG / "CombinedLocalQE.log").open("w", encoding="utf-8") as stream:
    result = subprocess.run(["lean", "-R", str(SRC), str(combined)], env=env,
                            stdout=stream, stderr=subprocess.STDOUT).returncode
output = (LOG / "CombinedLocalQE.log").read_text(encoding="utf-8")
bad_axioms = [a.strip() for block in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
              for a in block.split(",") if a.strip() not in
              {"", "propext", "Classical.choice", "choice", "Quot.sound"}]
failed = result != 0 or bool(re.search(r"\berror\b", output)) or bool(bad_axioms)
if audit and "SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination' depends" not in output:
    failed = True
status = result if result != 0 else int(failed)
(BUILD / "status.txt").write_text(str(status) + "\n", encoding="utf-8")
if failed:
    print(output, file=sys.stderr)
sys.exit(status)
