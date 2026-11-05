#!/usr/bin/env python3
"""Check the extracted Johnson proof with the repository's pinned Lean 4.33.1.

Run with that Lean on PATH and matching Mathlib package paths in LEAN_PATH:
    python3 QE/LocalJohnson/verify.py

Sources are copied byte for byte. All generated files stay in
.scratch/local-johnson-check; the machine-specific Lake setup is not used.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BUILD = ROOT / ".scratch" / "local-johnson-check"
SRC, LIB, LOG = (BUILD / name for name in ("src", "lib", "logs"))
MODULES = (
    "JohnsonLanguagePrime",
    "JohnsonGeometry",
    "JohnsonAmalgamation",
    "JohnsonCriterion",
    "JohnsonMain",
)
HEADLINES = ("hasQE_ACVF_val", "hasQEb_ACVF_val")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "choice", "Quot.sound"}
AUDIT_PATTERN = re.compile(r"'([^'\n]+)'\s+depends on axioms:\s*\[([^]]*)\]")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def lean_code(text):
    """Blank comments and strings, including nested Lean block comments."""
    result = []
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    result.extend(" " * min(2, len(text) - i))
                    i += 2
                elif text[i] == '"':
                    result.append(" ")
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def audit_output(output, require_headlines=False):
    failures = []
    if re.search(r"\berror\b", output, re.I):
        failures.append("compiler output contains an error")
    if re.search(r"\b(?:sorry|sorryAx|admit)\b", output):
        failures.append("compiler output contains a proof placeholder")
    audits = {}
    for declaration, block in AUDIT_PATTERN.findall(output):
        axioms = {item.strip() for item in block.split(",") if item.strip()}
        audits[declaration] = axioms
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            failures.append(declaration + " uses " + ", ".join(sorted(unexpected)))
    if require_headlines:
        for declaration in HEADLINES:
            if declaration not in audits or not audits[declaration]:
                failures.append("missing or empty headline axiom audit: " + declaration)
    return failures


def main():
    for directory in (SRC, LIB, LOG):
        directory.mkdir(parents=True, exist_ok=True)
    status = BUILD / "status.txt"
    status.write_text("RUNNING\n", encoding="utf-8")
    report = []

    def record(name, result, failed, cached=False):
        row = f"{name}\t{result}\t{'FAIL' if failed else 'PASS'}\t"
        row += "cached" if cached else "checked"
        report.append(row)
        (BUILD / "results.tsv").write_text("\n".join(report) + "\n", encoding="utf-8")
        print(row, flush=True)

    try:
        version = subprocess.check_output(["lean", "--version"], text=True).strip()
        if not re.search(r"\bversion 4\.33\.1(?:,|\s|$)", version):
            raise RuntimeError("Expected pinned Lean 4.33.1; found: " + version)
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip() != \
                "leanprover/lean4:v4.33.1":
            raise RuntimeError("Repository lean-toolchain no longer pins Lean 4.33.1")

        sources = {name: (HERE / (name + ".lean")).read_bytes() for name in MODULES}
        code = {name: lean_code(data.decode("utf-8-sig")) for name, data in sources.items()}
        dependencies = {}
        for name, text in code.items():
            forbidden = re.search(r"\b(?:sorry|admit|axiom)\b", text)
            if forbidden:
                line = text.count("\n", 0, forbidden.start()) + 1
                raise RuntimeError(f"{name}.lean:{line}: forbidden {forbidden.group()}")
            imports = [module for line in re.findall(r"^\s*import\s+([^\n]+)", text, re.M)
                       for module in line.split()]
            unknown = [module for module in imports
                       if module not in sources and module != "Mathlib"
                       and not module.startswith("Mathlib.")]
            if unknown:
                raise RuntimeError(name + " has untracked imports: " + ", ".join(unknown))
            dependencies[name] = [module for module in imports if module in sources]

        ordered, active = [], set()

        def visit(name):
            if name in ordered:
                return
            if name in active:
                raise RuntimeError("Cyclic imports at " + name)
            active.add(name)
            for dependency in dependencies[name]:
                visit(dependency)
            active.remove(name)
            ordered.append(name)

        visit("JohnsonMain")
        if set(ordered) != set(MODULES):
            raise RuntimeError("JohnsonMain does not import the complete five-module proof")

        env = os.environ.copy()
        inherited_path = env.get("LEAN_PATH", "")
        env["LEAN_PATH"] = str(LIB) + os.pathsep + inherited_path
        context = digest(json.dumps({
            "compiler": version,
            "checker": digest(Path(__file__).read_bytes()),
            "LEAN_PATH": inherited_path,
        }, sort_keys=True).encode())
        manifest_path = BUILD / "manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8")) \
            if manifest_path.exists() else {}
        fingerprints = {}

        for name in ordered:
            fingerprint = digest(json.dumps({
                "context": context,
                "source": digest(sources[name]),
                "dependencies": {dep: fingerprints[dep] for dep in dependencies[name]},
            }, sort_keys=True).encode())
            fingerprints[name] = fingerprint
            source, olean, log = (SRC / (name + ".lean"), LIB / (name + ".olean"),
                                  LOG / (name + ".log"))
            source.write_bytes(sources[name])
            entry = manifest.get(name, {})
            cached = (entry.get("fingerprint") == fingerprint and olean.exists()
                      and log.exists() and entry.get("olean") == digest(olean.read_bytes())
                      and entry.get("log") == digest(log.read_bytes()))
            result = 0
            if not cached:
                # Never leave an earlier successful artifact behind after a failed rebuild.
                olean.unlink(missing_ok=True)
                with log.open("w", encoding="utf-8") as stream:
                    result = subprocess.run(
                        ["lean", "-R", str(SRC), "-o", str(olean), str(source)],
                        env=env, stdout=stream, stderr=subprocess.STDOUT,
                    ).returncode
            output = log.read_text(encoding="utf-8")
            failures = audit_output(output)
            failed = result != 0 or bool(failures) or not olean.exists()
            record(name, result, failed, cached)
            if failed:
                print(output, file=sys.stderr)
                raise RuntimeError("; ".join(failures) or name + " did not compile")
            manifest[name] = {"fingerprint": fingerprint, "olean": digest(olean.read_bytes()),
                              "log": digest(log.read_bytes())}
            manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

        # A fresh import verifies the actual exported theorems, even on a fully cached run.
        audit_source = SRC / "JohnsonHeadlineAudit.lean"
        audit_source.write_text("import JohnsonMain\n" + "".join(
            "#check @" + name + "\n#print axioms " + name + "\n" for name in HEADLINES
        ), encoding="utf-8")
        audit_log = LOG / "JohnsonHeadlineAudit.log"
        with audit_log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(["lean", "-R", str(SRC), str(audit_source)],
                                    env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
        output = audit_log.read_text(encoding="utf-8")
        failures = audit_output(output, require_headlines=True)
        record("JohnsonHeadlineAudit", result, result != 0 or bool(failures))
        if result != 0 or failures:
            print(output, file=sys.stderr)
            raise RuntimeError("; ".join(failures) or "headline audit did not compile")
        (BUILD / "AXIOMS.txt").write_text(output, encoding="utf-8")
        status.write_text("0\n", encoding="utf-8")
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        status.write_text("1\n", encoding="utf-8")
        print("Verification failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
