#!/usr/bin/env python3
"""Fresh Section 7 source checks and headline audits in the pinned Lake environment.

Usage: lake env python3 Section7/verify.py
Earlier compiled inputs must be available on LEAN_PATH. Their resolved complete
closure is fingerprinted; this does not re-certify those earlier source proofs.
All generated sources, artifacts, logs and receipts stay under .scratch/.
"""
from pathlib import Path
import atexit
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'Archive'))
from inspect_legacy import code_only
sys.path.insert(0, str(ROOT / 'scripts'))
from lean_provenance import artifacts, providers, file_stamps

BUILD = ROOT / '.scratch/section7-verified'
LIB = BUILD / 'lib'
LIB.mkdir(parents=True, exist_ok=True)
STATUS = BUILD / 'status.txt'
STATUS.write_text('RUNNING\n')
atexit.register(lambda: STATUS.write_text('FAIL\n')
                if STATUS.read_text().strip() == 'RUNNING' else None)
env = os.environ.copy()
env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

version = subprocess.check_output(['lean', '--version'], text=True).strip()
if '4.33.1' not in version or (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
    raise RuntimeError('Incorrect Lean toolchain: ' + version)
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
expected = {
    'mathlib': ('0df444a360eaa60ab8c11dca51a86af692955474', 'https://github.com/leanprover-community/mathlib4.git'),
    'acvf_qe': ('f3ef4ee679f921079aa8f742a2807a9cc724d2d6', 'https://github.com/daviddhilbert/ACVF-QE.git'),
}
pin_rows = []
for name, (revision, url) in expected.items():
    entry = next(p for p in manifest['packages'] if p['name'] == name)
    location = ROOT / '.lake/packages' / name
    actual = subprocess.check_output(['git', '-C', str(location), 'rev-parse', 'HEAD'], text=True).strip()
    origin = subprocess.check_output(['git', '-C', str(location), 'config', '--get', 'remote.origin.url'], text=True).strip()
    if entry['rev'] != revision or entry['url'] != url or actual != revision or origin != url:
        raise RuntimeError('Dependency identity mismatch: ' + name)
    pin_rows.append(dict(name=name, revision=actual, url=origin))
write_json(BUILD / 'pins.json', pin_rows)

modules, imports, source_hashes, visiting = [], {}, {}, set()
def visit(name):
    if name in modules:
        return
    if name in visiting:
        raise RuntimeError('Import cycle: ' + name)
    visiting.add(name)
    source = ROOT / (name.replace('.', '/') + '.lean')
    content = code_only(source.read_text(encoding='utf-8'))
    if re.search(r'\b(?:sorry|admit|axiom)\b', content):
        raise RuntimeError('Proof placeholder or custom axiom: ' + name)
    deps = re.findall(r'^\s*import ([\w.]+)\s*$', content, re.M)
    imports[name] = deps
    source_hashes[str(source)] = sha(source)
    for dep in deps:
        if dep.startswith('Section7.'):
            visit(dep)
    visiting.remove(name)
    modules.append(name)
visit('Section7.Library')
external = sorted({d for ds in imports.values() for d in ds if not d.startswith('Section7.')} | {'ACVFQE'})
probe = BUILD / 'ImportProviders.lean'
probe_result = BUILD / 'resolved-imports.json'
probe.write_text('\n'.join('import ' + d for d in external) + '''
open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for moduleName in env.header.moduleNames do
    let path ← Lean.findOLean moduleName
    rows := rows.push <| Json.mkObj [("module", toJson moduleName.toString),
      ("olean", toJson path.toString)]
  IO.FS.writeFile ''' + json.dumps(str(probe_result)) + ''' (toJson rows).pretty
''', encoding='utf-8')

def resolve(label):
    probe_result.unlink(missing_ok=True)
    with (BUILD / (label + '.log')).open('w') as stream:
        rc = subprocess.run(['lean', '-j1', str(probe)], cwd=ROOT, env=env,
                            stdout=stream, stderr=subprocess.STDOUT).returncode
    if rc or not probe_result.exists():
        raise RuntimeError('Import-provider check failed: ' + label)
    return providers(json.loads(probe_result.read_text()))

given = resolve('ImportProviders.before')
if any(n.startswith('Section7.') for n in given):
    raise RuntimeError('Earlier boundary imports Section 7')
write_json(BUILD / 'import-providers.json', dict(lean_path=env['LEAN_PATH'], providers=given))
stamps = file_stamps(given)
rows = []
for name in modules:
    source = ROOT / (name.replace('.', '/') + '.lean')
    output = LIB / (name.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = BUILD / (name + '.log')
    if file_stamps(given) != stamps:
        raise RuntimeError('Earlier import provider changed before ' + name)
    start = time.time()
    command = ['lean', '-j1', '-o', str(output), str(source)]
    print('CHECKING ' + name, flush=True)
    with log.open('w') as stream:
        rc = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    stable = all(sha(path) == h for path, h in source_hashes.items()) and file_stamps(given) == stamps
    row = dict(module=name, command=command, exit_code=rc, fresh_source_compilation=True,
               seconds=time.time()-start, source_sha256=sha(source), inputs_unchanged=stable,
               log_sha256=sha(log), output_sha256=sha(output) if rc == 0 else None,
               output_artifacts=artifacts(output) if rc == 0 else None)
    rows.append(row)
    write_json(BUILD / 'results.json', dict(lean=version, modules=rows, sources=source_hashes))
    if rc or not stable:
        print(log.read_text(), flush=True)
        raise RuntimeError('Failed ' + name)
    print('PASS ' + name, flush=True)

if resolve('ImportProviders.after') != given:
    raise RuntimeError('Import closure changed during verification')
library_log = (BUILD / 'Section7.Library.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", library_log, re.S)
headline_axioms = {}
for name, names in audits:
    # pp.universes prints instantiations such as Classical.choice.{u}.
    # Erase only those instantiations, retaining the exact constant names.
    names = re.sub(r'\.\{[^}]*\}', '', names)
    actual = {a.strip() for a in names.split(',') if a.strip()}
    if actual - allowed:
        raise RuntimeError('Unexpected axiom in ' + name)
    headline_axioms[name] = sorted(actual)
expected_headlines = re.findall(r'^#print axioms ([\w.]+)$',
    (ROOT / 'Section7/Library.lean').read_text(), re.M)
clean = re.findall(r"'([^']+)' does not depend on any axioms", library_log)
headline_axioms.update({name: [] for name in clean})
if set(n for n, _ in audits) | set(clean) != set(expected_headlines):
    raise RuntimeError('Headline audit coverage mismatch')
integration_source = BUILD / 'integration.lean'
integration_source.write_text('import ACVFQE\nimport Section7.Library\n'
    '#check @SpecialTransformations.Section7.encoded_residueRoot_iff_exists\n'
    '#check @SpecialTransformations.Section7.exists_gammaPolynomial_normalization\n'
    '#check @SpecialTransformations.Section7.simpleRoot_normalization_iff\n'
    '#check @SpecialTransformations.Section7.exists_integral_simpleRoot_normalization\n'
    '#check @SpecialTransformations.Section7.multivariate_simpleRoot_lift\n'
    '#check @SpecialTransformations.Section7.generalized_hensel\n'
    '#check @SpecialTransformations.Section7.encoded_generalized_hensel\n'
    '#check @SpecialTransformations.Section7.exists_gammaPolynomial_residue_projection\n'
    '#check @SpecialTransformations.Section7.remark_7_5\n'
    '#check @SpecialTransformations.Section7.lemma_7_4\n'
    '#check @SpecialTransformations.Section7.IsAmbientLift\n'
    '#check @SpecialTransformations.Section7.theorem_7_6\n'
    '#check @SpecialTransformations.Section7.corollary_7_7\n'
    '#check @SpecialTransformations.Section7.corollary_7_7_finite\n', encoding='utf-8')
integration_log = BUILD / 'integration.log'
integration_command = ['lean', '-j1', str(integration_source)]
with integration_log.open('w') as stream:
    integration_exit = subprocess.run(integration_command, cwd=ROOT, env=env,
        stdout=stream, stderr=subprocess.STDOUT).returncode
if integration_exit or file_stamps(given) != stamps or not all(sha(p) == h for p, h in source_hashes.items()):
    raise RuntimeError('Integration check failed or its inputs changed')
write_json(BUILD / 'certificate.json', dict(lean=version, pins=pin_rows,
    fresh_modules=len(rows), headline_audits=len(expected_headlines),
    allowed_axioms=sorted(allowed), sources=source_hashes,
    headline_axioms=headline_axioms,
    import_manifest_sha256=sha(BUILD / 'import-providers.json'),
    results_sha256=sha(BUILD / 'results.json'),
    headline_log_sha256=sha(BUILD / 'Section7.Library.log'),
    integration=dict(command=integration_command, exit_code=integration_exit,
        source_sha256=sha(integration_source), log_sha256=sha(integration_log)),
    verifier_sha256=sha(Path(__file__))))
STATUS.write_text('PASS\n')
print(f'PASS: {len(rows)} fresh modules, {len(expected_headlines)} headline audits, combined ACVF-QE import; inspect full types in Section7.Library.log', flush=True)
