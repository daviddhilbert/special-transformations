#!/usr/bin/env python3
"""Verify the active Section 6 library, accepting earlier sections as given.

Use `lake env python3 Section6/verify.py` with the given earlier interfaces
on LEAN_PATH. Only Section 6 sources are built. Logs, source and imported
artifact identities, full headline types and axioms go under .scratch/.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'Archive'))
from inspect_legacy import code_only

BUILD = Path(os.environ.get('SECTION6_BUILD_DIR', str(ROOT / '.scratch/section6-verified'))).resolve()
LIB = BUILD / 'lib'
BUILD.mkdir(parents=True, exist_ok=True)
(BUILD / 'status.txt').write_text('RUNNING\n')
env = os.environ.copy()
env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')
version = subprocess.check_output(['lean', '--version'], text=True).strip()
if '4.35.0' not in version:
    raise RuntimeError('Wrong Lean version: ' + version)

def sha(path):
    state = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            state.update(block)
    return state.hexdigest()

def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins['mathlib'] == '56a005855ea17e0b0958f73ec801ae140b0a1679'
assert pins['acvf_qe'] == '1d7396d7e23c34dc23d19214e510e63e1ec1fe03'
pin_key = sha(ROOT / 'lean-toolchain') + sha(ROOT / 'lake-manifest.json')
cache_path = BUILD / 'cache.json'
cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
modules, fingerprints, given = [], {}, {}
search = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep) if p]

def external(name):
    if name in given:
        return given[name]['fingerprint']
    rel = Path(name.replace('.', '/') + '.olean')
    artifact = next((p / rel for p in search if (p / rel).is_file()), None)
    if artifact is None:
        raise RuntimeError('Missing compiled import: ' + name)
    files = [artifact] + [Path(str(artifact) + suffix) for suffix in ('.private', '.server')
                          if Path(str(artifact) + suffix).is_file()]
    identities = {str(p): sha(p) for p in files}
    fp = hashlib.sha256(json.dumps(identities, sort_keys=True).encode()).hexdigest()
    source = ROOT / (name.replace('.', '/') + '.lean')
    given[name] = dict(artifact_files=identities, fingerprint=fp,
                       current_source_sha256=sha(source) if source.exists() else None,
                       scope='accepted compiled import; current earlier source not rebuilt')
    return fp

def visit(name):
    if name in fingerprints:
        return fingerprints[name]
    source = ROOT / (name.replace('.', '/') + '.lean')
    content = source.read_text(encoding='utf-8')
    if re.search(r'\b(?:sorry|admit|axiom)\b', code_only(content)):
        raise RuntimeError('Placeholder or custom axiom in ' + name)
    imports = re.findall(r'^(?:public\s+)?import ([\w.]+)$', content, re.M)
    deps = [visit(d) if d.startswith('Section6.') else external(d) for d in imports]
    fp = hashlib.sha256((version + pin_key + sha(source) + ''.join(deps)).encode()).hexdigest()
    fingerprints[name] = fp
    modules.append(name)
    return fp

visit('Section6.Library')
save(BUILD / 'given-inputs.json', given)
rows = []
for name in modules:
    source = ROOT / (name.replace('.', '/') + '.lean')
    output = LIB / (name.replace('.', '/') + '.olean')
    log = BUILD / (name + '.log')
    output.parent.mkdir(parents=True, exist_ok=True)
    before = sha(source)
    entry = cache.get(name, {})
    reused = (name != 'Section6.Library' and output.exists() and log.exists()
              and entry.get('fingerprint') == fingerprints[name]
              and entry.get('olean_sha256') == sha(output)
              and entry.get('log_sha256') == sha(log))
    command = ['lean', '-j1', '-o', str(output), str(source)]
    if not reused:
        print('Checking ' + name, flush=True)
        with log.open('w') as stream:
            proc = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                  stderr=subprocess.STDOUT)
        code = proc.returncode
    else:
        print('Reusing matching check: ' + name, flush=True)
        code = 0
    text = log.read_text()
    unchanged = before == sha(source)
    rows.append(dict(module=name, command=command, exit_code=code,
                     source_sha256=before, source_unchanged=unchanged,
                     reused=reused, log=str(log)))
    save(BUILD / 'results.json', dict(lean=version, pins=pins, modules=rows))
    if code or not unchanged or re.search(r'\berror:|declaration uses .sorry.', text):
        (BUILD / 'status.txt').write_text('FAIL: ' + name + '\n')
        print(text)
        sys.exit(code or 1)
    cache[name] = dict(fingerprint=fingerprints[name], source_sha256=before,
                       olean_sha256=sha(output), log_sha256=sha(log))
    save(cache_path, cache)

library = (ROOT / 'Section6/Library.lean').read_text()
headlines = re.findall(r'^#print axioms ([\w.]+)$', library, re.M)
audit = (BUILD / 'Section6.Library.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in headlines:
    match = re.search(re.escape("'" + name + "' depends on axioms:") + r'\s*\[([^]]*)\]', audit)
    clean = "'" + name + "' does not depend on any axioms" in audit
    if not match and not clean:
        raise RuntimeError('Missing axiom audit: ' + name)
    axioms = {a.strip() for a in match[1].split(',') if a.strip()} if match else set()
    if not axioms <= allowed:
        raise RuntimeError('Unaccepted axioms: ' + name + ': ' + repr(axioms))

integration = BUILD / 'integration.lean'
integration.write_text('import ACVFQE\nimport Section5.Library\nimport Section6.Library\n')
command = ['lean', '-j1', str(integration)]
with (BUILD / 'integration.log').open('w') as stream:
    proc = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
if proc.returncode:
    (BUILD / 'status.txt').write_text('FAIL: integration\n')
    sys.exit(proc.returncode)
for name in modules:
    assert cache[name]['source_sha256'] == sha(ROOT / (name.replace('.', '/') + '.lean'))
save(BUILD / 'results.json', dict(lean=version, pins=pins, modules=rows,
     headline_count=len(headlines), accepted_axioms=sorted(allowed),
     integration=dict(command=command, exit_code=proc.returncode),
     scope='Section 6 only; earlier compiled interfaces accepted as given'))
(BUILD / 'status.txt').write_text('PASS\n')
print('PASS: %d modules, %d headline type/axiom audits, combined import' %
      (len(modules), len(headlines)), flush=True)
