#!/usr/bin/env python3
"""Compile unchanged legacy Section 3 snapshots in isolated historical aliases.

Run with pinned `lake env python3 Archive/audit_section3.py`.
Compiler success is NOT a claim that a paper theorem or its hypotheses are proved.
All generated sources, artifacts and diagnostics stay in .scratch/section3-audit.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from inspect_legacy import ROOT, MOVES, PUBLISHED, code_only, imports

BUILD = ROOT / '.scratch/section3-audit'
SRC, LIB, LOG = (BUILD / x for x in ('src', 'lib', 'logs'))
for p in (SRC, LIB, LOG):
    p.mkdir(parents=True, exist_ok=True)
aliases = {}
for row in MOVES:
    if row.get('status') == 'removed_obsolete_qe':
        continue
    old, new = Path(row['old']), row['new']
    if old.suffix == '.lean':
        aliases[old.stem] = new
aliases.update({'Sat': 'Archive/Milestone0/Saturation.lean',
                'Sec3Frozen': 'Section3/Sec3_frozen.lean',
                'Sec3Sat': 'Section3/Sec3_sat.lean',
                'Sec3': 'Section3/Sec3_draft.lean'})
names = {v: k for k, v in aliases.items()}
ordered = []
active = set()
def visit(path):
    if path in ordered:
        return
    if path in active:
        raise RuntimeError('Import cycle: ' + path)
    active.add(path)
    for dep in imports(path):
        if dep not in PUBLISHED and dep in aliases:
            visit(aliases[dep])
        elif dep not in PUBLISHED and dep != 'Mathlib':
            raise RuntimeError('Unresolved import: ' + dep)
    active.remove(path)
    ordered.append(path)

for path in sorted(r['new'] for r in MOVES
                   if r.get('status') != 'removed_obsolete_qe'
                   and r['new'].startswith('Section3/')
                   and r['new'].endswith('.lean')
                   and '/LegacyScaffold/' not in r['new']):
    visit(path)
version = subprocess.check_output(['lean', '--version'], text=True).strip()
if '4.33.1' not in version:
    raise RuntimeError('Wrong Lean: ' + version)
env = os.environ.copy()
env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')
results, state = [], {}
for path in ordered:
    name = names[path]
    raw = (ROOT / path).read_bytes()
    text = raw.decode('utf-8-sig')
    deps = [aliases[d] for d in imports(path) if d in aliases and d not in PUBLISHED]
    placeholders = len(re.findall(r'\b(?:sorry|admit)\b', code_only(text)))
    row = dict(path=path, alias=name, sha256=hashlib.sha256(raw).hexdigest(),
               placeholder_tokens=placeholders)
    if any(state[d] != 0 for d in deps):
        row.update(compiler_exit=None, status='blocked by failed dependency')
        state[path] = -1
    else:
        source = SRC / (name + '.lean')
        source.write_text(text, encoding='utf-8')
        with (LOG / (name + '.log')).open('w', encoding='utf-8') as out:
            rc = subprocess.run(['lean', '-R', str(SRC), '-o', str(LIB / (name + '.olean')),
                                 str(source)], env=env, stdout=out, stderr=subprocess.STDOUT).returncode
        output = (LOG / (name + '.log')).read_text()
        errors = len(re.findall('error', output, re.I))
        row.update(compiler_exit=rc, error_occurrences=errors,
                   status='compiled legacy candidate' if rc == 0 and errors == 0 else 'compiler failure')
        state[path] = 0 if rc == 0 and errors == 0 else 1
    results.append(row)
    (BUILD / 'results.json').write_text(json.dumps(dict(lean=version, files=results), indent=2) + '\n')
    print(f"{path}: {row['status']} ({placeholders} local placeholders)", flush=True)
(BUILD / 'status.txt').write_text('audit finished; inspect results.json; not a paper proof certificate\n')
