#!/usr/bin/env python3
"""Verify relocated Fubini prerequisite proofs against their original full types."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'PROMOTED-FOUNDATIONS.json').read_text())
    shared = ROOT / '.lake/packages/hilbert-mathlib/verification/verify.py'
    sys.path.insert(0, str(shared.parent))
    spec = importlib.util.spec_from_file_location('shared_signatures', shared)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    names = []
    source_hashes = {}
    for item in manifest['modules']:
        path = ROOT / item['target_path']
        source = path.read_text()
        if hashlib.sha256(source.encode()).hexdigest() != item['extracted_sha256']:
            raise RuntimeError('Promoted proof source changed: ' + str(path))
        source_hashes[item['target_path']] = item['extracted_sha256']
        if re.search(r'\b(?:sorry|admit|axiom)\b', parser.code_only(source)):
            raise RuntimeError('Unproved declaration in ' + str(path))
        names.extend(d['name'] for d in parser.declarations(source))
    for relative, expected_hash in manifest['entry_points'].items():
        path = ROOT / relative
        source = path.read_text()
        if hashlib.sha256(source.encode()).hexdigest() != expected_hash:
            raise RuntimeError('Promoted entry point changed: ' + relative)
        if parser.declarations(source) or re.search(r'\b(?:sorry|admit|axiom)\b', parser.code_only(source)):
            raise RuntimeError('Promoted entry point introduces declarations: ' + relative)
        source_hashes[relative] = expected_hash
    expected = manifest['declarations']
    if names != [d['name'] for d in expected]:
        raise RuntimeError('Promoted declaration inventory changed')
    commands = ['import ' + item['target_module'] for item in manifest['modules']]
    commands += ['set_option pp.universes true', 'set_option pp.fullNames true',
                 'set_option pp.notation false', 'set_option format.width 160']
    for item in expected:
        commands += ['#check @' + item['name'], '#print axioms ' + item['name']]
    scratch = ROOT / '.scratch/promoted-foundations'
    scratch.mkdir(parents=True, exist_ok=True)
    audit = scratch / 'Audit.lean'
    audit.write_text('\n'.join(commands) + '\n')
    run = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=ROOT, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (scratch / 'types-and-axioms.txt').write_text(run.stdout)
    if run.returncode:
        raise RuntimeError('Promoted type audit failed; see ' + str(scratch))
    actual = parser.records(run.stdout)
    if len(actual) != len(expected):
        raise RuntimeError('Missing promoted public type/axiom records')
    for before, after in zip(expected, actual):
        if (before['name'] != after['name'] or before['axioms'] != after['axioms'] or
                before['signature_sha256'] != hashlib.sha256(after['signature'].encode()).hexdigest()):
            raise RuntimeError('Changed promoted statement or axiom inventory: ' + before['name'])
    if source_hashes != {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                         for path in source_hashes}:
        raise RuntimeError('Promoted proof source changed during its type audit')
    result = {'status': 'PASS', 'modules': len(manifest['modules']),
              'unchanged_public_types': len(actual), 'principles': sorted(parser.ALLOWED),
              'source_sha256': source_hashes}
    (scratch / 'status.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
