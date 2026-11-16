#!/usr/bin/env python3
"""Validate the exact shared proof provider behind compatibility imports."""
from pathlib import Path
import hashlib
import json
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root):
    root = Path(root)
    record = json.loads((root / 'SHARED-FOUNDATION.json').read_text())
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    dependency = next(p for p in manifest['packages']
                      if p['name'] in ('hilbert-mathlib', '«hilbert-mathlib»'))
    provider = root / manifest['packagesDir'] / 'hilbert-mathlib'
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=provider,
                                     text=True).strip()
    if actual != dependency['rev'] or actual != record['revision']:
        raise RuntimeError('Shared foundation does not match its exact dependency pin')
    evidence = {}
    for item in record['modules']:
        source = provider / item['target_path']
        shim = root / item['path']
        if sha(source) != item['extracted_sha256']:
            raise RuntimeError('Shared proof source changed: ' + str(source))
        if sha(shim) != item['compatibility_sha256']:
            raise RuntimeError('Compatibility import changed: ' + str(shim))
        evidence[item['module']] = {'provider': item['target_module'],
            'provider_source_sha256': sha(source), 'compatibility_sha256': sha(shim)}
    result = {'status': 'PASS', 'revision': actual, 'modules': evidence}
    out = root / '.scratch/shared-foundation.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print('Shared foundation: exact pin and source provenance checked for', len(evidence), 'compatibility imports.')
    return result


if __name__ == '__main__':
    verify(Path(__file__).resolve().parents[1])
