#!/usr/bin/env python3
"""Repair module discovery for the pinned QE package without changing Lean sources."""

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SUPPORTED_REVISION = 'f3ef4ee679f921079aa8f742a2807a9cc724d2d6'


def prepare(root=ROOT, package=None):
    manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    dependency = next(p for p in manifest['packages'] if p['name'] == 'acvf_qe')
    if dependency['rev'] != SUPPORTED_REVISION:
        raise RuntimeError('Review the QE packaging workaround for the new dependency revision')
    package = package or root / manifest['packagesDir'] / 'acvf_qe'
    actual = subprocess.check_output(
        ['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != SUPPORTED_REVISION:
        raise RuntimeError('QE checkout does not match the pinned revision')
    sources = sorted((package / 'Proofs').glob('*.lean'))
    if not sources or not any(p.stem == 'ACVFQE' for p in sources):
        raise RuntimeError('Expected the exported QE proof modules')
    original_sources = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    config = package / 'lakefile.toml'
    text = config.read_bytes().decode('utf-8')
    modules = [p.stem for p in sources]
    old = 'roots = ["ACVFQE"]'
    new = 'roots = ' + json.dumps(modules)
    if new in text:
        changed = False
    elif text.count(old) == 1 and text.count('[[lean_lib]]') == 1:
        config.write_bytes(text.replace(old, new).encode('utf-8'))
        changed = True
    else:
        raise RuntimeError('Unexpected QE Lake configuration; refusing to rewrite it')
    if any(hashlib.sha256(p.read_bytes()).hexdigest() != original_sources[p.name] for p in sources):
        raise RuntimeError('A QE proof source changed during preparation')
    out = root / '.scratch' / 'ci-verified'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'preparation.json').write_text(json.dumps({
        'revision': actual, 'changed_lake_configuration': changed,
        'library_roots': modules, 'proof_source_sha256': original_sources,
    }, indent=2) + '\n', encoding='utf-8')
    print(f'QE package: registered {len(modules)} sibling modules; proof sources unchanged.')


if __name__ == '__main__':
    prepare()
