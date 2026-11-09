#!/usr/bin/env python3
"""Verify that the pinned QE package declares all its shipped proof modules."""

import hashlib
import json
from pathlib import Path
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parent.parent


def prepare(root=ROOT, package=None):
    manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    dependency = next(p for p in manifest['packages'] if p['name'] == 'acvf_qe')
    package = package or root / manifest['packagesDir'] / 'acvf_qe'
    actual = subprocess.check_output(
        ['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != dependency['rev']:
        raise RuntimeError('QE checkout does not match the pinned revision')
    sources = sorted((package / 'Proofs').glob('*.lean'))
    modules = [p.stem for p in sources]
    config = tomllib.loads((package / 'lakefile.toml').read_text(encoding='utf-8'))
    library = next(lib for lib in config['lean_lib'] if lib['name'] == 'ACVFQE')
    if ('ACVFQE' not in modules or library.get('srcDir') != 'Proofs'
            or sorted(library.get('roots', [])) != modules):
        raise RuntimeError('QE Lake library roots do not match the shipped proof modules')
    out = root / '.scratch' / 'ci-verified'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'preparation.json').write_text(json.dumps({
        'revision': actual, 'library_roots': modules,
        'proof_source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    }, indent=2) + '\n', encoding='utf-8')
    print(f'QE package: verified {len(modules)} registered proof modules.')


if __name__ == '__main__':
    prepare()
