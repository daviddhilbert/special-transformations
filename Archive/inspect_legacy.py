#!/usr/bin/env python3
"""Inspect relocated legacy snapshots; this tool does not compile Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
MOVES = json.loads((ROOT / 'Archive/MOVE-INDEX.json').read_text(encoding='utf-8-sig'))
PUBLISHED = set(json.loads((ROOT / 'Shared/ACVF-QE-MODULES.json').read_text(encoding='utf-8-sig'))['modules'])


def code_only(source):
    """Remove nested Lean comments while preserving quoted strings."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: i += 1
        elif quoted:
            out.append(source[i])
            if source[i] == '\\' and i + 1 < len(source):
                out.append(source[i+1]); i += 2; continue
            if source[i] == '"': quoted = False
            i += 1
        elif pair == '/-':
            depth = 1; out.append(' '); i += 2
        elif pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
            out.append('\n')
        else:
            if source[i] == '"': quoted = True
            out.append(source[i]); i += 1
    return ''.join(out)


def imports(path):
    code = code_only((ROOT / path).read_text(encoding='utf-8-sig'))
    return [name for line in re.findall(r'^import\s+([^\n]+)', code, re.M)
            for name in line.split()]


def check_moves():
    bad = []
    retained = 0
    removed = 0
    for row in MOVES:
        p = ROOT / row['new']
        if row.get('status') == 'removed_obsolete_qe':
            removed += 1
            if p.exists(): bad.append(row['new'] + ' (marked removed but still present)')
            continue
        retained += 1
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != row['sha256']:
            bad.append(row['new'])
    if bad:
        print('Different from initial relocation snapshot:', *bad, sep='\n', file=sys.stderr)
        return 1
    print(f'PASS: {retained} retained files match original hashes; {removed} obsolete QE entries are absent.')
    return 0


def inventory():
    rows = []
    for row in MOVES:
        if row.get('status') == 'removed_obsolete_qe': continue
        if row['new'].startswith('Section') and row['new'].endswith('.lean'):
            raw = (ROOT / row['new']).read_bytes()
            code = code_only(raw.decode('utf-8-sig'))
            rows.append({**row, 'current_sha256': hashlib.sha256(raw).hexdigest(),
                         'imports': imports(row['new']),
                         'placeholder_tokens': len(re.findall(r'\b(?:sorry|admit)\b', code)),
                         'verification': 'not freshly compiled during reorganization'})
    p = ROOT / 'Archive/LEGACY-INVENTORY.json'
    p.write_text(json.dumps({'kind':'static source inventory, not a proof audit',
                            'files':rows}, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(f'Wrote static inventory for {len(rows)} section Lean files to {p.relative_to(ROOT)}.')
    return 0


def plan(target):
    aliases = {}
    for row in MOVES:
        if row.get('status') == 'removed_obsolete_qe': continue
        old, new = Path(row['old']), row['new']
        if old.suffix != '.lean': continue
        # The independent LocalQE/LocalJohnson checkers have their own module
        # registries. Do not mix their duplicate names into this legacy plan.
        if old.parts[:2] in [('QE','LocalQE'), ('QE','LocalJohnson')]: continue
        aliases[old.with_suffix('').as_posix().replace('/', '.')] = new
        aliases[Path(new).with_suffix('').as_posix().replace('/', '.')] = new
        if len(old.parts) == 2 and old.parts[0] in ('QE','Milestone0'):
            aliases[old.stem] = new
    for name, old in {'Sat':'Milestone0/Saturation.lean',
                      'Sec3Frozen':'QE/Sec3_frozen.lean', 'Sec3Sat':'QE/Sec3_sat.lean',
                      'Sec3':'QE/Sec3_draft.lean'}.items():
        aliases[name] = next(r['new'] for r in MOVES if r['old'] == old)
    p = (ROOT / target).resolve()
    if not p.is_relative_to(ROOT) or not p.is_file():
        raise ValueError('Target must be an existing file inside this repository')
    target = p.relative_to(ROOT).as_posix()
    ordered, visiting, seen, missing, cycles, supplied = [], [], set(), [], [], set()
    external = {'Mathlib','Lean','Std','Init','Batteries','Aesop','Qq','ProofWidgets','Cli','Plausible','ImportGraph'}
    def visit(path):
        if path in seen: return
        if path in visiting:
            cycles.append(visiting[visiting.index(path):] + [path]); return
        visiting.append(path)
        for dep in imports(path):
            if dep in PUBLISHED: supplied.add(dep)
            elif dep in aliases: visit(aliases[dep])
            elif dep.split('.')[0] not in external: missing.append((path, dep))
        visiting.pop(); seen.add(path); ordered.append(path)
    visit(target)
    print('Static dependency plan only; no Lean compilation or proof certification.')
    if supplied: print('Provided by pinned ACVF-QE: ' + ', '.join(sorted(supplied)))
    for path in ordered: print(path)
    for path, dep in missing: print(f'UNRESOLVED: {path}: {dep}', file=sys.stderr)
    for cycle in cycles: print('CYCLE: ' + ' -> '.join(cycle), file=sys.stderr)
    return int(bool(missing or cycles))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check-moves', action='store_true')
    group.add_argument('--inventory', action='store_true')
    group.add_argument('--plan', metavar='FILE')
    args = parser.parse_args()
    sys.exit(check_moves() if args.check_moves else inventory() if args.inventory else plan(args.plan))
