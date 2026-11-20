#!/usr/bin/env python3
"""Check the blueprint's dependency graph, Lean links and source anchors.

The default check needs no Lean build. It checks that

- every `\\uses` target is a node label and the node graph is acyclic;
- the `\\lean` declarations in `content.tex` equal the source-link registry
  `src/source-links.tsv`;
- `src/source_links.py` pins ACVF-QE and hilbert-mathlib to the revisions in
  `lake-manifest.json`, and pins this repository to an ancestor of HEAD;
- every source anchor names the declaration keyword line at its pinned
  revision, and no file linked at this repository's pin has changed since;
- `blueprint/README.md` and `content.tex` quote the current pins and counts.

`--write [--pin REV]` regenerates the anchors from the pinned revisions
(optionally re-pinning this repository to REV first). `--audit` also prints
the full type and axioms of every linked declaration from the Lake build and
accepts only `propext`, `Classical.choice` and `Quot.sound`; run it with
`lake env python3` after `lake build`.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / 'blueprint' / 'src'
CONTENT = SRC / 'content.tex'
REGISTRY = SRC / 'source-links.tsv'
LINKS = SRC / 'source_links.py'
README = ROOT / 'blueprint' / 'README.md'
PROVIDERS = {'paper': None, 'qe': 'acvf_qe', 'hilbert': 'hilbert-mathlib'}
PIN_NAMES = {'paper': 'PAPER', 'qe': 'QE', 'hilbert': 'HILBERT'}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODIFIERS = r'(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
KEYWORDS = r'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)'


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], capture_output=True,
                          text=True, check=True).stdout


def pins():
    text = LINKS.read_text(encoding='utf-8')
    found = {}
    for repo, name in PIN_NAMES.items():
        m = re.search(name + r' = "https://github\.com/[^/]+/[^/]+/blob/([0-9a-f]{40})/"', text)
        if not m:
            raise SystemExit(f'Missing {name} pin in {LINKS.relative_to(ROOT)}')
        found[repo] = m.group(1)
    return found


def checkout(repo):
    return ROOT if PROVIDERS[repo] is None else ROOT / '.lake' / 'packages' / PROVIDERS[repo]


def source_at(repo, rev, path):
    return git(checkout(repo), 'show', f'{rev}:{path}').splitlines()


def declaration_pattern(name):
    short = re.escape(name.split('.')[-1])
    return re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?' + MODIFIERS + KEYWORDS
                      + r"\s+(?:[^\s.]+\.)*" + short + r"(?![\w'!?₀-₉])")


def parse_content():
    content = CONTENT.read_text(encoding='utf-8')
    labels, uses, decls, current = [], {}, [], None
    for m in re.finditer(r'\\label\{([^}]+)\}|\\uses\{([^}]+)\}|\\lean\{([^}]+)\}', content):
        if m.group(1):
            current = m.group(1)
            labels.append(current)
            uses.setdefault(current, set())
        elif current is None:
            raise SystemExit('Blueprint dependency before the first node label')
        elif m.group(2):
            uses[current].update(x.strip() for x in m.group(2).split(',') if x.strip())
        else:
            decls.extend(x.strip() for x in m.group(3).split(',') if x.strip())
    return content, labels, uses, decls


def read_registry():
    rows = []
    for line in REGISTRY.read_text(encoding='utf-8').splitlines():
        name, repo, loc = line.split('\t')
        path, _, anchor = loc.partition('#L')
        rows.append([name, repo, path, int(anchor)])
    return rows


def write_registry(rows):
    REGISTRY.write_text(''.join(f'{n}\t{r}\t{p}#L{line}\n' for n, r, p, line in rows),
                        encoding='utf-8')


def audit(names):
    out = ROOT / '.scratch' / 'blueprint-audit'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'BlueprintAudit.lean'
    source.write_text('import SpecialTransformations\nset_option pp.explicit true\n'
                      'set_option pp.fullNames true\n'
                      + ''.join(f'#check @{n}\n#print axioms {n}\n' for n in names),
                      encoding='utf-8')
    result = subprocess.run(['lean', str(source)], cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (out / 'BlueprintAudit.log').write_text(output, encoding='utf-8')
    if result.returncode or re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
        print(output[-4000:], file=sys.stderr)
        raise SystemExit('Blueprint type/axiom audit failed to compile')
    audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
    audits += [(n, '') for n in re.findall(r"'([^'\n]+)' does not depend on any axioms", output)]
    if len(audits) != len(names) or {n for n, _ in audits} != set(names):
        raise SystemExit('Incomplete blueprint axiom audit')
    for name, block in audits:
        found = {x.strip() for x in re.sub(r'\.\{[^}]*\}', '', block).split(',') if x.strip()}
        if found - ALLOWED:
            raise SystemExit(f'Unexpected axioms for {name}: {sorted(found - ALLOWED)}')
    return len(audits)


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--write', action='store_true', help='regenerate source anchors')
    parser.add_argument('--pin', help='with --write: re-pin this repository to REV')
    parser.add_argument('--audit', action='store_true', help='type/axiom-audit linked declarations')
    args = parser.parse_args()
    errors = []

    if args.pin:
        if not args.write:
            raise SystemExit('--pin requires --write')
        rev = git(ROOT, 'rev-parse', '--verify', args.pin + '^{commit}').strip()
        text = LINKS.read_text(encoding='utf-8')
        LINKS.write_text(re.sub(r'(PAPER = "https://github\.com/[^/]+/[^/]+/blob/)[0-9a-f]{40}/',
                                r'\g<1>' + rev + '/', text), encoding='utf-8')
    pin = pins()

    manifest = {p['name'].strip('«»'): p['rev']
                for p in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']}
    for repo, package in PROVIDERS.items():
        if package and manifest.get(package) != pin[repo]:
            errors.append(f'{PIN_NAMES[repo]} pin {pin[repo]} differs from lake-manifest {package}')
    if subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', pin['paper'], 'HEAD'],
                      capture_output=True).returncode:
        errors.append(f'PAPER pin {pin["paper"]} is not an ancestor of HEAD')

    content, labels, uses, decls = parse_content()
    if len(set(labels)) != len(labels):
        errors.append('Duplicate node labels')
    for label, deps in uses.items():
        for dep in sorted(deps - set(labels)):
            errors.append(f'Unknown dependency {dep} in {label}')
    state = {}

    def visit(node, stack):
        if state.get(node) == 'done':
            return
        if state.get(node) == 'active':
            errors.append('Cyclic dependencies: ' + ' -> '.join(stack + [node]))
            return
        state[node] = 'active'
        for dep in sorted(uses.get(node, ())):
            visit(dep, stack + [node])
        state[node] = 'done'

    for label in labels:
        visit(label, [])

    rows = read_registry()
    names = [r[0] for r in rows]
    if len(set(names)) != len(names):
        errors.append('Duplicate source-link registry entries')
    if set(decls) != set(names):
        errors.append('TeX declarations differ from the registry: missing '
                      f'{sorted(set(decls) - set(names))}, extra {sorted(set(names) - set(decls))}')

    cache = {}
    for row in rows:
        name, repo, path, line = row
        if repo not in PROVIDERS:
            errors.append(f'Unknown repository {repo} for {name}')
            continue
        key = (repo, path)
        if key not in cache:
            try:
                cache[key] = source_at(repo, pin[repo], path)
            except subprocess.CalledProcessError:
                cache[key] = None
        lines = cache[key]
        if lines is None:
            errors.append(f'{path} is absent at {repo} revision {pin[repo]}')
            continue
        pattern = declaration_pattern(name)
        if 0 < line <= len(lines) and pattern.match(lines[line - 1]):
            continue
        matches = [i + 1 for i, text in enumerate(lines) if pattern.match(text)]
        if args.write and len(matches) == 1:
            row[3] = matches[0]
        else:
            errors.append(f'Stale anchor {name}: {path}#L{line} (declaration lines {matches})')

    linked = sorted({p for _, repo, p, _ in rows if repo == 'paper'})
    changed = git(ROOT, 'diff', '--name-only', pin['paper'], '--', *linked).split()
    errors.extend(f'{p} changed after the PAPER pin; re-pin with --write --pin' for p in changed)

    counts = {'nodes': len(labels), 'declarations': len(names)}
    readme = README.read_text(encoding='utf-8')
    m = re.search(r'contains (\d+) nodes and links\s+(\d+) distinct', readme)
    if not m or (int(m.group(1)), int(m.group(2))) != (counts['nodes'], counts['declarations']):
        errors.append(f'blueprint/README.md does not state {counts["nodes"]} nodes and '
                      f'{counts["declarations"]} distinct declarations')
    for repo, rev in pin.items():
        if rev not in readme.replace('\n', ''):
            errors.append(f'blueprint/README.md does not quote the {PIN_NAMES[repo]} pin {rev}')
        if f'\\texttt{{{rev[:7]}}}' not in content:
            errors.append(f'content.tex does not quote the {PIN_NAMES[repo]} pin {rev[:7]}')

    if args.write:
        write_registry(rows)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    if args.audit:
        counts['audited'] = audit(names)
    by_repo = {repo: sum(r[1] == repo for r in rows) for repo in PROVIDERS}
    print(json.dumps(dict(counts, links_by_repository=by_repo, pins=pin, status='PASS')))
    return 0


if __name__ == '__main__':
    sys.exit(main())
