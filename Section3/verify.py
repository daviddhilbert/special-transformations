#!/usr/bin/env python3
"""Compile the new Section 3 library and audit its exported headlines.

Usage after building pinned dependencies: lake env python3 Section3/verify.py
All logs and build artifacts are scratch output. No legacy source is imported.
"""
import json
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'Archive'))
from inspect_legacy import code_only

BUILD = ROOT / '.scratch/section3-verified'
LIB = ROOT / '.lake/build/lib/lean'
BUILD.mkdir(parents=True, exist_ok=True)
(BUILD / 'status.txt').write_text('RUNNING\n')
(LIB / 'Section3').mkdir(parents=True, exist_ok=True)
version = subprocess.check_output(['lean', '--version'], text=True).strip()
if '4.33.1' not in version:
    raise RuntimeError('Expected pinned Lean 4.33.1: ' + version)
modules, visiting = [], set()
def visit(module):
    if module in modules:
        return
    if module in visiting:
        raise RuntimeError('Cyclic import: ' + module)
    visiting.add(module)
    source = ROOT / 'Section3' / (module + '.lean')
    for dep in re.findall(r'^import Section3\.(\w+)$', source.read_text(encoding='utf-8'), re.M):
        visit(dep)
    visiting.remove(module)
    modules.append(module)
visit('Library')
headlines = [
    'DefinableOver.finite_character', 'AlgebraicAt.finite_character',
    'definableClosureAt_of_mem', 'BaseContext.model',
    'Saturated.finite_inconsistent', 'Saturated.finite_subcover',
    'DefinableOver.quantifier_free', 'Coordinates.fibre_nonempty_iff',
    'Average.lemma_3_8', 'QuotientFamilies.notation_3_16',
    'QuotientFamilies.overDomain_iff_nonempty_values', 'c_minimal_valued_language',
    'c_minimal_valued_definable', 'Balls.rvFibre_eq_openDisc', 'realize_rvEquality',
    'rvOnly_correct', 'DefinableAt.raw_definable', 'AlgebraicAt.raw_finite_witness']
headlines += ['BaseContext.namedModel', 'small_insert',
    'Saturated.definable_finite_subcover_tuple', 'RawClosure.Tuple.promote_tuple',
    'RawClosure.Tuple.good_relation_of_algebraic', 'RawClosure.Tuple.algebraicity_descent_raw',
    'raw_definable_sorted', 'algebraicAt_iff_raw', 'lemma_3_1', 'corollary_3_2_vf',
    'RawClosure.finite_of_definable_subset_algebraic']
headlines += ['PolynomialSyntax.realizes', 'polynomial_rv_locally_constant',
    'infinite_valued_neighbourhood', 'rvTerm_local', 'qf_local',
    'algebraicAt_vf_isAlgebraic', 'vfParameterField_union_rv', 'lemma_3_3']
headlines += ['RingSyntax.realizes', 'PolynomialRoots.term_realize',
    'PolynomialRoots.rootSet_definable', 'PolynomialRoots.rootSet_finite',
    'PolynomialRoots.algebraicAt_of_isAlgebraic_named', 'VFFieldBase.algebraicAt_iff',
    'finite_rv_to_vf_tuple_relation_image', 'corollary_3_5']
env = os.environ.copy()
env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')
rows = []
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

cache_path = BUILD / 'cache.json'
cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
fingerprints = {}
pin_key = sha(ROOT / 'lake-manifest.json') + sha(ROOT / 'lean-toolchain')
def run(name, source, output=None, fingerprint=None):
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    args = ['lean']
    if output:
        args += ['-o', str(output)]
    args += [str(source)]
    log = BUILD / (name + '.log')
    entry = cache.get(name, {})
    reused = bool(output and output.exists() and log.exists() and fingerprint
                  and entry.get('fingerprint') == fingerprint
                  and entry.get('olean_sha256') == sha(output)
                  and entry.get('log_sha256') == sha(log))
    if reused:
        rc = 0
    else:
        with log.open('w', encoding='utf-8') as out:
            rc = subprocess.run(args, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
    text = log.read_text(encoding='utf-8')
    if hashlib.sha256(source.read_bytes()).hexdigest() != source_sha:
        raise RuntimeError('Source changed during compiler run: ' + str(source))
    errors = len(re.findall('error', text, re.I))
    bad = rc != 0 or errors != 0 or bool(re.search(r'\b(?:sorry|sorryAx|admit)\b', text))
    rows.append(dict(module=name, source_sha256=source_sha,
                     compiler_exit=rc, error_occurrences=errors, passed=not bad, reused=reused))
    (BUILD / 'results.json').write_text(json.dumps(dict(lean=version, files=rows), indent=2) + '\n')
    print(name + ': ' + ('FAIL' if bad else 'PASS') + (' (matching checked cache)' if reused else ''), flush=True)
    if bad:
        print(text)
        sys.exit(1)
    if output and fingerprint:
        cache[name] = dict(fingerprint=fingerprint, olean_sha256=sha(output), log_sha256=sha(log))
        cache_path.write_text(json.dumps(cache, indent=2) + '\n')
    return text

for module in modules:
    source = ROOT / 'Section3' / (module + '.lean')
    if re.search(r'\b(?:sorry|admit|axiom)\b', code_only(source.read_text(encoding='utf-8'))):
        raise RuntimeError('Placeholder or custom axiom in ' + str(source))
    deps = re.findall(r'^import Section3\.(\w+)$', source.read_text(encoding='utf-8'), re.M)
    fingerprints[module] = hashlib.sha256((version + pin_key + sha(source) +
        ''.join(fingerprints[d] for d in deps)).encode()).hexdigest()
    run(module, source, LIB / 'Section3' / (module + '.olean'), fingerprints[module])
source = BUILD / 'HeadlineAudit.lean'
source.write_text('import Section3.Library\n' + '\n'.join(
    '#check @SpecialTransformations.Section3.' + h + '\n#print axioms SpecialTransformations.Section3.' + h
    for h in headlines) + '\n', encoding='utf-8')
output = run('HeadlineAudit', source)
audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
audits += [(name, '') for name in re.findall(r"'([^'\n]+)' does not depend on any axioms", output)]
if len(audits) != len(headlines):
    raise RuntimeError('Incomplete headline axiom output')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, block in audits:
    if set(filter(None, (s.strip() for s in block.split(',')))) - allowed:
        raise RuntimeError('Unexpected axiom: ' + name)
run('Root', ROOT / 'SpecialTransformations.lean')
(BUILD / 'status.txt').write_text('PASS\n')
print('PASS: checked library, headline types, allowed axioms, and project root. See STATUS.md for scope.')
