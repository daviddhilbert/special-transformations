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
headlines += ['BooleanCombinations.boolean', 'RVRepresentatives.add_correct',
    'RVRepresentatives.neg_correct', 'RVRepresentatives.inv_correct',
    'RVRepresentatives.liftFn_correct', 'RVRepresentatives.liftTerm_correct',
    'RVRepresentatives.qf_definable', 'good_vfImage', 'theorem_2_8_c_minimal',
    'algebraicAt_vf_union_rv_iff', 'corollary_3_7_vf',
    'Balls.closedDisc_rv_constant', 'Balls.openDisc_rv_constant']
headlines += ['SpecialTransformations.DefinableConstants.eliminate_parameters',
    'definableClosureAt_iff_raw', 'AlgebraicAt.eliminate_definable_params',
    'vfDefinableClosureField', 'algebraicAt_vf_iff_parameterField',
    'relativeTrdeg_eq_of_algebraic', 'mem_vfAlgebraicClosureField', 'corollary_3_4',
    'algebraicAt_vf_iff_matroid_closure', 'lemma_3_6_vf',
    'definableClosure_idempotent', 'algebraicAt_definableClosure_iff',
    'definableClosureSubstructure']
headlines += ['definableOver_normalize_iff', 'algebraicAt_normalize_iff',
    'definableClosureAt_normalize_iff',
    'SpecialTransformations.ModelTheory.DefinableReduct.term',
    'SpecialTransformations.ModelTheory.DefinableReduct.formula',
    'SpecialTransformations.ModelTheory.DefinableReduct.definable',
    'normalization_definableReduct', 'Saturated.normalize',
    'DefinableAt.eliminate_sorted_definable_params',
    'AlgebraicAt.eliminate_sorted_definable_params',
    'definableClosureAt_function_symbol', 'definableClosureAt_vf_inv',
    'lemma_3_1_canonical', 'corollary_3_5_sorted',
    'raw_definableOver_sorted', 'DefinableOver.eliminate_sorted_definable_params',
    'RawClosure.Tuple.promote_definable_fibre', 'RawClosure.Tuple.glue_finite',
    'RawClosure.Tuple.definable_choice_graph', 'RawClosure.Tuple.definable_choice',
    'Balls.valuativeCentre_closedDisc', 'Balls.valuativeCentre_openDisc',
    'RawClosure.eliminate_algebraic_parameters', 'AlgebraicAt.eliminate_algebraic_params']
headlines += ['algebraicAt_algebraicClosureSet_iff', 'algebraicClosureSet_idempotent',
    'definableClosure_algebraicClosureSet', 'algebraicClosureSubstructure',
    'Balls.tupleValuation_le_coordinate', 'Balls.le_tupleValuation_iff',
    'Balls.tupleValuation_empty', 'Balls.closedPolydisc_uniform_iff',
    'Balls.openPolydisc_uniform_iff']
explicit_types = {'SpecialTransformations.ModelTheory.DefinableReduct.formula',
    'SpecialTransformations.ModelTheory.DefinableReduct.definable',
    'normalization_definableReduct', 'Saturated.normalize',
    'definableOver_normalize_iff', 'algebraicAt_normalize_iff', 'normalized_model00',
    'normalizeSubstructure'}
headlines += ['Barycentre.natCast_ne_zero', 'Barycentre.sum_sub_mean',
    'Barycentre.mean_equation_of_equiv', 'Barycentre.rv_nonconstant', 'Barycentre.fibre_card_lt',
    'Barycentre.code_sorted', 'Barycentre.code_injective',
    'RawClosure.Tuple.enumeration_definable', 'Barycentre.linearTerm_realize',
    'Barycentre.linearTerm_zero_definable', 'normalizeSubstructure', 'normalized_model00',
    'Barycentre.finiteFibre_enumeration_exists', 'Barycentre.enumerated_mean_equation',
    'Barycentre.mean_definable', 'Barycentre.rawCode_definable', 'Barycentre.rawCode_eq_code',
    'Barycentre.rawCode_injective', 'Balls.mixedRVFibre_nonempty', 'Balls.mixedRVFibre_zero_coordinate',
    'FiniteCoding.projection_definable', 'FiniteCoding.finite_coding_canonical', 'lemma_3_9',
    'Values.vrv_eq_iff', 'Values.vrv_eq_infinity_iff', 'Values.gamma_has_nonzero_representative',
    'Values.vf_value_eq_iff']

headlines += ['Barycentre.mean_sub_eq', 'Barycentre.natCast_value_one',
    'Barycentre.mean_mem_closedDisc', 'Barycentre.mean_mem_openDisc',
    'Balls.sub_mem_closedDisc_iff', 'Balls.sub_mem_openDisc_iff',
    'Balls.rv_sub_constant_openDisc', 'Balls.rv_sub_constant_closedDisc',
    'polynomial_rv_eq_of_linear_factors', 'polynomial_rv_constant_openDisc',
    'polynomial_rv_constant_closedDisc', 'PolynomialSupport.rv_term_eq_of_support',
    'PolynomialSupport.formula_iff_of_support', 'definableOver_iff_normalized_raw',
    'definableAt_iff_normalized_raw', 'DefinableAt.finite_iUnion',
    'PolynomialObstacles.rawRoots_definable', 'PolynomialObstacles.obstacles_definable',
    'qf_rootFree_constant', 'finite_definable_obstacles', 'ClosedBallRoots.enlarge',
    'ClosedBallRoots.meets_each', 'BallFamilies.subset_codes_definable',
    'BallFamilies.minimalDomain_definable', 'BallFamilies.minimal_union_definable',
    'BallFamilies.exists_minimal_below', 'BallFamilies.finite_definable_hitting_set',
    'BallFamilies.closed_family_centres', 'ClosedBallCodes.body_sorted',
    'ClosedBallCodes.body_realize', 'ClosedBallCodes.ball_eq_closed',
    'ClosedBallCodes.ball_eq_univ', 'ClosedBallCodes.exists_code_of_closed',
    'ClosedBallCodes.relation_definable', 'ClosedBallCodes.rawBall_normalize',
    'ClosedBallCodes.coded_centers', 'ClosedBallCodes.underlying_injective',
    'ClosedBallCodes.pullback_image', 'lemma_3_10',
    'ValOneEC.Johnson.ne_finite_union_of_proper_subballs',
    'ValOneEC.Johnson.isValBall_subset_or_subset']
explicit_types |= {'definableOver_iff_normalized_raw', 'ClosedBallCodes.rawBall_normalize',
    'ClosedBallCodes.coded_centers', 'lemma_3_10'}

def qualify(h):
    return h if h.startswith(('SpecialTransformations.', 'ValOneEC.')) else 'SpecialTransformations.Section3.' + h
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
    ('set_option pp.explicit true in\n' if h in explicit_types else '') +
    '#check @' + qualify(h) + '\n#print axioms ' + qualify(h)
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
