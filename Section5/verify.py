#!/usr/bin/env python3
"""Check Section 5 locally; earlier-section interfaces are given imports.

Run in the pinned Lake environment with the earlier modules available.
Compiler output and the actual headline type/axiom audit go in .scratch/.
The verifier does not rebuild, certify, or change Sections 2--4.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import atexit
import signal

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'Archive'))
from inspect_legacy import code_only
sys.path.insert(0, str(ROOT / 'scripts'))
from lean_provenance import SCHEMA, artifacts, cache_matches, digest, file_stamps, providers

BUILD = ROOT / '.scratch/section5-verified'
LIB = BUILD / 'lib'
BUILD.mkdir(parents=True, exist_ok=True)
(BUILD / 'status.txt').write_text('RUNNING\n')
atexit.register(lambda: (BUILD / 'status.txt').write_text('FAIL\n')
    if (BUILD / 'status.txt').read_text().strip() == 'RUNNING' else None)
signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(128 + signum))
version = subprocess.check_output(['lean', '--version'], text=True).strip()
if '4.33.1' not in version:
    raise RuntimeError('Expected Lean 4.33.1, got: ' + version)
env = os.environ.copy()
env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read_json(path):
    return json.loads(path.read_text()) if path.exists() else {}

cache_path = BUILD / 'cache.json'
cache = read_json(cache_path)
pin_key = sha(ROOT / 'lean-toolchain') + sha(ROOT / 'lake-manifest.json')
modules, given, fingerprints, scanned_sources = [], {}, {}, {}

def visit(name):
    if name in fingerprints:
        return
    src = ROOT / (name.replace('.', '/') + '.lean')
    content = src.read_text(encoding='utf-8')
    scanned_sources[name] = sha(src)
    deps = re.findall(r'^import ((?:Section3|Section4|Section5)\.[\w.]+)$', content, re.M)
    for dep in deps:
        visit(dep)
    fingerprint = hashlib.sha256((version + pin_key + sha(src) +
        ''.join(fingerprints[d] for d in deps)).encode()).hexdigest()
    fingerprints[name] = fingerprint
    if name.startswith('Section5.'):
        if re.search(r'\b(?:sorry|admit|axiom)\b', code_only(content)):
            raise RuntimeError('Placeholder or custom axiom in ' + name)
        modules.append(name)
    else:
        given[name] = dict(source_sha256=sha(src), source_dependency_fingerprint=fingerprint)

visit('Section5.Library')
(BUILD / 'given-inputs.json').write_text(json.dumps(given, indent=2) + '\n')
rows = []

# Ask Lean to load precisely the non-Section-5 import boundary and resolve the
# complete compiled closure. Earlier mathematics remains given, not rebuilt.
external_imports = set()
section5_deps = {}
for name in modules:
    content = code_only((ROOT / (name.replace('.', '/') + '.lean')).read_text(encoding='utf-8'))
    imports = re.findall(r'^\s*import ([\w.]+)\s*$', content, re.M)
    section5_deps[name] = [dep for dep in imports if dep.startswith('Section5.')]
    external_imports.update(dep for dep in imports if not dep.startswith('Section5.'))

probe = BUILD / 'ImportProviders.lean'
probe_result = BUILD / 'resolved-imports.json'
probe.write_text('\n'.join('import ' + name for name in sorted(external_imports)) + '''
open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for moduleName in env.header.moduleNames do
    let path ← Lean.findOLean moduleName
    rows := rows.push <| Json.mkObj [("module", toJson moduleName.toString),
      ("olean", toJson path.toString)]
  IO.FS.writeFile ''' + json.dumps(str(probe_result)) + ''' (toJson rows).pretty
''', encoding='utf-8')

def resolve_given(label):
    probe_result.unlink(missing_ok=True)
    with (BUILD / (label + '.log')).open('w', encoding='utf-8') as stream:
        rc = subprocess.run(['lean', '-j1', str(probe)], cwd=ROOT, env=env,
                            stdout=stream, stderr=subprocess.STDOUT).returncode
    if rc != 0 or not probe_result.exists():
        raise RuntimeError('Compiled import provider probe failed: ' + label)
    return providers(json.loads(probe_result.read_text(encoding='utf-8')))

given_providers = resolve_given('ImportProviders.before')
if any(name.startswith('Section5.') for name in given_providers):
    raise RuntimeError('Earlier-section boundary unexpectedly imports Section 5')
(BUILD / 'import-providers.json').write_text(json.dumps(dict(schema=SCHEMA,
    lean_path=env['LEAN_PATH'], providers=given_providers), indent=2) + '\n')
given_stamps = file_stamps(given_providers)
provider_key = digest(dict(schema=SCHEMA, lean_path=env['LEAN_PATH'],
    providers=given_providers, verifier_sha256=sha(Path(__file__)),
    provenance_helper_sha256=sha(ROOT / 'scripts/lean_provenance.py')))

def compiled_dependencies(name):
    result = {}
    def collect(dep):
        if dep in result:
            return
        path = LIB / (dep.replace('.', '/') + '.olean')
        # LIB is the first search path and every Section 5 dependency has
        # already been checked in topological order into this directory.
        result[dep] = dict(olean=str(path), artifacts=artifacts(path))
        for child in section5_deps[dep]:
            collect(child)
    for dep in section5_deps[name]:
        collect(dep)
    return result

def run(name, source, output=None, fingerprint=None, fresh=False):
    before = sha(source)
    if before != scanned_sources[name]:
        raise RuntimeError('Source changed after dependency scan: ' + name)
    log = BUILD / (name + '.log')
    entry = cache.get(name, {})
    dependencies = compiled_dependencies(name)
    fingerprint = digest(dict(source_fingerprint=fingerprint, provider_key=provider_key,
                              section5_providers=dependencies))
    if file_stamps(given_providers) != given_stamps:
        raise RuntimeError('Given compiled provider changed during verification')
    dependency_stamps = file_stamps(dependencies)
    reused = bool(not fresh and output and cache_matches(entry, fingerprint, output, log))
    if reused:
        rc = 0
    else:
        cmd = ['lean', '-j1']
        if output:
            output.parent.mkdir(parents=True, exist_ok=True)
            cmd += ['-o', str(output)]
        cmd += [str(source)]
        with log.open('w', encoding='utf-8') as stream:
            rc = subprocess.run(cmd, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    text = log.read_text(encoding='utf-8')
    if sha(source) != before:
        raise RuntimeError('Source changed during check: ' + name)
    if file_stamps(given_providers) != given_stamps or file_stamps(dependencies) != dependency_stamps:
        raise RuntimeError('Compiled import changed during check: ' + name)
    bad = rc != 0 or bool(re.search(r'\berror(?:\(|:)|\b(?:sorry|sorryAx|admit)\b', text))
    rows.append(dict(module=name, source_sha256=before, compiler_exit=rc, passed=not bad, reused=reused,
        validation=('cached source compilation and recorded kernel replay' if reused and entry.get('kernel_recheck')
                    else 'matching compiled cache' if reused else 'fresh source compilation'),
        kernel_recheck=entry.get('kernel_recheck') if reused else None))
    (BUILD / 'results.json').write_text(json.dumps(dict(lean=version,
        given_previous_section_imports=sorted(given), files=rows), indent=2) + '\n')
    print(name + ': ' + ('FAIL' if bad else 'PASS') + (' (matching cache)' if reused else ''), flush=True)
    if bad:
        (BUILD / 'status.txt').write_text('FAIL\n')
        print(text, flush=True)
        raise SystemExit(1)
    if output and not reused:
        cache[name] = dict(schema=SCHEMA, fingerprint=fingerprint,
            provider_key=provider_key, section5_providers=dependencies,
            output_artifacts=artifacts(output), log_sha256=sha(log))
        cache_path.write_text(json.dumps(cache, indent=2) + '\n')
    return text

for name in modules:
    run(name, ROOT / (name.replace('.', '/') + '.lean'),
        LIB / (name.replace('.', '/') + '.olean'), fingerprints[name], fresh=name=='Section5.Library')

if resolve_given('ImportProviders.after') != given_providers:
    raise RuntimeError('Resolved compiled import providers changed during verification')

headlines = [
    'hull_idem', 'isRVPullback_iff', 'canonical_injective', 'canonical_image_pullback',
    'tagged_hull', 'FocusGeometry.center_sameRV', 'FocusGeometry.eta_injOn',
    'rvCode_eq', 'subCode_eq', 'canonicalMap', 'canonicalImage_carrier', 'keyMap', 'hull_definable',
    'subtractMap', 'Focus.centerMap', 'Focus.etaMap', 'Focus.etaMap_injective',
    'Primitive.bijective', 'Chain.bijective', 'SpecialBijection.bijective',
    'SpecialBijection.equiv', 'SpecialBijection.inverseMap', 'SpecialBijection.inverse_apply',
    'SpecialBijection.apply_inverse', 'SpecialBijection.length_comp',
    'contractionMap', 'contractionMap_spec', 'exists_unique_definable_contraction',
    'root_factor_rv_eq', 'barycentric_code_controls_factors',
    'unary_polynomial_rv_of_barycentric_code',
    'rv_add_back', 'FocusGeometry.eta_target_strict', 'FocusGeometry.image_pullback',
    'SpecialBijection.preserves_pullback', 'FocusGeometry.unary_sub', 'Chain.labels_eq_of',
    'Chain.sameRV_of', 'Chain.unary_sub', 'SpecialBijection.inverse_contractible',
    'SpecialBijection.unary_inverse_fibre', 'SpecialBijection.remark_5_3',
    'normalizeVFEquiv', 'mean_normalize', 'mean_definable_normalized', 'mean_sameRV',
    'rootFocusGeometry', 'rootBound_step', 'FiniteRootSet.focus', 'FiniteRootSet.iterate',
    'FiniteRootSet.centralize_tagged', 'FiniteRootSet.centralize_after',
    'polynomial_contractible_of_zero_roots', 'polynomialCode_definable',
    'polynomialZeroSet_finite', 'scalarContractible_iff', 'theorem_5_4_unary',
    'Focus.restrict', 'SpecialBijection.restrict_at', 'RootFamily.focus',
    'RootFamily.step_bound', 'RootFamily.iterate', 'RootFamily.centralize_after',
    'RootFamily.centralize_boundary', 'rawUnarySet_definable', 'lemma_5_2_at_boundary',
    'lemma_5_2', 'lemma_5_2_after', 'Chain.append_assoc', 'Chain.append_suffix_alternating',
    'theorem_5_5_unary',
    'SpecialBijection.comp_toMap', 'SpecialBijection.comp_inverseMap',
    'ScalarContractible.refine', 'theorem_5_5_unary_finite',
    'dropHeadMap', 'dropHead_preimage_definable', 'Focus.lift', 'Focus.lift_eta',
    'Focus.lift_eta_replace_head', 'Chain.lift_dropHead', 'pullback_of_headKey_image',
    'RootFamily.image_fibre_cover', 'RootFamily.push', 'RootFamily.push_bound',
    'relation_contractible_of_zero_obstacles', 'unary_relation_preparation',
    'point_code_iff', 'mean_definable_index', 'headKeyMap',
    'VerticalRootFamily.verticalHull_definable', 'VerticalRootFamily.geometry',
    'VerticalRootFamily.rawFamily_definable', 'VerticalRootFamily.meanMap',
    'VerticalRootFamily.focus', 'VerticalRootFamily.step', 'VerticalRootFamily.step_bound',
    'VerticalRootFamily.step_tagged', 'FocusGeometry.headBlind_sub', 'Focus.lift_headBlind',
    'Primitive.tail_forward', 'Chain.TailProgram.forward', 'Chain.TailProgram.replace_head',
    'Chain.headCompatible_sub', 'Chain.lift_dropHead_compatible',
    'SpecialBijection.compatible_inverse_slice', 'VerticalRootFamily.pushTail_bound',
    'Chain.lastKind_tagged_at', 'Chain.labelIndex_apply', 'Chain.TailProgram.tagged',
    'finite_mean_child_bound',
    'isRVPullback_zeroVF', 'corollary_5_6_zeroVF', 'unary_relation_preparation_at_boundary',
    'attachRVMap', 'rvGraph', 'mem_rvGraph', 'unaryPoint_eq_of', 'rvGraph_transfer',
    'unary_rvMap_preparation', 'flattenKeyMap', 'unary_map_preparation',
    'unary_rvMap_preparation_at_boundary', 'unary_map_preparation_at_boundary',
    'zero_map_preparation_at_boundary', 'membershipMap', 'membershipMap_eq_iff',
    'Map.extend', 'Map.descend', 'headDescend', 'headDescend_apply', 'headKey_eq_iff',
    'headImage_pullback', 'Chain.lastKind_allTagged', 'SpecialBijection.restrict_prepared_at',
    'vertical_relation_of_zero_obstacles', 'finish_tail_lift', 'prepared_verticalHull',
    'prepare_vertical_locus', 'vertical_centralize', 'headKey_mem_iff', 'dropHead_headTag',
    'vertical_rvGraph_transfer', 'Map.transportImage', 'restricted_image_mem_iff',
    'vertical_graph_image', 'complete_head_preparation', 'restrict_prepared_map',
    'tagged_rvMap_preparation', 'rvPreparation_zero', 'rvPreparation_succ', 'rvPreparation_all',
    'map_preparation_at_boundary', 'map_preparation', 'corollary_5_6',
    'PolynomialExpression.expression_eval', 'mvPolynomialCode_eq', 'mvPolynomialCode_definable',
    'mvPolynomialTupleMap', 'theorem_5_5_finite', 'theorem_5_5', 'theorem_5_4',
    'rawPointMap', 'rawKeyFlattenMap', 'rawKeyMap', 'rawRVProjectionMap', 'pullbackObject',
    'normalized_tupleRV', 'canonicalRawMap_mem_lift', 'pullbackLiftMap_bijective',
    'pullbackObject_finiteVolume', 'deformed_pullback_is_lift',
    'lift_representation_of_reduction', 'finite_lift_representation_of_reduction',
    'corollary_5_7', 'corollary_5_7_finite', 'keyTags_definable', 'taggedAmbient_pullback',
    'exists_taggedAmbient',
]
headlines += [
    'Focus.extendBase',
    'Primitive.extendBase',
    'Primitive.extendBase_apply',
    'Primitive.extendBase_kind',
    'Chain.extendBase',
    'Chain.extendBase_alternating',
    'Chain.extendBase_apply',
    'Chain.extendBase_lastKind',
    'SpecialBijection.extendBase',
    'SpecialBijection.extendBase_inverse',
    'GammaChainDefinable.source',
    'GammaChainDefinable.target',
    'GammaPrimitiveDefinable.extendBase',
    'GammaChainDefinable.extendBase',
    'GammaSpecialBijection.source_definable',
    'GammaSpecialBijection.target_definable',
    'GammaGraphDefinable.congr',
    'GammaScalarGraphDefinable.congr',
    'GammaLogicInput.image_real',
    'GammaLogicInput.preimage_real',
    'GammaLogicInput.hull',
    'GammaFocusDefinable.of_real',
    'GammaFocusDefinable.restrict',
    'affineGraphMap',
    'gamma_eta_graph',
    'GammaPrimitiveDefinable.source',
    'GammaPrimitiveDefinable.graph',
    'GammaPrimitiveDefinable.target',
    'GammaPrimitiveDefinable.of_real',
    'GammaChainDefinable.of_real',
    'gamma_restrict_primitive',
    'gamma_restrict_chain',
    'SpecialBijection.restrict_gamma_at',
    'GammaChainDefinable.graph',
    'gamma_inverse_graph',
    'gamma_restrict_prepared_map',
    'gamma_rvMap_preparation_at_boundary',
    'postcomposeRealMap',
    'postcomposeRealMap_apply',
    'gamma_postcompose_real',
    'gamma_map_preparation_at_boundary',
    'gamma_map_preparation',
    'corollary_5_6_gamma',
    'theorem_5_5_finite_gamma',
    'theorem_5_5_gamma',
    'theorem_5_4_gamma',
    'GammaIso.congr',
    'GammaIso.trans',
    'GammaIso.symm',
    'GammaSpecialBijection.iso',
    'rvCoordinatePointMap',
    'gamma_pullback_domain',
    'gammaPullbackObject',
    'GammaIso.target_definable',
    'gamma_pullback_iso',
    'gamma_deformed_pullback_is_lift',
    'corollary_5_7_gamma',
    'corollary_5_7_finite_gamma',
    'flatKey_eq_iff',
    'gamma_contraction_graph',
    'contractionRelation_unique',
    'keyContraction',
    'keyContraction_graph',
    'gamma_keyContraction_graph',
    'keyContraction_spec',
    'exists_unique_gamma_contraction',
    'nonzeroTag',
    'nonzeroTag_pullback',
    'nonzeroTag_definable',
    'printedSharp',
    'printedTarget',
    'Focus.withoutZero',
    'Focus.withoutZero_nonzero',
    'Focus.withoutZero_eta',
    'Focus.withoutZero_image',
    'Focus.eta_printedTarget',
    'Focus.withoutZero_printedTarget',
    'GammaFocusDefinable.withoutZero',
    'Primitive.NonzeroLoci',
    'Primitive.withoutZero',
    'Primitive.withoutZero_nonzero',
    'Primitive.withoutZero_kind',
    'Primitive.withoutZero_length',
    'Primitive.withoutZero_toMap',
    'Primitive.withoutZero_gamma',
    'Chain.NonzeroLoci',
    'Chain.withoutZero',
    'Chain.withoutZero_nonzero',
    'Chain.withoutZero_toMap',
    'Chain.withoutZero_length',
    'Chain.withoutZero_alternating',
    'Chain.withoutZero_gamma',
    'SpecialBijection.withoutZero',
    'SpecialBijection.withoutZero_nonzero',
    'SpecialBijection.withoutZero_toMap',
    'SpecialBijection.withoutZero_inverseMap',
    'SpecialBijection.withoutZero_length',
    'SpecialBijection.paper_representative',
    'SpecialBijection.paper_representative_gamma',
    'GammaSpecialBijection.withoutZero',
    'GammaSpecialBijection.withoutZero_spec',
    'Focus.printedSharp_disjoint_hull',
    'Focus.printedTarget_disjoint',
]
library_text = (ROOT / 'Section5/Library.lean').read_text(encoding='utf-8')
for headline in headlines:
    if '#print axioms SpecialTransformations.Section5.' + headline not in library_text:
        raise RuntimeError('Missing library headline audit: ' + headline)
text = (BUILD / 'Section5.Library.log').read_text(encoding='utf-8')
audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", text)
audits += [(name, '') for name in re.findall(r"'([^'\n]+)' does not depend on any axioms", text)]
expected_audits = {'SpecialTransformations.Section5.' + name for name in headlines}
if len(audits) != len(headlines) or {name for name, _ in audits} != expected_audits:
    raise RuntimeError('Incomplete headline audit')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, block in audits:
    if set(filter(None, (a.strip() for a in block.split(',')))) - allowed:
        raise RuntimeError('Unexpected axiom: ' + name)
for name in modules:
    if sha(ROOT / (name.replace('.', '/') + '.lean')) != next(
            r['source_sha256'] for r in rows if r['module'] == name):
        raise RuntimeError('Source changed after check: ' + name)
(BUILD / 'status.txt').write_text('PASS\n')
print('PASS: Section 5 modules, fresh library import, headline types and allowed axioms.', flush=True)
