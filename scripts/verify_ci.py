#!/usr/bin/env python3
"""Audit published headlines after `lake build`; run with `lake env python3`."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
QE_HEADLINES = [
    'JohnsonACF.hasQEb',
    'hasQE_ACVF_val',
    'hasQEb_ACVF_val',
    'SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination',
    'ValPM.hasQE_ACVF_trivial_val',
    'ValPM.hasQEb_ACVF_trivial_val',
    'SpecialTransformations.TrivialRV.canonical_trivial_rv_qe',
    'SpecialTransformations.TrivialRV.hasQE',
]
SECTION9_HEADLINES = [
    'lemma_9_2',
    'lemma_9_3',
    'lemma_9_4',
    'lemma_9_5',
    'HasVFDerivativeAt.comp',
    'lemma_9_8',
    'corollary_9_9',
    'lemma_9_11_ae',
    'lemma_9_11_zero_arity',
    'mixedVFJacobian_comp_of_full_derivative',
    'lemma_9_12_ae',
    'lemma_9_12_zero_arity',
    'rvEssentialIso',
    'rvEssentialLift_complement_dim_lt',
    'IsRVJacobianAt.gamma_eq',
    'rvGammaJacobian_comp',
    'exists_definable_generic_RVJacobian',
    'rvJacobian_chain_ae_finite_volume',
    'rvJacobian_chain_zero_arity',
    'lemma_9_15_finite_volume_of_reference_input',
    'lemma_9_15_zero_arity',
    'theorem_9_16_finite_volume_of_reference_input',
    'exists_prescribed_lift_zero_arity',
    'gammaDescent_polydiscs_of_vfSmall_exception',
    'acvf_henselizedGaussGraphInput_of_finite_extension_reference',
    'monomialPermutation_bijOn_and_changes_sum',
]
SECTION9_DEFINITIONS = [
    'IsLimitSet', 'IsMinimalLimitSet', 'HasVFDerivativeAt', 'HasVFJacobianAt',
    'HasMixedVFJacobianAt', 'rvEssential', 'IsRVJacobianAt', 'rvGammaJacobian',
    'FiniteHenselianExtensionReference',
]
SECTION9_SUPPORT_HEADLINES = [
    'Section3.RawClosure.Tuple.definable_choice_graph',
    'Section3.RawClosure.Tuple.definable_choice_graph_over',
    'Section7.generatedBase_rv_representative',
    'Section7.definable_rv_representative_of_algebraic_lift',
    'Section7.exists_localPolynomialSystem',
    'Section7.exists_weightedLocalPolynomialSystem',
    'Section7.exists_correspondence_local_polynomials',
    'Section7.exists_correspondence_weighted_local_polynomials',
    'Section7.rvLift_isomorphic_of_volume_lift',
    'Section7.exists_liftMap_of_volume_lift',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LIBRARY_SECTIONS = (5, 6, 7, 8, 10)


def run_workflow_audits(independent):
    """Audit the completed Lake build, with optional independent source checks."""
    verifier_flags = () if independent else ('--audit-built',)
    checks = {
        'foundation': ('scripts/verify_ci.py', 'qe'),
        'section3': ('Section3/verify.py', *verifier_flags),
        'section4': ('Section4/verify.py', *verifier_flags),
        'section5': ('Section5/verify.py',) if independent else ('scripts/verify_ci.py', 'section5'),
        'section6': ('scripts/verify_ci.py', 'section6'),
        'section7': ('Section7/verify.py',) if independent else ('scripts/verify_ci.py', 'section7'),
        'section8': ('scripts/verify_ci.py', 'section8'),
        'section9': ('scripts/verify_ci.py', 'section9'),
        'section10': ('scripts/verify_ci.py', 'section10'),
    }
    out = ROOT / '.scratch' / 'ci-verified'
    out.mkdir(parents=True, exist_ok=True)
    workers = min(4, int(os.environ.get('LEAN_NUM_THREADS', '4')))
    env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONUNBUFFERED='1')

    def run(label, args):
        started = time.monotonic()
        with (out / (label + '.log')).open('w', encoding='utf-8') as log:
            result = subprocess.run([sys.executable, *args], cwd=ROOT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        return ('success' if result.returncode == 0 else 'failure',
                time.monotonic() - started)

    outcomes = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(run, label, args): label for label, args in checks.items()}
        for future in as_completed(futures):
            label = futures[future]
            outcome, seconds = future.result()
            outcomes[label] = outcome
            print(f'{label}: {outcome} ({seconds:.1f}s)', flush=True)
            if outcome == 'failure':
                lines = (out / (label + '.log')).read_text(encoding='utf-8', errors='replace').splitlines()
                for line in lines[-40:]:
                    print('  ' + line, flush=True)

    output = os.environ.get('GITHUB_OUTPUT')
    if output:
        with Path(output).open('a', encoding='utf-8') as stream:
            for label in checks:
                stream.write(f'{label}={outcomes[label]}\n')
    return int('failure' in outcomes.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    libraries = {f'section{section}': section for section in LIBRARY_SECTIONS}
    parser.add_argument('scope', choices=('qe', *libraries, 'section9', 'built', 'all'),
                        nargs='?', default='qe')
    args = parser.parse_args()
    if args.scope in ('built', 'all'):
        return run_workflow_audits(independent=args.scope == 'all')
    section = libraries.get(args.scope)
    if section:
        label = f'Section {section}'
        # Keep Lake-build audits separate from independent source certificates.
        out = ROOT / '.scratch' / ('section10-verified' if section == 10 else f'ci-verified/section{section}')
        source = ROOT / f'Section{section}' / 'Library.lean'
        directives = source.read_text(encoding='utf-8')
        headlines = re.findall(r'(?m)^#print axioms (\S+)$', directives)
        types = re.findall(r'(?m)^#check @(\S+)$', directives)
        if (not headlines or set(headlines) != set(types)
                or len(headlines) != len(types) or len(headlines) != len(set(headlines))):
            raise RuntimeError(f'Expected paired and distinct {label} type and axiom directives')
    elif args.scope == 'section9':
        label = 'Section 9'
        out = ROOT / '.scratch' / 'section9-verified'
        prefix = 'SpecialTransformations.Section9.'
        headlines = [prefix + name for name in SECTION9_HEADLINES]
        headlines.extend('SpecialTransformations.' + name for name in SECTION9_SUPPORT_HEADLINES)
        definitions = [prefix + name for name in SECTION9_DEFINITIONS]
        print_options = 'set_option pp.maxSteps 100000\nset_option pp.deepTerms true\n'
    else:
        label = 'published QE'
        out = ROOT / '.scratch' / 'ci-verified'
        headlines = QE_HEADLINES
        definitions = []
        print_options = 'set_option pp.explicit true\n'

    out.mkdir(parents=True, exist_ok=True)
    status = out / 'status.txt'
    status.write_text('RUNNING\n', encoding='utf-8')
    try:
        if not section:
            source = out / 'HeadlineAudit.lean'
            source.write_text(
                'import SpecialTransformations\n'
                + print_options
                + '\n'.join('#print ' + name for name in definitions)
                + '\n'
                + '\n'.join('#check @' + h + '\n#print axioms ' + h for h in headlines)
                + '\n', encoding='utf-8')
        result = subprocess.run(
            ['lean', str(source)], cwd=ROOT, capture_output=True, text=True,
            encoding='utf-8', errors='replace')
        output = result.stdout + result.stderr
        (out / 'HeadlineAudit.log').write_text(output, encoding='utf-8')
        print(output, end='')
        if result.returncode or re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Headline compilation or diagnostics failed')
        if args.scope == 'section10' and any(f'@{name} :' not in output for name in headlines):
            raise RuntimeError('Incomplete Section 10 headline type output')
        audits = re.findall(
            r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(headlines) or {name for name, _ in audits} != set(headlines):
            raise RuntimeError('Incomplete or unexpected headline axiom audit')
        records = []
        for name, block in audits:
            # Some library audits print universe instantiations on axiom names.
            block = re.sub(r'\.\{[^}]*\}', '', block)
            axioms = {x.strip() for x in block.split(',') if x.strip()}
            if axioms - ALLOWED:
                raise RuntimeError('Unexpected axioms for ' + name + ': ' + str(axioms - ALLOWED))
            records.append({'name': name, 'axioms': sorted(axioms)})
        (out / 'headlines.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print(f'PASS: {label} headline types and allowed axioms.')
    except Exception:
        status.write_text('FAIL\n', encoding='utf-8')
        raise


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
