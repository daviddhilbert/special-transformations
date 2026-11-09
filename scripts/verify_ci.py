#!/usr/bin/env python3
"""Audit published headlines after `lake build`; run with `lake env python3`."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
QE_HEADLINES = [
    'JohnsonACF.hasQEb',
    'hasQE_ACVF_val',
    'hasQEb_ACVF_val',
    'SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination',
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('scope', choices=('qe', 'section9'), nargs='?', default='qe')
    args = parser.parse_args()
    if args.scope == 'section9':
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
        audits = re.findall(
            r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(headlines) or {name for name, _ in audits} != set(headlines):
            raise RuntimeError('Incomplete or unexpected headline axiom audit')
        records = []
        for name, block in audits:
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
        main()
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
