#!/usr/bin/env python3
"""Audit published QE headlines after `lake build`; run with `lake env python3`."""

import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.scratch' / 'ci-verified'
HEADLINES = [
    'JohnsonACF.hasQEb',
    'hasQE_ACVF_val',
    'hasQEb_ACVF_val',
    'SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    status = OUT / 'status.txt'
    status.write_text('RUNNING\n', encoding='utf-8')
    try:
        source = OUT / 'HeadlineAudit.lean'
        source.write_text(
            'import SpecialTransformations\nset_option pp.explicit true\n'
            + '\n'.join('#check @' + h + '\n#print axioms ' + h for h in HEADLINES)
            + '\n', encoding='utf-8')
        result = subprocess.run(
            ['lean', str(source)], cwd=ROOT, capture_output=True, text=True,
            encoding='utf-8', errors='replace')
        output = result.stdout + result.stderr
        (OUT / 'HeadlineAudit.log').write_text(output, encoding='utf-8')
        print(output, end='')
        if result.returncode or re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Headline compilation or diagnostics failed')
        audits = re.findall(
            r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(HEADLINES) or {name for name, _ in audits} != set(HEADLINES):
            raise RuntimeError('Incomplete or unexpected headline axiom audit')
        records = []
        for name, block in audits:
            axioms = {x.strip() for x in block.split(',') if x.strip()}
            if axioms - ALLOWED:
                raise RuntimeError('Unexpected axioms for ' + name + ': ' + str(axioms - ALLOWED))
            records.append({'name': name, 'axioms': sorted(axioms)})
        (OUT / 'headlines.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print('PASS: published QE headline types and allowed axioms; section coverage is separate.')
    except Exception:
        status.write_text('FAIL\n', encoding='utf-8')
        raise


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
