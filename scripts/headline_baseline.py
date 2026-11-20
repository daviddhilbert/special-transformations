"""Compare audited headline statements with the committed baseline.

Each suite's baseline is `verification/headline-types/<suite>.txt`. For every
audited headline, in sorted order, it records the SHA-256 of the full type
printed with `pp.explicit`, `pp.fullNames` and `pp.deepTerms`, followed by the
readable type printed without `pp.explicit`. A changed, added or removed
headline statement therefore fails even when its axioms stay clean.

Set `UPDATE_HEADLINE_BASELINE=1` only after reviewing an intended statement
change; the run then rewrites the baseline instead of comparing.
"""
import difflib
import hashlib
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
BASELINES = ROOT / 'verification' / 'headline-types'
OPTIONS = ('set_option pp.fullNames true\nset_option pp.deepTerms true\n'
           'set_option pp.maxSteps 1000000\n')


def _blocks(output):
    """Split `#check` output into messages; continuation lines are indented."""
    blocks = []
    for line in output.splitlines():
        if line and not line[0].isspace():
            blocks.append([line])
        elif blocks:
            blocks[-1].append(line)
        elif line.strip():
            raise RuntimeError('Unexpected headline type output: ' + line)
    return ['\n'.join(b).rstrip() for b in blocks]


def render(suite, names, imports, env=None, scratch=None):
    """Return the baseline text for `names`, printed from `imports`."""
    names = sorted(set(names))
    scratch = Path(scratch or ROOT / '.scratch' / 'headline-types')
    scratch.mkdir(parents=True, exist_ok=True)
    source = scratch / f'{suite}-HeadlineTypes.lean'
    checks = ''.join(f'#check @{name}\n' for name in names)
    source.write_text(''.join(f'import {m}\n' for m in imports) + OPTIONS + checks
                      + 'set_option pp.explicit true\n' + checks, encoding='utf-8')
    result = subprocess.run(['lean', str(source)], cwd=ROOT, env=env, capture_output=True,
                            text=True, encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    (scratch / f'{suite}-HeadlineTypes.log').write_text(output, encoding='utf-8')
    if result.returncode or re.search(r'\berror\b', output):
        raise RuntimeError(f'{suite} headline type printing failed:\n{output[-4000:]}')
    blocks = _blocks(output)
    if len(blocks) != 2 * len(names):
        raise RuntimeError(f'{suite}: expected {2 * len(names)} type messages, got {len(blocks)}')
    lines = []
    for name, plain, explicit in zip(names, blocks, blocks[len(names):]):
        # Lean omits `@` for declarations with no implicit parameters, and
        # prints the resolved name when a headline is reached through an alias.
        printed = {b.split(' :', 1)[0].lstrip('@') for b in (plain, explicit)}
        if len(printed) != 1 or not any(
                p == name or p.endswith('.' + name.rsplit('.', 1)[-1]) for p in printed):
            raise RuntimeError(f'{suite}: type output out of order at {name}')
        digest = hashlib.sha256(explicit.encode('utf-8')).hexdigest()
        lines.append(f'== {name} explicit-sha256:{digest}\n{plain}\n')
    return ''.join(lines)


def check(suite, names, imports, env=None, scratch=None):
    """Fail if the current statements differ from the committed baseline."""
    current = render(suite, names, imports, env, scratch)
    path = BASELINES / f'{suite}.txt'
    count = len(set(names))
    if os.environ.get('UPDATE_HEADLINE_BASELINE') == '1':
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(current, encoding='utf-8')
        print(f'Updated {path.relative_to(ROOT)} ({count} declarations)', flush=True)
        return
    old = path.read_text(encoding='utf-8') if path.exists() else ''
    if old != current:
        diff = list(difflib.unified_diff(old.splitlines(), current.splitlines(),
                                         str(path.relative_to(ROOT)), 'current', lineterm=''))
        print('\n'.join(diff[:400]), flush=True)
        if len(diff) > 400:
            print(f'... {len(diff) - 400} more diff lines', flush=True)
        raise RuntimeError(f'{suite} headline statements differ from the reviewed baseline '
                           f'{path.relative_to(ROOT)}; review, then rerun with '
                           'UPDATE_HEADLINE_BASELINE=1 if the change is intended')
    print(f'{suite}: headline statements match the reviewed baseline ({count} declarations)',
          flush=True)
