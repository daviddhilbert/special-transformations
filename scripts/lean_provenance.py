"""Content identities for Lean's resolved compiled import providers.

The module list and provider paths must come from Lean.findOLean in an actual
imported environment, not from a source-tree dependency approximation.
"""
from pathlib import Path
import hashlib
import json

SCHEMA = 2


def sha(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def artifacts(olean):
    """Include split module parts and interpreter code when present."""
    path = Path(olean).absolute()
    if not path.is_file():
        raise RuntimeError('Missing resolved import: ' + str(path))
    candidates = [path, Path(str(path) + '.private'), Path(str(path) + '.server'),
                  path.with_suffix('.ir')]
    return {str(p): sha(p) if p.is_file() else None for p in candidates}


def providers(rows):
    result = {}
    for row in rows:
        name = row['module']
        if name in result:
            raise RuntimeError('Duplicate imported module: ' + name)
        result[name] = dict(olean=str(Path(row['olean']).absolute()),
                            artifacts=artifacts(row['olean']))
    return result


def cache_matches(entry, fingerprint, output, log):
    replay = entry.get('kernel_recheck')
    replay_ok = replay is None or (replay.get('exit') == 0 and
        all(Path(path).is_file() and sha(path) == expected
            for path, expected in replay.get('evidence', {}).items()) and
        bool(replay.get('evidence')))
    return bool(replay_ok and entry.get('schema') == SCHEMA and Path(output).is_file()
                and Path(log).is_file() and entry.get('fingerprint') == fingerprint
                and entry.get('output_artifacts') == artifacts(output)
                and entry.get('log_sha256') == sha(log))


def file_stamps(provider_map):
    """Reject concurrent provider replacement, creation or removal during a run."""
    paths = {path for row in provider_map.values() for path in row['artifacts']}
    return {path: ((stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_ino)
                   if (stat := Path(path).stat() if Path(path).exists() else None)
                   else None) for path in paths}
