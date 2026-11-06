"""Regression checks for compiled-provider cache acceptance."""
from pathlib import Path
import ast
import json
import re
import tempfile
import unittest
from unittest.mock import Mock
from lean_provenance import SCHEMA, artifacts, cache_matches, digest, file_stamps, providers, sha


class ProvenanceTests(unittest.TestCase):
    def test_verifier_cache_hit_retains_replay_evidence(self):
        """Exercise each present section verifier twice on an actual cache hit."""
        root = Path(__file__).resolve().parents[1]
        checked = 0
        for section in ['Section4', 'Section5']:
            verifier = root / section / 'verify.py'
            if not verifier.is_file():
                continue
            checked += 1
            with self.subTest(section=section), tempfile.TemporaryDirectory() as tmp:
                tree = ast.parse(verifier.read_text(encoding='utf-8'))
                run = next(node for node in tree.body
                           if isinstance(node, ast.FunctionDef) and node.name == 'run')
                build = Path(tmp)
                source, output = build / 'Checked.lean', build / 'Checked.olean'
                log, evidence = build / 'Checked.log', build / 'Replay.log'
                source.write_text('def checked := 1', encoding='utf-8')
                output.write_bytes(b'previously checked output')
                log.write_text('compiler exit zero', encoding='utf-8')
                evidence.write_text('kernel replay exit zero', encoding='utf-8')
                fingerprint = digest(dict(source_fingerprint='source', provider_key='providers',
                    **{section.lower() + '_providers': {}}))
                entry = dict(schema=SCHEMA, fingerprint=fingerprint,
                    output_artifacts=artifacts(output), log_sha256=sha(log),
                    kernel_recheck=dict(exit=0, evidence={str(evidence): sha(evidence)}))
                cache = {'Checked': entry}
                cache_path = build / 'cache.json'
                cache_path.write_text(json.dumps(cache), encoding='utf-8')
                no_compiler = Mock()
                no_compiler.run.side_effect = AssertionError('Cache hit invoked the compiler')
                scope = dict(BUILD=build, ROOT=build, scanned_sources={'Checked': sha(source)},
                    cache=cache, compiled_dependencies=lambda name: {}, digest=digest,
                    provider_key='providers', pin_key='test-pins', file_stamps=file_stamps,
                    given_providers={}, given_stamps={}, cache_matches=cache_matches,
                    sha=sha, artifacts=artifacts, rows=[], version='test', given={},
                    json=json, re=re, subprocess=no_compiler, env={}, cache_path=cache_path)
                exec(compile(ast.Module(body=[run], type_ignores=[]), str(verifier), 'exec'), scope)
                for _ in range(2):
                    scope['run']('Checked', source, output, 'source')
                    self.assertEqual(cache['Checked'], entry)
                    self.assertEqual(json.loads(cache_path.read_text())['Checked'], entry)
                    self.assertEqual(scope['rows'][-1]['kernel_recheck'], entry['kernel_recheck'])
                    self.assertTrue(scope['rows'][-1]['reused'])
                no_compiler.run.assert_not_called()
        self.assertGreater(checked, 0)

    def test_provider_path_content_and_split_parts(self):
        with tempfile.TemporaryDirectory() as tmp:
            a, b = Path(tmp) / 'a.olean', Path(tmp) / 'b.olean'
            a.write_bytes(b'same compiled content')
            b.write_bytes(a.read_bytes())
            snap = lambda p: digest(providers([dict(module='Given.Input', olean=str(p))]))
            original = snap(a)
            self.assertEqual(original, snap(a))
            self.assertNotEqual(original, snap(b))
            a.write_bytes(b'changed compiled content')
            self.assertNotEqual(original, snap(a))
            changed = snap(a)
            Path(str(a) + '.private').write_bytes(b'private implementation')
            self.assertNotEqual(changed, snap(a))
            split = snap(a)
            a.with_suffix('.ir').write_bytes(b'interpreter code')
            self.assertNotEqual(split, snap(a))

    def test_cache_requires_new_schema_all_outputs_and_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            out, log = Path(tmp) / 'Checked.olean', Path(tmp) / 'Checked.log'
            out.write_bytes(b'checked')
            log.write_text('exit zero', encoding='utf-8')
            entry = dict(schema=SCHEMA, fingerprint='imports and source',
                         output_artifacts=artifacts(out), log_sha256=sha(log))
            self.assertTrue(cache_matches(entry, 'imports and source', out, log))
            self.assertFalse(cache_matches(entry, 'different imports', out, log))
            self.assertFalse(cache_matches({**entry, 'schema': 1}, entry['fingerprint'], out, log))
            log.write_text('modified', encoding='utf-8')
            self.assertFalse(cache_matches(entry, entry['fingerprint'], out, log))
            entry['log_sha256'] = sha(log)
            out.write_bytes(b'changed output')
            self.assertFalse(cache_matches(entry, entry['fingerprint'], out, log))

    def test_kernel_recheck_evidence_is_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            out, log, replay = (Path(tmp) / name for name in
                                ['Checked.olean', 'Checked.log', 'Replay.log'])
            out.write_bytes(b'checked')
            log.write_text('source compiler exited zero')
            replay.write_text('kernel replay passed')
            entry = dict(schema=SCHEMA, fingerprint='bound inputs',
                         output_artifacts=artifacts(out), log_sha256=sha(log),
                         kernel_recheck=dict(exit=0, evidence={str(replay): sha(replay)}))
            self.assertTrue(cache_matches(entry, 'bound inputs', out, log))
            replay.write_text('changed receipt')
            self.assertFalse(cache_matches(entry, 'bound inputs', out, log))


if __name__ == '__main__':
    unittest.main()
