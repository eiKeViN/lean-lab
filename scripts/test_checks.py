#!/usr/bin/env python3
"""Offline rejection regressions for history, pins, evidence, audits and caches."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest

from baseline import ROOT, PROJECT, GitSnapshot, snapshot, configuration, verify_export
from verify import verify_sources, verify_project

spec = importlib.util.spec_from_file_location('project_validation', PROJECT/'validate.py')
validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validator)
(ROOT/'results').mkdir(exist_ok=True)


def source_records():
    rows = [line.split('\t') for line in (ROOT/'provenance/kl-blobs.tsv').read_text().splitlines()]
    upstream = {path: sha for _, sha, path in
                [x.split('\t') for x in (ROOT/'provenance/upstream.manifest.tsv').read_text().splitlines()[1:]]}
    return rows, upstream


class HistoryChecks(unittest.TestCase):
    def test_pristine_blobs_without_checkout(self):
        self.assertFalse((ROOT/'experiments/kl').exists())
        rows, upstream = source_records()
        verify_sources(snapshot('pristine'), rows, upstream)

    def test_reject_changed_expected_blob(self):
        rows, upstream = source_records()
        rows[0][0] = '0'*40
        with self.assertRaises(RuntimeError):
            verify_sources(snapshot('pristine'), rows, upstream)

    def test_reject_missing_source(self):
        rows, upstream = source_records()
        rows.pop()
        with self.assertRaises(RuntimeError):
            verify_sources(snapshot('pristine'), rows, upstream)

    def test_reject_absent_git_blob(self):
        with self.assertRaises(RuntimeError):
            snapshot('pristine').read_bytes('OAI/DoesNotExist.lean')

    def test_reject_missing_commit(self):
        with self.assertRaises(RuntimeError):
            GitSnapshot('test', spec={'commit': '0'*40, 'prefix': 'missing'})

    def test_reject_nonexact_commit(self):
        with self.assertRaises(ValueError):
            GitSnapshot('test', spec={'commit': 'main', 'prefix': 'missing'})

    def test_reject_source_path_escape(self):
        for path in ('../README.md', '/etc/passwd'):
            with self.assertRaises(ValueError):
                snapshot('pristine').read_bytes(path)


class PinChecks(unittest.TestCase):
    def test_active_pins_and_rejections(self):
        with tempfile.TemporaryDirectory(dir=ROOT/'results') as temp:
            p = Path(temp)
            for name in ('lean-toolchain', 'lake-manifest.json'):
                (p/name).write_bytes(snapshot('published').read_bytes(name))
            verify_project(p)
            (p/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
            with self.assertRaises(RuntimeError):
                verify_project(p)
            (p/'lean-toolchain').write_bytes(snapshot('published').read_bytes('lean-toolchain'))
            lock = json.loads((p/'lake-manifest.json').read_text())
            next(d for d in lock['packages'] if d['name'] != 'mathlib')['rev'] = '0'*40
            (p/'lake-manifest.json').write_text(json.dumps(lock))
            with self.assertRaises(RuntimeError):
                verify_project(p)

    def test_reject_dependency_symlink(self):
        with tempfile.TemporaryDirectory(dir=ROOT/'results') as temp:
            p = Path(temp)
            for name in ('lean-toolchain', 'lake-manifest.json'):
                (p/name).write_bytes(snapshot('published').read_bytes(name))
            (p/'.lake').mkdir()
            (p/'.lake/packages').symlink_to(PROJECT/'.lake/packages')
            with self.assertRaises(RuntimeError):
                verify_project(p)


class ExportEvidenceChecks(unittest.TestCase):
    def test_verified_archive(self):
        self.assertEqual(hashlib.sha256(verify_export()).hexdigest(), configuration()['reference_export']['sha256'])

    def test_reject_archive_corruption(self):
        with tempfile.TemporaryDirectory(dir=ROOT/'results') as temp:
            p = Path(temp)
            meta = copy.deepcopy(configuration()['reference_export'])
            data = (ROOT/meta['path']).read_bytes()
            meta['path'] = 'export.gz'
            (p/meta['path']).write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
            with self.assertRaises(RuntimeError):
                verify_export(p, meta)

    def test_reject_wrong_content_hash_and_count(self):
        meta = copy.deepcopy(configuration()['reference_export'])
        meta['sha256'] = '0'*64
        with self.assertRaises(RuntimeError):
            verify_export(metadata=meta)
        meta = copy.deepcopy(configuration()['reference_export'])
        meta['public_count'] = 0
        with self.assertRaises(RuntimeError):
            verify_export(metadata=meta)


class AuditChecks(unittest.TestCase):
    def rows(self):
        return [f"'{name}' depends on axioms: [propext, Quot.sound, Classical.choice]" for name in
                re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$', (PROJECT/'Audit.lean').read_text(), re.M)]

    def test_complete_named_audit(self):
        validator.check_axioms('\n'.join(reversed(self.rows())))

    def test_empty_or_missing_closure(self):
        for text in ('', '\n'.join(self.rows()[:-1])):
            with self.assertRaises(RuntimeError):
                validator.check_axioms(text)

    def test_duplicate_or_substituted_target(self):
        rows = self.rows()
        for replacement in (rows[0], "'Other.theorem' depends on axioms: [propext]"):
            with self.assertRaises(RuntimeError):
                validator.check_axioms('\n'.join(rows[:-1] + [replacement]))

    def test_disallowed_axiom(self):
        for axiom in ('sorryAx', 'Other.axiom'):
            with self.assertRaises(RuntimeError):
                validator.check_axioms('\n'.join(self.rows()).replace('Quot.sound', axiom, 1))

    def test_main_requires_exact_axioms(self):
        rows = self.rows()
        rows = [r.replace(', Classical.choice', '') if "'OAI.KLInvariance.combinatorial_invariance'" in r else r for r in rows]
        with self.assertRaises(RuntimeError):
            validator.check_axioms('\n'.join(rows))


class CacheChecks(unittest.TestCase):
    def test_warm_and_denied_or_incomplete_cache(self):
        with tempfile.TemporaryDirectory(dir=ROOT/'results') as temp:
            p = Path(temp); calls = p/'calls.log'
            (p/'lake').write_text('''#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$MOCK_CALLS"
if [[ "$*" == '--no-build build Mathlib' ]]; then exit "$MOCK_READY"; fi
if [[ "$*" == 'exe cache get Mathlib' ]]; then exit "$MOCK_DOWNLOAD"; fi
exit 99
''')
            (p/'curl').write_text('#!/usr/bin/env bash\necho unexpected-network >> "$MOCK_CALLS"\nexit 97\n')
            for name in ('lake', 'curl'):
                (p/name).chmod(0o755)
            for ready, download, expected in ((0, 99, 0), (1, 22, 22), (1, 0, 1)):
                calls.write_text('')
                env = dict(os.environ, PATH=str(p)+':'+os.environ['PATH'], MOCK_CALLS=str(calls),
                           MOCK_READY=str(ready), MOCK_DOWNLOAD=str(download))
                env.pop('CACHE_PROBE_URL', None)
                result = subprocess.run(['bash', str(ROOT/'scripts/cache.sh')], env=env, capture_output=True)
                self.assertEqual(result.returncode, expected)
                self.assertNotIn('unexpected-network', calls.read_text())
                if ready == 0:
                    self.assertEqual(calls.read_text().splitlines(), ['--no-build build Mathlib'])
            calls.write_text('')
            env.update(MOCK_READY='1', CACHE_PROBE_URL='https://cache.example.invalid/artifact')
            result = subprocess.run(['bash', str(ROOT/'scripts/cache.sh')], env=env, capture_output=True)
            self.assertEqual(result.returncode, 97)
            self.assertNotIn('exe cache get Mathlib', calls.read_text())


if __name__ == '__main__':
    unittest.main()
