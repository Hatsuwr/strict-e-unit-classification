#!/usr/bin/env python3
"""Offline runner regressions. Fake compiler only; no Lean replay is claimed."""
from pathlib import Path
import contextlib
import io
import json
import tempfile
import unittest
from unittest.mock import patch
import rebuild
from check_package import digest


class ExportChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.output = self.root / 'A.olean'
        self.output.write_bytes(b'accepted A')
        self.accepted = {'A': digest(self.output)}

    def tearDown(self):
        self.temp.cleanup()

    def test_accepted_dependency_passes(self):
        self.assertEqual(rebuild.dependency_hashes(self.root, ['A'], self.accepted), self.accepted)

    def test_unaccepted_dependency_rejected(self):
        with self.assertRaisesRegex(ValueError, 'not been accepted'):
            rebuild.dependency_hashes(self.root, ['A'], {})

    def test_changed_dependency_before_import_rejected(self):
        self.output.write_bytes(b'tampered')
        with self.assertRaisesRegex(ValueError, 'export changed'):
            rebuild.dependency_hashes(self.root, ['A'], self.accepted)

    def test_missing_or_symlink_export_rejected(self):
        self.output.unlink()
        with self.assertRaisesRegex(ValueError, 'export changed'):
            rebuild.check_exports(self.root, self.accepted)
        other = self.root / 'other'; other.write_bytes(b'accepted A')
        self.output.symlink_to(other)
        with self.assertRaisesRegex(ValueError, 'export changed'):
            rebuild.check_exports(self.root, self.accepted)


class RunnerChecks(unittest.TestCase):
    def run_fixture(self, mode=None):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'project').mkdir()
            manifest_path = root / 'SOURCE_MANIFEST.json'
            manifest_path.write_text('fixed manifest')
            lean = root / 'lean'; lean.write_text('fake compiler')
            modules = ['A', 'B', 'C']
            for module in modules:
                (root / 'project' / (module + '.lean')).write_text('-- ' + module)
            sources = {'module_order': modules, 'audit_results': {}, 'modules': {
                m: {'sha256': digest(root / 'project' / (m + '.lean'))} for m in modules}}
            edges = {'A': [], 'B': ['A'], 'C': []}
            invoked = []

            def fake_popen(command, **kwargs):
                output = Path(command[command.index('-o') + 1])
                module = output.stem
                invoked.append(module)
                output.write_bytes(('compiled ' + module).encode())
                if mode == 'during_import' and module == 'B':
                    (output.parent / 'A.olean').write_bytes(b'changed during B')
                if mode == 'terminal_export' and module == 'C':
                    (output.parent / 'B.olean').write_bytes(b'changed later')
                if mode == 'manifest' and module == 'A':
                    manifest_path.write_text('changed manifest')

                class Child:
                    returncode = 0
                    def poll(self): return 0
                return Child()

            real_dependencies = rebuild.dependency_hashes

            def dependencies(objects, imported, accepted):
                if mode == 'before_import' and imported:
                    (objects / 'A.olean').write_bytes(b'changed before B')
                return real_dependencies(objects, imported, accepted)

            with patch.object(rebuild, 'ROOT', root), \
                 patch.object(rebuild, 'source_checks', return_value=(sources, edges)), \
                 patch.object(rebuild, 'inspect_environment', return_value=(root, [], {})), \
                 patch.object(rebuild, 'snapshot_external', return_value={}), \
                 patch.object(rebuild, 'dependency_hashes', side_effect=dependencies), \
                 patch.object(rebuild.subprocess, 'Popen', side_effect=fake_popen), \
                 patch.object(rebuild.sys, 'argv', ['rebuild.py', '--lean', str(lean)]), \
                 contextlib.redirect_stdout(io.StringIO()):
                try:
                    if mode is None:
                        rebuild.main()
                        result = json.loads(next((root / 'replay').glob('*/result.json')).read_text())
                        self.assertEqual(result['status'], 'FRESH_REPLAY_PASS')
                        self.assertTrue(result['final_project_exports_rechecked_after_run'])
                        self.assertEqual(result['accepted'], modules)
                    else:
                        with self.assertRaises(ValueError): rebuild.main()
                        result = json.loads(next((root / 'replay').glob('*/result.json')).read_text())
                        self.assertNotEqual(result['status'], 'FRESH_REPLAY_PASS')
                        if mode == 'before_import': self.assertEqual(invoked, ['A'])
                finally:
                    rebuild.ACTIVE_RUN = None

    def test_complete_fake_run(self): self.run_fixture()
    def test_tamper_before_dependent_compile(self): self.run_fixture('before_import')
    def test_tamper_during_dependent_compile(self): self.run_fixture('during_import')
    def test_terminal_export_rehash(self): self.run_fixture('terminal_export')
    def test_frozen_source_manifest(self): self.run_fixture('manifest')


if __name__ == '__main__': unittest.main()
