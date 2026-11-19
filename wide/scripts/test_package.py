#!/usr/bin/env python3
# Broad v5 source-package integrity regression tests, 19 November 2026.
"""Offline tamper tests. These tests do not run Lean."""
from pathlib import Path
import json
import tempfile
import unittest
import check_package as package


class SourceIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'project').mkdir()
        self.texts = {
            'A': 'import Mathlib.Tactic\nset_option maxHeartbeats 400000\ntheorem a : True := by trivial\n',
            'B': 'import A\ntheorem b : True := by trivial\n',
        }
        self.manifest = {'roots': ['B'], 'module_order': ['A', 'B'],
                         'external_imports': ['Mathlib.Tactic'],
                         'audit_results': {'B': {'Example.b': ['propext']}}, 'modules': {}}
        for name, text in self.texts.items():
            self.put_source(name, text)
        self.save()

    def tearDown(self):
        self.temp.cleanup()

    def put_source(self, name, text):
        path = self.root / 'project' / (name + '.lean')
        path.write_text(text)
        code = package.lean_code(text)
        self.manifest['modules'][name] = {
            'path': 'project/' + name + '.lean', 'bytes': path.stat().st_size,
            'sha256': package.digest(path), 'imports': package.imports_from_code(code),
            'options': package._options(code)}

    def save(self):
        (self.root / 'SOURCE_MANIFEST.json').write_text(json.dumps(self.manifest))

    def distribution_manifest(self):
        files = {p.relative_to(self.root).as_posix():
                 {'bytes': p.stat().st_size, 'sha256': package.digest(p)}
                 for p in self.root.rglob('*') if p.is_file()}
        (self.root / 'MANIFEST.json').write_text(json.dumps({'files': files}))

    def test_large_pinned_source_option_is_allowed(self):
        manifest, edges = package.source_checks(self.root)
        self.assertEqual(manifest['modules']['A']['options'][0]['value'], '400000')
        self.assertEqual(edges['B'], ['A'])

    def test_changed_source_rejected(self):
        (self.root / 'project/A.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Source mismatch'):
            package.source_checks(self.root)

    def test_genuine_axiom_rejected_even_when_hash_updated(self):
        self.put_source('A', self.texts['A'] + 'axiom invented : False\n')
        self.save()
        with self.assertRaisesRegex(ValueError, 'Disallowed source token'):
            package.source_checks(self.root)

    def test_comments_and_strings_do_not_become_code(self):
        self.put_source('A', self.texts['A'] + '/- unsafe /- axiom nested -/ sorry -/\n'
                        + 'def note : String := "axiom sorry unsafe"\n')
        self.save()
        package.source_checks(self.root)

    def test_changed_option_inventory_rejected(self):
        self.manifest['modules']['A']['options'][0]['value'] = '400001'
        self.save()
        with self.assertRaisesRegex(ValueError, 'option inventory mismatch'):
            package.source_checks(self.root)

    def test_async_elaboration_rejected(self):
        self.put_source('A', self.texts['A'] + 'set_option Elab.async true\n')
        self.save()
        with self.assertRaisesRegex(ValueError, 'Asynchronous elaboration'):
            package.source_checks(self.root)

    def test_kernel_bypass_option_rejected(self):
        self.put_source('A', self.texts['A'] + 'set_option debug.skipKernelTC true\n')
        self.save()
        with self.assertRaisesRegex(ValueError, 'Unapproved source option'):
            package.source_checks(self.root)

    def test_missing_topological_dependency_rejected(self):
        self.manifest['module_order'] = ['B', 'A']
        self.save()
        with self.assertRaisesRegex(ValueError, 'non-topological'):
            package.source_checks(self.root)

    def test_unlisted_lean_source_rejected(self):
        (self.root / 'project/Unrelated.lean').write_text('def extra := 1\n')
        with self.assertRaisesRegex(ValueError, 'source inventory mismatch'):
            package.source_checks(self.root)

    def test_listed_unrelated_source_rejected(self):
        self.put_source('Unused', 'def unused := 0\n')
        self.manifest['module_order'].insert(0, 'Unused')
        self.save()
        with self.assertRaisesRegex(ValueError, 'outside root dependency closure'):
            package.source_checks(self.root)

    def test_case_collision_rejected(self):
        self.put_source('a', 'def small := 0\n')
        self.manifest['module_order'].insert(0, 'a')
        self.save()
        with self.assertRaisesRegex(ValueError, 'Case-colliding'):
            package.source_checks(self.root)

    def test_symlink_source_rejected(self):
        original = self.root / 'project/A.lean'
        target = self.root / 'copy.lean'
        target.write_bytes(original.read_bytes())
        original.unlink()
        original.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'Invalid distribution member'):
            package.source_checks(self.root)

    def test_unlisted_distribution_file_rejected(self):
        self.distribution_manifest()
        (self.root / 'private.txt').write_text('unexpected')
        with self.assertRaisesRegex(ValueError, 'Unexpected distribution files'):
            package.verify(self.root)

    def test_manifest_parent_traversal_rejected(self):
        self.distribution_manifest()
        path = self.root / 'MANIFEST.json'
        data = json.loads(path.read_text())
        data['files']['../outside'] = {'bytes': 0, 'sha256': ''}
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'Invalid distribution member'):
            package.verify(self.root)


class AuditLogTests(unittest.TestCase):
    expected = {'Example.final': ['propext', 'Classical.choice', 'Quot.sound']}
    good = "'Example.final' depends on axioms: [propext, Classical.choice, Quot.sound]\n"

    def test_standard_report_accepted(self):
        self.assertEqual(package.check_audit(self.good, self.expected)['Example.final'],
                         sorted(self.expected['Example.final']))

    def test_failed_log_after_report_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Failed or incomplete'):
            package.check_audit(self.good + 'Proof.lean:10:2: error: failed\n', self.expected)

    def test_unexpected_axiom_rejected(self):
        with self.assertRaises(ValueError):
            package.check_audit(self.good.replace('Quot.sound', 'invented'), self.expected)

    def test_missing_report_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Missing or unexpected'):
            package.check_audit('', self.expected)

    def test_axiom_free_report_accepted(self):
        self.assertEqual(package.check_audit("'Example.free' does not depend on any axioms\n",
                                             {'Example.free': []}), {'Example.free': []})


if __name__ == '__main__':
    unittest.main()
