#!/usr/bin/env python3
# Modified for the source-focused edition, 12 November 2026.
"""Offline regression tests for the narrow package source/log checks."""
from pathlib import Path
import json
import shutil
import tempfile
import unittest
from check_package import ROOT, digest, source_checks, check_audit, verify

class Checks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temp.name)
        (cls.root / 'project').mkdir()
        shutil.copyfile(ROOT / 'SOURCE_MANIFEST.json', cls.root / 'SOURCE_MANIFEST.json')
        for path in (ROOT / 'project').glob('*.lean'):
            shutil.copyfile(path, cls.root / 'project' / path.name)

    @classmethod
    def tearDownClass(cls): cls.temp.cleanup()

    def test_unchanged_sources(self):
        manifest, _ = source_checks(self.root)
        self.assertEqual(len(manifest['modules']), 986)

    def test_source_tamper_is_rejected(self):
        path = self.root / 'project/StrictEValueUnitClassification.lean'
        original = path.read_bytes()
        try:
            path.write_bytes(original + b'\n-- changed\n')
            with self.assertRaisesRegex(ValueError, 'Source mismatch'):
                source_checks(self.root)
        finally: path.write_bytes(original)

    def test_disallowed_token_is_rejected_even_with_updated_hash(self):
        path = self.root / 'project/StrictEValueUnitClassification.lean'
        manifest_path = self.root / 'SOURCE_MANIFEST.json'
        original, original_manifest = path.read_bytes(), manifest_path.read_bytes()
        try:
            path.write_bytes(original + b'\nexample : True := by sorry\n')
            manifest = json.loads(original_manifest)
            manifest['modules'][path.stem] = {'bytes': path.stat().st_size, 'sha256': digest(path)}
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'Disallowed source token'):
                source_checks(self.root)
        finally:
            path.write_bytes(original); manifest_path.write_bytes(original_manifest)

    def test_expected_audit_schema(self):
        manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
        self.assertEqual(len(manifest['audit_results']), 3)
        self.assertEqual(set(manifest['allowed_axioms']), {'propext', 'Classical.choice', 'Quot.sound'})
        for declarations in manifest['audit_results'].values():
            self.assertTrue(declarations)
            for axioms in declarations.values():
                self.assertEqual(set(axioms), set(manifest['allowed_axioms']))

    def test_identical_symlink_source_is_rejected(self):
        path = self.root / 'project/StrictEValueUnitClassification.lean'
        original = path.read_bytes()
        with tempfile.TemporaryDirectory() as temp:
            target = Path(temp) / path.name
            target.write_bytes(original)
            try:
                path.unlink()
                path.symlink_to(target)
                with self.assertRaisesRegex(ValueError, 'Invalid project source'):
                    source_checks(self.root)
            finally:
                path.unlink()
                path.write_bytes(original)

    def test_missing_and_extra_axioms_are_rejected(self):
        expected = {'Example.endpoint': ['propext', 'Classical.choice', 'Quot.sound']}
        with self.assertRaises(ValueError): check_audit('', expected)
        bad = "'Example.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]"
        with self.assertRaises(ValueError): check_audit(bad, expected)
        duplicate = bad + "\n'Example.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]"
        with self.assertRaises(ValueError): check_audit(duplicate, expected)


class DistributionPaths(unittest.TestCase):
    def test_git_checkout_metadata_is_permitted(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'project').mkdir()
            (root / '.git').mkdir()
            (root / '.git/HEAD').write_text('ref: refs/heads/main\n')
            source_manifest = root / 'SOURCE_MANIFEST.json'
            source_manifest.write_text(json.dumps({'modules': {}, 'module_order': [], 'audit_results': {}}))
            (root / 'MANIFEST.json').write_text(json.dumps({'files': {'SOURCE_MANIFEST.json': {
                'bytes': source_manifest.stat().st_size, 'sha256': digest(source_manifest)}}}))
            self.assertEqual(verify(root)['status'], 'PACKAGE_INTEGRITY_PASS')

    def test_parent_path_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'MANIFEST.json').write_text(json.dumps({'files': {'../outside': {}}}))
            with self.assertRaisesRegex(ValueError, 'Invalid distribution member'):
                verify(root)

    def test_unlisted_broken_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'MANIFEST.json').write_text(json.dumps({'files': {}}))
            (root / 'unlisted').symlink_to(root / 'absent')
            with self.assertRaisesRegex(ValueError, 'Unexpected distribution files'):
                verify(root)

if __name__ == '__main__': unittest.main()
