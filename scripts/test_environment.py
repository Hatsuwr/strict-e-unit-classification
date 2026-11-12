"""Synthetic tests for dependency pin validation; no Lean execution is performed."""
from pathlib import Path
import io
import json
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import rebuild
from check_package import digest


class EnvironmentChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.package = self.root / 'project/.lake/packages/example'
        self.package.mkdir(parents=True)
        self.prefix = self.root / 'toolchain'
        self.prefix.mkdir()
        self.archives = self.root / 'archives'
        self.archives.mkdir()
        self.source = self.package / 'Example.lean'
        self.source.write_bytes(b'theorem sample : True := by trivial\n')
        self.archive = self.archives / 'example.tar.gz'
        with tarfile.open(self.archive, 'w:gz') as tar:
            data = self.source.read_bytes()
            info = tarfile.TarInfo('example/Example.lean')
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
        self.pins = {'packages': [{
            'name': 'example', 'git_revision': 'a' * 40,
            'source_archive_filename': self.archive.name,
            'bytes': self.archive.stat().st_size, 'sha256': digest(self.archive)}]}
        (self.root / 'DEPENDENCY_PINS.json').write_text(json.dumps(self.pins))
        self.version = 'Lean (version 4.19.0, x86_64-unknown-linux-gnu, Release)'

    def tearDown(self):
        self.temp.cleanup()

    def command(self, args, cwd=None):
        if args[-1] == '--version':
            return self.version
        if args[-1] == '--print-prefix':
            return str(self.prefix)
        if args == ['git', 'rev-parse', 'HEAD']:
            return 'a' * 40
        raise AssertionError('Unexpected command: ' + repr(args))

    def inspect(self, archives=True):
        with patch.object(rebuild, 'ROOT', self.root), \
             patch.object(rebuild, 'command', side_effect=self.command):
            return rebuild.inspect_environment(self.prefix / 'bin/lean',
                                               self.archives if archives else None)

    def test_source_archive_route_without_historical_files(self):
        prefix, paths, result = self.inspect()
        self.assertEqual(prefix, self.prefix)
        self.assertEqual(paths, [self.package])
        self.assertTrue(result['pinned_source_archive_contents_checked'])
        self.assertFalse(result['package_git_pins_checked'])
        self.assertFalse(result['external_environment_rechecked_after_run'])

    def test_changed_source_rejected(self):
        self.source.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Installed source differs'):
            self.inspect()

    def test_changed_archive_rejected(self):
        self.archive.write_bytes(self.archive.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'Source archive hash mismatch'):
            self.inspect()

    def test_wrong_compiler_version_rejected(self):
        self.version = 'Lean (version 4.20.0)'
        with self.assertRaisesRegex(ValueError, 'Expected Lean 4.19.0'):
            self.inspect()

    def test_missing_package_rejected(self):
        self.source.unlink()
        self.package.rmdir()
        with self.assertRaisesRegex(ValueError, 'Missing package'):
            self.inspect()

    def test_git_route_checks_pins_and_cleanliness(self):
        with patch.object(rebuild.subprocess, 'run') as run:
            _, _, result = self.inspect(archives=False)
        self.assertTrue(result['package_git_pins_checked'])
        self.assertFalse(result['pinned_source_archive_contents_checked'])
        run.assert_called_once_with(['git', 'diff', '--quiet', 'HEAD', '--'],
                                    cwd=self.package, check=True)


if __name__ == '__main__':
    unittest.main()
