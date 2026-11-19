#!/usr/bin/env python3
# Added for the public source-focused edition, 12 November 2026.
"""Offline release-metadata consistency tests; these do not run Lean."""
import json
import unittest
from check_package import ROOT, digest


class ReleaseMetadata(unittest.TestCase):
    def test_version_status_and_source_identity(self):
        release = json.loads((ROOT / 'RELEASE.json').read_text())
        package = json.loads((ROOT / 'MANIFEST.json').read_text())
        sources = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
        self.assertEqual(release['version'], package['release_version'])
        self.assertEqual(release['status'], 'PUBLIC_SOURCE_RELEASE')
        self.assertEqual(release['status'], package['status'])
        self.assertEqual(release['source_manifest_sha256'], digest(ROOT / 'SOURCE_MANIFEST.json'))
        self.assertEqual(package['source_manifest_sha256'], release['source_manifest_sha256'])
        self.assertEqual(release['proof_module_count'], len(sources['modules']))
        self.assertEqual(release['proof_source_bytes'], sum(m['bytes'] for m in sources['modules'].values()))
        self.assertIn('Version ' + release['version'], (ROOT / 'README.md').read_text())
        self.assertIn('Version ' + release['version'], (ROOT / 'CITATION.md').read_text())
        self.assertIn('Version ' + release['version'], (ROOT / 'references.bib').read_text())

    def test_development_credit_is_consistent(self):
        release = json.loads((ROOT / 'RELEASE.json').read_text())
        credit = release['development_credit']
        self.assertEqual(credit, 'Developed by dot, an AI assistant powered by OpenAI')
        for name in ('README.md', 'CITATION.md', 'NOTICE', 'references.bib'):
            with self.subTest(name=name):
                self.assertIn(credit, (ROOT / name).read_text())

    def test_recorded_checks_keep_verification_boundary(self):
        release = json.loads((ROOT / 'RELEASE.json').read_text())
        result = json.loads((ROOT / 'CHECK_RESULTS.json').read_text())
        self.assertIs(release['fresh_Lean_execution_performed'], False)
        self.assertIs(release['historical_execution_records_bundled'], False)
        self.assertIs(result['fresh_Lean_execution_performed'], False)
        self.assertIs(result['package']['fresh_Lean_replay_performed'], False)
        self.assertIs(result['contracts']['Lean_elaboration_performed'], False)
        self.assertNotIn('public_release_authorized', release)
        self.assertNotIn('public_release_authorized', result)


if __name__ == '__main__':
    unittest.main()
