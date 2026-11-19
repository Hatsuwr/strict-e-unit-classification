#!/usr/bin/env python3
# Modified for the broad v5 source package, 19 November 2026.
# Adapted from the strict source-focused release's offline runner regressions.
# Original and modified project material: Apache-2.0; see LICENSE and NOTICE.
"""Synthetic integrity regressions. These tests do not execute Lean."""
from pathlib import Path
import contextlib
import io
import json
import os
import hashlib
import tempfile
import unittest
from unittest.mock import patch

import rebuild
from check_package import check_audit


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExportIntegrityTests(unittest.TestCase):
    """Accepted object bytes, rather than their mere presence, authorize imports."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.objects = self.root / 'objects'
        self.objects.mkdir()
        self.first = self.objects / 'A.olean'
        self.second = self.objects / 'B.olean'
        self.first.write_bytes(b'accepted A export')
        self.second.write_bytes(b'accepted B export')
        self.accepted = {'A': sha256(self.first), 'B': sha256(self.second)}

    def tearDown(self):
        self.temp.cleanup()

    def test_dependency_receipt_contains_only_requested_accepted_exports(self):
        expected = {'A': self.accepted['A']}
        self.assertEqual(rebuild.dependency_hashes(self.objects, ['A'], self.accepted), expected)

    def test_unaccepted_dependency_is_rejected(self):
        with self.assertRaises(ValueError):
            rebuild.dependency_hashes(self.objects, ['C'], self.accepted)

    def test_changed_dependency_is_rejected_before_import(self):
        self.first.write_bytes(b'changed before the dependent compiler starts')
        with self.assertRaises(ValueError):
            rebuild.dependency_hashes(self.objects, ['A'], self.accepted)

    def test_dependency_changed_during_compilation_is_rejected_afterward(self):
        imported = rebuild.dependency_hashes(self.objects, ['A'], self.accepted)
        self.first.write_bytes(b'changed while compiling dependent B')
        with self.assertRaises(ValueError):
            rebuild.check_exports(self.objects, imported)

    def test_terminal_export_tampering_is_rejected_by_final_recheck(self):
        rebuild.check_exports(self.objects, self.accepted)
        self.second.write_bytes(b'changed after the final compiler invocation')
        with self.assertRaises(ValueError):
            rebuild.check_exports(self.objects, self.accepted)

    def test_missing_export_is_not_an_accepted_dependency(self):
        self.first.unlink()
        with self.assertRaises((ValueError, OSError)):
            rebuild.check_exports(self.objects, self.accepted)

    def test_symlink_export_is_rejected_even_when_target_bytes_match(self):
        outside = self.root / 'external-export'
        outside.write_bytes(self.first.read_bytes())
        self.first.unlink()
        self.first.symlink_to(outside)
        with self.assertRaises(ValueError):
            rebuild.check_exports(self.objects, self.accepted)


class ManifestIntegrityTests(unittest.TestCase):
    def test_source_manifest_drift_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = root / 'SOURCE_MANIFEST.json'
            manifest.write_bytes(b'original manifest')
            expected = sha256(manifest)
            with patch.object(rebuild, 'ROOT', root):
                rebuild.check_source_manifest(expected)
                manifest.write_bytes(b'changed manifest')
                with self.assertRaises(ValueError):
                    rebuild.check_source_manifest(expected)


class NamedAxiomAuditTests(unittest.TestCase):
    name = 'StrictEUnit.v5_wide_unit_classification140'
    axioms = ['propext', 'Classical.choice', 'Quot.sound']

    def report(self, name=None, axioms=None):
        return "'{}' depends on axioms: [{}]\n".format(
            self.name if name is None else name,
            ', '.join(self.axioms if axioms is None else axioms))

    def test_complete_named_standard_axiom_report_is_accepted(self):
        parsed = check_audit(self.report(), {self.name: self.axioms})
        self.assertEqual(parsed[self.name], sorted(self.axioms))

    def test_empty_audit_log_does_not_pass_vacuously(self):
        with self.assertRaises(ValueError):
            check_audit('', {self.name: self.axioms})

    def test_unrelated_report_does_not_replace_required_endpoint(self):
        with self.assertRaises(ValueError):
            check_audit(self.report('Unrelated.theorem'), {self.name: self.axioms})

    def test_unexpected_axiom_in_an_additional_report_is_rejected(self):
        log = self.report() + self.report('Unrelated.theorem', ['sorryAx'])
        with self.assertRaises(ValueError):
            check_audit(log, {self.name: self.axioms})

    def test_conflicting_duplicate_reports_are_rejected(self):
        log = self.report() + self.report(axioms=['propext'])
        with self.assertRaises(ValueError):
            check_audit(log, {self.name: self.axioms})


class ReplayBudgetTests(unittest.TestCase):
    def test_kernel_and_serial_elaboration_flags_are_present(self):
        self.assertIn('-t0', rebuild.FLAGS)
        self.assertIn('-j1', rebuild.FLAGS)
        self.assertIn('-DElab.async=false', rebuild.FLAGS)

    def test_resource_budgets_are_finite_and_consistent(self):
        soft_cpu, hard_cpu = rebuild.CPU
        self.assertGreater(soft_cpu, 0)
        self.assertGreater(hard_cpu, soft_cpu)
        self.assertGreaterEqual(rebuild.WALL, hard_cpu)
        self.assertGreater(rebuild.RSS, 0)
        self.assertGreater(rebuild.AS, rebuild.RSS)


class EnvironmentIsolationTests(unittest.TestCase):
    def test_inherited_lean_paths_are_replaced_and_threads_are_serial(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            objects, sources = base / 'objects', base / 'sources'
            prefix, package = base / 'toolchain', base / 'mathlib'
            (package / '.lake/build/lib/lean').mkdir(parents=True)
            inherited = {'LEAN_PATH': 'UNTRUSTED_OLD_PROJECT_EXPORTS',
                         'LEAN_SRC_PATH': 'UNTRUSTED_OLD_PROJECT_SOURCES',
                         'LEAN_NUM_THREADS': '64'}
            with patch.dict(os.environ, inherited):
                env = rebuild.isolated_environment(objects, sources, prefix, [package])
                self.assertEqual(os.environ['LEAN_PATH'], inherited['LEAN_PATH'])
            self.assertEqual(env['LEAN_NUM_THREADS'], '1')
            self.assertEqual(env['LEAN_PATH'].split(':'), [str(objects),
                str(package / '.lake/build/lib/lean'), str(prefix / 'lib/lean')])
            self.assertEqual(env['LEAN_SRC_PATH'].split(':'),
                [str(sources), str(package), str(prefix / 'src/lean')])
            self.assertNotIn('UNTRUSTED', env['LEAN_PATH'])
            self.assertNotIn('UNTRUSTED', env['LEAN_SRC_PATH'])

    def test_external_project_export_shadowing_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            rebuild.reject_shadowing([root], ['A'])
            (root / 'A.olean').write_bytes(b'untrusted external A')
            with self.assertRaises(ValueError):
                rebuild.reject_shadowing([root], ['A'])


class FakeCompilerReplayTests(unittest.TestCase):
    """Exercise runner guards with synthetic exports; never invoke a compiler."""

    def run_fixture(self, mode='complete'):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            root, output_parent = base / 'package', base / 'runs'
            (root / 'project').mkdir(parents=True)
            (root / 'scripts').mkdir()
            (root / 'scripts/rebuild.py').write_bytes(b'fixture replay helper')
            (root / 'scripts/check_package.py').write_bytes(b'fixture package checker')
            prefix, package = base / 'toolchain', base / 'mathlib'
            (prefix / 'bin').mkdir(parents=True)
            (prefix / 'lib/lean').mkdir(parents=True)
            (package / '.lake/build/lib/lean').mkdir(parents=True)
            lean = prefix / 'bin/lean'
            lean.write_bytes(b'FAKE COMPILER: must never be executed')
            manifest = root / 'SOURCE_MANIFEST.json'
            manifest.write_bytes(b'fixed fixture manifest')
            modules = ['A', 'B', 'C']
            records = {}
            for module in modules:
                path = root / 'project' / (module + '.lean')
                path.write_text('-- synthetic source ' + module + '\n')
                records[module] = {'path': 'project/' + module + '.lean',
                                   'sha256': sha256(path)}
            sources = {'module_order': modules, 'modules': records, 'audit_results': {}}
            edges = {'A': [], 'B': ['A'], 'C': []}
            invoked = []
            real_dependencies = rebuild.dependency_hashes

            def source_checks():
                for record in records.values():
                    if sha256(root / record['path']) != record['sha256']:
                        raise ValueError('Fixture original source changed')
                return sources, edges

            def dependencies(objects, imported, accepted):
                if mode == 'before_import' and imported:
                    (objects / 'A.olean').write_bytes(b'tampered before import')
                return real_dependencies(objects, imported, accepted)

            def fake_compile(compiler, source, output, source_root, log, env, deadline, save):
                module = source.stem
                invoked.append(module)
                output.write_bytes(('synthetic export ' + module).encode())
                log.write_text('')
                if module == 'WideReleaseAudit':
                    if mode != 'missing_terminal_report':
                        names = ['StrictEUnit.v5ActualReciprocalExponential140',
                                 'StrictEUnit.v5_wide_reciprocal_at_one140',
                                 'StrictEUnit.v5_wide_unit_classification140']
                        log.write_text(''.join("'" + name + "' depends on axioms: "
                            "[propext, Classical.choice, Quot.sound]\n" for name in names))
                    if mode == 'terminal_export':
                        (output.parent / 'B.olean').write_bytes(b'tampered terminal export')
                if module == 'B' and mode == 'during_import':
                    (output.parent / 'A.olean').write_bytes(b'tampered while compiling B')
                if module == 'A' and mode == 'manifest':
                    manifest.write_bytes(b'changed manifest')
                if module == 'A' and mode == 'copied_source_during':
                    source.write_bytes(b'changed copied source during compilation')
                if module == 'C' and mode == 'copied_source_after':
                    (source_root / 'A.lean').write_bytes(b'changed copied source after acceptance')
                if module == 'C' and mode == 'original_source_after':
                    (root / 'project/A.lean').write_bytes(b'changed packaged source after acceptance')
                return {'returncode': 0, 'external_stop': None, 'elapsed_seconds': 0.001,
                        'sampled_peak_rss_bytes': 1, 'log_sha256': sha256(log)}

            argv = ['rebuild.py', '--lean', str(lean), '--mathlib', str(package),
                    '--output-parent', str(output_parent)]
            if mode == 'partial':
                argv.extend(['--limit', '1'])
            successful = mode in {'complete', 'partial'}
            try:
                with patch.object(rebuild, 'ROOT', root), \
                     patch.object(rebuild, 'source_checks', side_effect=source_checks), \
                     patch.object(rebuild, 'inspect_environment', return_value=(prefix, [package], {})), \
                     patch.object(rebuild, 'snapshot_external', return_value={}), \
                     patch.object(rebuild, 'dependency_hashes', side_effect=dependencies), \
                     patch.object(rebuild, 'compile_one', side_effect=fake_compile), \
                     patch.object(rebuild.sys, 'argv', argv), \
                     contextlib.redirect_stdout(io.StringIO()):
                    if successful:
                        rebuild.main()
                    else:
                        with self.assertRaises(ValueError):
                            rebuild.main()
                result_path, = output_parent.glob('fresh-*/result.json')
                result = json.loads(result_path.read_text())
                if mode == 'complete':
                    self.assertEqual(result['status'], 'FULL_REPLAY_PASS')
                    self.assertEqual(result['accepted'], modules)
                    self.assertTrue(result['final_project_exports_rechecked_after_run'])
                    self.assertTrue(result['environment']['external_environment_rechecked_after_run'])
                    self.assertEqual(invoked, modules + ['WideReleaseAudit'])
                elif mode == 'partial':
                    self.assertEqual(result['status'], 'PARTIAL_REPLAY_PASS')
                    self.assertEqual(result['accepted'], ['A'])
                    self.assertNotIn('WideReleaseAudit', invoked)
                else:
                    self.assertNotEqual(result['status'], 'FULL_REPLAY_PASS')
                    if mode == 'before_import':
                        self.assertEqual(invoked, ['A'])
            finally:
                rebuild.ACTIVE_RUN = None

    def test_complete_synthetic_run_checks_terminal_audit(self): self.run_fixture()
    def test_partial_run_is_never_full_success(self): self.run_fixture('partial')
    def test_dependency_tampering_before_import_stops_runner(self): self.run_fixture('before_import')
    def test_dependency_tampering_during_compile_stops_runner(self): self.run_fixture('during_import')
    def test_terminal_export_tampering_stops_runner(self): self.run_fixture('terminal_export')
    def test_source_manifest_drift_stops_runner(self): self.run_fixture('manifest')
    def test_copied_source_mutation_during_compile_stops_runner(self): self.run_fixture('copied_source_during')
    def test_copied_source_mutation_after_acceptance_stops_runner(self): self.run_fixture('copied_source_after')
    def test_packaged_source_mutation_after_acceptance_stops_runner(self): self.run_fixture('original_source_after')
    def test_missing_terminal_axiom_report_stops_runner(self): self.run_fixture('missing_terminal_report')


if __name__ == '__main__':
    unittest.main()
