#!/usr/bin/env python3
# Wide v5 focused checker, 19 November 2026. Apache-2.0; see LICENSE/NOTICE.
"""Recheck the final source/audit against explicit existing project objects.
This is a FOCUSED check, never an isolated source-only rebuild of the closure.
"""
from pathlib import Path
import argparse
import json
import tempfile
import time
from check_package import ROOT, digest, source_checks, check_audit
from rebuild import FLAGS, CPU, WALL, RSS, AS, inspect_environment, isolated_environment, external_roots, reject_shadowing, compile_one, check_exports, now


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--mathlib', type=Path, required=True)
    p.add_argument('--packages-root', type=Path)
    p.add_argument('--source-archives', type=Path)
    p.add_argument('--project-objects', type=Path, required=True)
    p.add_argument('--output-parent', type=Path, required=True)
    a = p.parse_args()
    manifest, edges = source_checks()
    manifest_hash = digest(ROOT / 'SOURCE_MANIFEST.json')
    prefix, packages, environment = inspect_environment(a.lean.resolve(), a.mathlib, a.packages_root, a.source_archives)
    reject_shadowing(external_roots(prefix, packages), manifest['modules'])
    cache = a.project_objects.resolve()
    expected_names = {m + '.olean' for m in manifest['modules']}
    actual_names = {x.name for x in cache.iterdir() if x.is_file() or x.is_symlink()}
    if actual_names != expected_names:
        raise ValueError('Focused input directory must contain exactly the canonical project object names')
    accepted = {m: digest(cache / (m + '.olean')) for m in manifest['modules']}
    check_exports(cache, accepted)
    parent = a.output_parent.resolve()
    if parent.is_relative_to(ROOT) or parent.is_relative_to(ROOT.parent / 'strict'):
        raise ValueError('Focused outputs must be outside strict/ and wide/')
    parent.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='focused-', dir=parent))
    sources, objects, logs = run / 'sources', run / 'objects', run / 'logs'
    for d in [sources, objects, logs]:
        d.mkdir()
    env = isolated_environment(objects, sources, prefix, packages)
    env['LEAN_PATH'] = str(objects) + ':' + str(cache) + ':' + ':'.join(str(x) for x in external_roots(prefix, packages))
    result = {'status': 'RUNNING', 'scope': 'FOCUSED_EXISTING_PROJECT_OBJECTS',
              'source_modules': len(manifest['modules']), 'accepted': [], 'created_utc': now(),
              'last_updated_utc': now(), 'environment': environment,
              'input_project_objects_sha256': accepted, 'failure': None,
              'fresh_transitive_source_rebuild_performed': False, 'flags': FLAGS,
              'limits': {'cpu_seconds': CPU, 'wall_seconds_per_module': WALL, 'rss_bytes': RSS, 'virtual_memory_bytes': AS},
              'helper_sha256': digest(Path(__file__)), 'source_manifest_sha256': manifest_hash}
    def save():
        result['last_updated_utc'] = now()
        (run / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    try:
        save()
        print(json.dumps({'event': 'FOCUSED_RUN_CREATED', 'run_directory': str(run)}), flush=True)
        source = sources / 'V5WideFinal140.lean'
        source.write_bytes((ROOT / manifest['modules']['V5WideFinal140']['path']).read_bytes())
        result['stage'] = 'Compile final source with existing dependency exports'
        receipt = compile_one(a.lean.resolve(), source, objects / 'V5WideFinal140.olean', sources,
                              logs / 'V5WideFinal140.log', env, time.monotonic() + 1200, save)
        if receipt['returncode'] != 0 or receipt['external_stop'] is not None:
            raise ValueError('Focused final source failed')
        if digest(source) != manifest['modules']['V5WideFinal140']['sha256']:
            raise ValueError('Focused source changed during execution')
        check_audit((logs / 'V5WideFinal140.log').read_text(), manifest['audit_results']['V5WideFinal140'])
        final_export = {'V5WideFinal140': digest(objects / 'V5WideFinal140.olean')}
        result['accepted'] = ['V5WideFinal140']
        result['fresh_project_modules_compiled'] = 1
        result['final_source_receipt'] = receipt
        result['final_export_sha256'] = final_export['V5WideFinal140']
        leaf = sources / 'WideFocusedAudit.lean'
        leaf.write_text('''import V5WideFinal140
#print axioms StrictEUnit.v5ActualReciprocalExponential140
#print axioms StrictEUnit.v5_wide_reciprocal_at_one140
#print axioms StrictEUnit.v5_wide_unit_classification140
''')
        result['stage'] = 'Named endpoint audit'
        audit = compile_one(a.lean.resolve(), leaf, objects / 'WideFocusedAudit.olean', sources,
                            logs / 'WideFocusedAudit.log', env, time.monotonic() + 1200, save)
        if audit['returncode'] != 0 or audit['external_stop'] is not None:
            raise ValueError('Focused terminal audit failed')
        result['audit_receipt'] = audit
        result['audit_source_sha256'] = digest(leaf)
        names = ['StrictEUnit.v5ActualReciprocalExponential140', 'StrictEUnit.v5_wide_reciprocal_at_one140',
                 'StrictEUnit.v5_wide_unit_classification140']
        result['axiom_reports'] = check_audit((logs / 'WideFocusedAudit.log').read_text(),
                                             {n: ['propext', 'Classical.choice', 'Quot.sound'] for n in names})
        check_exports(cache, accepted)
        check_exports(objects, final_export)
        source_checks()
        if digest(ROOT / 'SOURCE_MANIFEST.json') != manifest_hash:
            raise ValueError('Source manifest changed during focused check')
        inspect_environment(a.lean.resolve(), a.mathlib, a.packages_root, a.source_archives)
        result['status'] = 'FOCUSED_CHECK_PASS'
        result['stage'] = 'Final source and endpoint audit complete; transitive source rebuild not performed'
        save()
        print(str(run / 'result.json'), flush=True)
    except BaseException as error:
        result['status'] = 'FAILED'
        result['failure'] = str(error) or type(error).__name__
        save()
        raise


if __name__ == '__main__':
    main()
