#!/usr/bin/env python3
# Wide v5 status projection, 19 November 2026. Apache-2.0; see LICENSE/NOTICE.
"""Write a portable status snapshot without copying local logs, paths, or objects.
Run freeze_manifest.py and check_release.py after updating this metadata.
A RUNNING/FAILED/PARTIAL replay is never projected as a full verification pass.
"""
import argparse
import json
from pathlib import Path
from check_package import ROOT, digest, source_checks
from rebuild import now

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--static', type=Path, required=True)
p.add_argument('--focused-run', type=Path, required=True)
p.add_argument('--full-run', type=Path, required=True)
a = p.parse_args()
manifest, _ = source_checks()
static = json.loads(a.static.read_text())
focused = json.loads((a.focused_run / 'result.json').read_text())
full = json.loads((a.full_run / 'result.json').read_text())
if static['status'] != 'STATIC_RELEASE_CHECK_PASS':
    raise ValueError('Static checks did not pass')
if focused['scope'] != 'FOCUSED_EXISTING_PROJECT_OBJECTS' or full['scope'] != 'ISOLATED_SOURCE_ONLY':
    raise ValueError('Verification scope mismatch')
expected = digest(ROOT / 'SOURCE_MANIFEST.json')
for receipt in [focused, full]:
    if receipt.get('source_manifest_sha256') != expected:
        raise ValueError('Verification receipt belongs to another source closure')
failure = full.get('failure')
if failure is not None:
    matches = [m for m in manifest['modules'] if failure == m or failure == 'Replay failed for ' + m]
    failure = matches[0] if matches else 'EXTERNAL_ENVIRONMENT_OR_RUN_FAILURE_SEE_LOCAL_RECEIPT'
full_pass = (full['status'] == 'FULL_REPLAY_PASS' and len(full['accepted']) == len(manifest['modules'])
             and full.get('final_project_exports_rechecked_after_run') is True
             and full['environment'].get('external_environment_rechecked_after_run') is True
             and bool(full.get('axiom_reports')))
if full['status'] == 'FULL_REPLAY_PASS' and not full_pass:
    raise ValueError('Incomplete full replay receipt')
status = {
    'schema_version': 1, 'observed_utc': now(),
    'source_modules': len(manifest['modules']), 'source_bytes': manifest['source_bytes'],
    'source_manifest_sha256': expected,
    'static': {'status': static['status'], 'offline_regressions': static['offline_regressions'],
               'fresh_Lean_execution_performed': False},
    'focused': {'status': focused['status'], 'scope': focused['scope'],
                'fresh_project_modules_compiled': focused.get('fresh_project_modules_compiled', 1),
                'fresh_transitive_source_rebuild_performed': False,
                'axiom_reports': focused.get('axiom_reports', {})},
    'isolated_full_replay': {'status': full['status'], 'accepted_modules': len(full['accepted']),
                             'stage': full['stage'], 'last_updated_utc': full['last_updated_utc'],
                             'flags': full['flags'], 'limits': full['limits'],
                             'axiom_reports': full.get('axiom_reports', {}),
                             'failure_module_or_category': failure},
    'release_verification': 'FULL_ISOLATED_REPLAY_PASS' if full_pass else 'FULL_ISOLATED_REPLAY_NOT_COMPLETE',
    'notice': 'This is a frozen status snapshot. Static and focused passes do not imply a full source-only replay. Live records remain outside the source distribution.'}
(ROOT / 'VERIFICATION_STATUS.json').write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps({'status': status['release_verification'], 'accepted_modules': len(full['accepted'])}))
