#!/usr/bin/env python3
# Wide v5 adaptation, 19 November 2026, of the strict source-release replay helper.
# Original strict project attribution and Apache-2.0 terms are retained in NOTICE/LICENSE.
"""Offline isolated Linux replay. Requires separately provisioned pinned dependencies.

No installation, network request, project-cache reuse, or resume is performed.
Outputs are created in a fresh directory outside the source distribution.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
from check_package import ROOT, digest, source_checks, check_audit

FLAGS = ['-t0', '-j1', '-DElab.async=false', '-DmaxHeartbeats=200000',
         '-DsynthInstance.maxHeartbeats=20000']
CPU, WALL, RSS, AS = (300, 301), 600, 6442450944, 9663676416
ACTIVE_RUN = None


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, CPU)
    resource.setrlimit(resource.RLIMIT_AS, (AS, AS))


def command(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def check_source_manifest(expected_hash):
    if digest(ROOT / 'SOURCE_MANIFEST.json') != expected_hash:
        raise ValueError('Source manifest changed during replay')


def check_exports(objects, accepted):
    for module, expected in accepted.items():
        path = objects / (module + '.olean')
        if path.is_symlink() or not path.is_file() or digest(path) != expected:
            raise ValueError('Accepted project export changed: ' + module)


def dependency_hashes(objects, dependencies, accepted):
    if any(module not in accepted for module in dependencies):
        raise ValueError('Project dependency has not been accepted')
    expected = {module: accepted[module] for module in dependencies}
    check_exports(objects, expected)
    return expected


def inspect_environment(lean, mathlib, packages_root=None, source_archives=None):
    version = command([str(lean), '--version'])
    if not re.search(r'Lean \(version 4\.19\.0(?:[, )])', version):
        raise ValueError('Expected Lean4.19.0; received ' + version)
    prefix = Path(command([str(lean), '--print-prefix'])).resolve()
    pins = json.loads((ROOT / 'DEPENDENCY_PINS.json').read_text())
    mathlib = mathlib.resolve()
    names = [p['name'] for p in pins['packages'] if p['name'] != 'mathlib']
    if packages_root is None:
        candidates = [p for p in [mathlib / '.lake/packages', mathlib.parent]
                      if all((p / name).is_dir() for name in names)]
        candidates = list(dict.fromkeys(p.resolve() for p in candidates))
        if len(candidates) != 1:
            raise ValueError('Cannot uniquely locate dependencies; supply --packages-root')
        packages_root = candidates[0]
    paths = []
    for package in pins['packages']:
        p = mathlib if package['name'] == 'mathlib' else packages_root / package['name']
        p = p.resolve()
        if not p.is_dir():
            raise ValueError('Missing dependency source: ' + package['name'])
        if package['name'] == 'mathlib' and not (p / '.lake/build/lib/lean').is_dir():
            raise ValueError('Missing Mathlib cache')
        if source_archives:
            archive = source_archives / package['source_archive_filename']
            if archive.stat().st_size != package['bytes'] or digest(archive) != package['sha256']:
                raise ValueError('Source archive hash mismatch: ' + package['name'])
            with tarfile.open(archive, 'r:gz') as tar:
                for member in tar:
                    if not (member.isfile() or member.issym()):
                        continue
                    relative = Path(member.name).parts[1:]
                    if not relative or '..' in relative or member.name.startswith('/'):
                        raise ValueError('Unexpected source archive member')
                    target = p.joinpath(*relative)
                    if member.issym():
                        if not target.is_symlink() or os.readlink(target) != member.linkname:
                            raise ValueError('Dependency source symlink differs: ' + package['name'])
                    elif (target.is_symlink() or not target.is_file() or
                          digest(target) != hashlib.sha256(tar.extractfile(member).read()).hexdigest()):
                        raise ValueError('Dependency source differs: ' + package['name'])
        else:
            if command(['git', 'rev-parse', 'HEAD'], cwd=p) != package['git_revision']:
                raise ValueError('Incorrect dependency revision: ' + package['name'])
            subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=p, check=True)
        paths.append(p)
    return prefix, paths, {
        'lean_version': version,
        'package_git_pins_checked': not bool(source_archives),
        'pinned_source_archive_contents_checked': bool(source_archives),
        'external_environment_rechecked_after_run': False,
        'package_cache_present': {p.name: (p / '.lake/build/lib/lean').is_dir() for p in paths},
        'notice': 'Pins verify sources. External compiled caches and compiler bytes are observed and bound to this run, not reconstructed from source.'}


def external_roots(prefix, packages):
    return [p / '.lake/build/lib/lean' for p in packages if (p / '.lake/build/lib/lean').is_dir()] + [prefix / 'lib/lean']


def reject_shadowing(roots, modules):
    for root in roots:
        for module in modules:
            if (root / (module + '.olean')).exists():
                raise ValueError('Project module shadows an external export: ' + module)


def snapshot_external(prefix, packages):
    snapshot = {}
    for root, label in [(prefix, 'toolchain'), *[(p, 'packages/' + p.name) for p in packages]]:
        for directory, dirs, names in os.walk(root):
            # Packages are individually inventoried; do not count nested copies twice.
            dirs[:] = sorted(d for d in dirs if d not in ['.git', '__pycache__'] and
                             not (Path(directory).name == '.lake' and d == 'packages'))
            for name in sorted(names + [d for d in dirs if (Path(directory) / d).is_symlink()]):
                path = Path(directory) / name
                key = label + '/' + path.relative_to(root).as_posix()
                item = {}
                if path.is_symlink():
                    item['symlink'] = os.readlink(path)
                if path.is_file():
                    item.update(bytes=path.stat().st_size, sha256=digest(path))
                if not item:
                    raise ValueError('Unexpected external file type: ' + key)
                snapshot[key] = item
    return snapshot


def isolated_environment(objects, sources, prefix, packages):
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = ':'.join(str(p) for p in [objects, *external_roots(prefix, packages)])
    env['LEAN_SRC_PATH'] = ':'.join(str(p) for p in [sources, *packages, prefix / 'src/lean'])
    return env


def compile_one(lean, source, output, source_root, log, env, run_deadline, save):
    start = time.monotonic()
    peak = 0
    stop = None
    last_save = start
    with log.open('wb') as stream:
        child = subprocess.Popen([str(lean), *FLAGS, '--root=' + str(source_root),
                                  '-o', str(output), str(source)], cwd=source_root,
                                 env=env, stdout=stream, stderr=subprocess.STDOUT,
                                 preexec_fn=limits, start_new_session=True)
        try:
            while child.poll() is None:
                try:
                    pages = int(Path(f'/proc/{child.pid}/statm').read_text().split()[1])
                    peak = max(peak, pages * os.sysconf('SC_PAGE_SIZE'))
                except (FileNotFoundError, ProcessLookupError):
                    pass
                if peak > RSS:
                    stop = 'RSS_CAP'
                if time.monotonic() - start > WALL:
                    stop = 'WALL_CAP'
                if time.monotonic() > run_deadline:
                    stop = 'RUN_WALL_CAP'
                if stop:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if time.monotonic() - last_save > 5:
                    save()
                    last_save = time.monotonic()
                time.sleep(0.2)
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            raise
    return {'returncode': child.returncode, 'external_stop': stop,
            'elapsed_seconds': round(time.monotonic() - start, 3),
            'sampled_peak_rss_bytes': peak, 'log_sha256': digest(log)}


def main():
    global ACTIVE_RUN
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, help='Lean executable; default: lean on PATH')
    parser.add_argument('--mathlib', type=Path, required=True, help='Pinned Mathlib source tree with cache')
    parser.add_argument('--packages-root', type=Path, help='Explicit directory of other pinned packages')
    parser.add_argument('--source-archives', type=Path, help='Exact pinned dependency source archives instead of Git checkouts')
    parser.add_argument('--output-parent', type=Path, help='External directory in which a fresh run is created')
    parser.add_argument('--preflight', action='store_true')
    parser.add_argument('--limit', type=int, help='Limited diagnostic replay; never reports FULL_REPLAY_PASS')
    parser.add_argument('--max-run-seconds', type=int, default=21600)
    args = parser.parse_args()
    if sys.platform != 'linux':
        raise ValueError('This bounded helper supports Linux only')
    lean = args.lean or shutil.which('lean')
    if lean is None:
        raise ValueError('Lean is not installed')
    lean = Path(lean).resolve()
    helper_hashes = {name: digest(ROOT / name) for name in ['scripts/rebuild.py', 'scripts/check_package.py']}
    source_manifest_hash = digest(ROOT / 'SOURCE_MANIFEST.json')
    sources, edges = source_checks()
    if args.limit is not None and not 0 < args.limit <= len(sources['modules']):
        raise ValueError('Limit is outside the source inventory')
    if args.max_run_seconds <= 0:
        raise ValueError('Run bound must be positive')
    prefix, packages, environment = inspect_environment(lean, args.mathlib, args.packages_root, args.source_archives)
    roots = external_roots(prefix, packages)
    reject_shadowing(roots, sources['modules'])
    check_source_manifest(source_manifest_hash)
    if args.preflight:
        print(json.dumps({'status': 'PREFLIGHT_PASS', 'fresh_Lean_execution_performed': False,
                          **environment}, indent=2))
        return
    if args.output_parent is None:
        raise ValueError('Supply --output-parent outside the source distribution')
    parent = args.output_parent.resolve()
    if parent.is_relative_to(ROOT) or parent.is_relative_to(ROOT.parent / 'strict'):
        raise ValueError('Build output must be outside strict/ and wide/')
    parent.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='fresh-', dir=parent))
    objects, source_root, logs = run / 'objects', run / 'sources', run / 'logs'
    for p in [objects, source_root, logs]:
        p.mkdir()
    for module, record in sources['modules'].items():
        original = ROOT / record['path']
        if digest(original) != record['sha256']:
            raise ValueError('Source changed while copying: ' + module)
        shutil.copyfile(original, source_root / (module + '.lean'))
    env = isolated_environment(objects, source_root, prefix, packages)
    summary = {'schema_version': 1, 'scope': 'ISOLATED_SOURCE_ONLY', 'status': 'RUNNING',
               'created_utc': now(), 'last_updated_utc': now(), 'source_modules': len(sources['modules']),
               'helper_sha256': digest(Path(__file__)), 'helper_hashes': helper_hashes,
               'python_version': sys.version, 'lean_executable_sha256': digest(lean),
               'source_manifest_sha256': source_manifest_hash, 'environment': environment,
               'flags': FLAGS, 'limits': {'cpu_seconds': CPU, 'wall_seconds_per_module': WALL,
                                        'rss_bytes': RSS, 'virtual_memory_bytes': AS,
                                        'run_wall_seconds': args.max_run_seconds},
               'accepted': [], 'failure': None, 'stage': 'External inventory',
               'limited': args.limit is not None, 'fresh_project_exports_only': True,
               'accepted_dependency_exports_checked': True,
               'final_project_exports_rechecked_after_run': False}
    ACTIVE_RUN = (run, summary)
    def save():
        summary['last_updated_utc'] = now()
        target = run / 'result.json'
        temp = run / 'result.json.tmp'
        temp.write_text(json.dumps(summary, indent=2) + '\n')
        temp.replace(target)
    save()
    print(json.dumps({'event': 'RUN_CREATED', 'run_directory': str(run)}), flush=True)
    external_before = snapshot_external(prefix, packages)
    external_path = run / 'external_environment.json'
    external_path.write_text(json.dumps({'scope': 'Observed compiler/package bytes for this execution, not whole OS provenance.',
                                         'files': external_before}, indent=2) + '\n')
    summary['environment']['external_inventory_sha256'] = digest(external_path)
    summary['environment']['external_file_count'] = len(external_before)
    save()
    deadline = time.monotonic() + args.max_run_seconds
    accepted = {}
    order = sources['module_order'][:args.limit] if args.limit else sources['module_order']
    for module in order:
        summary['stage'] = 'Compile ' + module
        save()
        check_source_manifest(source_manifest_hash)
        record = sources['modules'][module]
        source = source_root / (module + '.lean')
        if digest(source) != record['sha256'] or digest(ROOT / record['path']) != record['sha256']:
            raise ValueError('Source changed before replay: ' + module)
        imported = dependency_hashes(objects, edges[module], accepted)
        output = objects / (module + '.olean')
        log = logs / (module + '.log')
        receipt = compile_one(lean, source, output, source_root, log, env, deadline, save)
        receipt.update(module=module, source_sha256=digest(source), dependency_export_sha256=imported)
        passed = receipt['returncode'] == 0 and receipt['external_stop'] is None and output.is_file() and not output.is_symlink()
        passed = passed and receipt['source_sha256'] == record['sha256']
        check_source_manifest(source_manifest_hash)
        check_exports(objects, imported)
        if passed and module in sources['audit_results']:
            check_audit(log.read_text(), sources['audit_results'][module])
        receipt['accepted'] = passed
        if passed:
            receipt['export_sha256'] = digest(output)
        (logs / (module + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({'module': module, 'accepted': passed,
                          'elapsed_seconds': receipt['elapsed_seconds']}), flush=True)
        if not passed:
            summary['failure'] = module
            raise ValueError('Replay failed for ' + module)
        accepted[module] = receipt['export_sha256']
        summary['accepted'].append(module)
        save()
    for module in order:
        if digest(source_root / (module + '.lean')) != sources['modules'][module]['sha256']:
            raise ValueError('Copied source changed during replay: ' + module)
    check_exports(objects, accepted)
    if args.limit is not None:
        summary['status'] = 'PARTIAL_REPLAY_PASS'
        summary['stage'] = 'Limited diagnostic complete; full replay not performed'
        save()
        print(str(run / 'result.json'), flush=True)
        return
    leaf = source_root / 'WideReleaseAudit.lean'
    leaf.write_text('''import V5WideFinal140
set_option Elab.async false
#check @StrictEUnit.v5_wide_unit_classification140
#print axioms StrictEUnit.v5ActualReciprocalExponential140
#print axioms StrictEUnit.v5_wide_reciprocal_at_one140
#print axioms StrictEUnit.v5_wide_unit_classification140
''')
    summary['stage'] = 'Terminal named axiom audit'
    save()
    check_exports(objects, accepted)
    audit = compile_one(lean, leaf, objects / 'WideReleaseAudit.olean', source_root,
                        logs / 'WideReleaseAudit.log', env, deadline, save)
    if audit['returncode'] != 0 or audit['external_stop'] is not None:
        raise ValueError('Terminal audit compilation failed')
    expected = {name: ['propext', 'Classical.choice', 'Quot.sound'] for name in [
        'StrictEUnit.v5ActualReciprocalExponential140', 'StrictEUnit.v5_wide_reciprocal_at_one140',
        'StrictEUnit.v5_wide_unit_classification140']}
    summary['axiom_reports'] = check_audit((logs / 'WideReleaseAudit.log').read_text(), expected)
    summary['stage'] = 'Final source/export/environment checks'
    save()
    check_source_manifest(source_manifest_hash)
    source_checks()
    check_exports(objects, accepted)
    summary['final_project_exports_rechecked_after_run'] = True
    inspect_environment(lean, args.mathlib, args.packages_root, args.source_archives)
    reject_shadowing(roots, sources['modules'])
    if snapshot_external(prefix, packages) != external_before:
        raise ValueError('Compiler/package bytes changed during replay')
    check_source_manifest(source_manifest_hash)
    check_exports(objects, accepted)
    summary['environment']['external_environment_rechecked_after_run'] = True
    for name, expected_hash in helper_hashes.items():
        if digest(ROOT / name) != expected_hash:
            raise ValueError('Replay helper changed during execution: ' + name)
    summary['status'] = 'FULL_REPLAY_PASS'
    summary['stage'] = 'Complete'
    save()
    print(str(run / 'result.json'), flush=True)


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, lambda signum, frame: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        main()
    except BaseException as error:
        if ACTIVE_RUN is not None:
            run, summary = ACTIVE_RUN
            summary['status'] = 'INTERRUPTED' if isinstance(error, KeyboardInterrupt) else 'FAILED'
            summary['failure'] = str(error) or type(error).__name__
            summary['last_updated_utc'] = now()
            (run / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
        if isinstance(error, SystemExit):
            raise
        print('REPLAY STOPPED: ' + str(error), file=sys.stderr)
        sys.exit(130 if isinstance(error, KeyboardInterrupt) else 1)
