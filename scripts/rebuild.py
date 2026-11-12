#!/usr/bin/env python3
# Modified for the source-focused edition, 12 November 2026.
"""Fresh, serial Linux replay. Installs nothing; never reuses project exports.

Read VALIDATION.md for testing status and REPRODUCING.md before use.
This helper creates new execution records; no earlier execution records are bundled.
"""
from pathlib import Path
import argparse
import datetime
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import tarfile
import hashlib
import time
from check_package import ROOT, digest, source_checks, check_audit

FLAGS = ['-t0', '-j1', '-DElab.async=false', '-DmaxHeartbeats=200000',
         '-DsynthInstance.maxHeartbeats=20000']
CPU, WALL, RSS, AS = (300, 301), 600, 4831838208, 7516192768
ACTIVE_RUN = None

def limits():
    resource.setrlimit(resource.RLIMIT_CPU, CPU)
    resource.setrlimit(resource.RLIMIT_AS, (AS, AS))

def command(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()

def snapshot_external(prefix, packages):
    """Observe current compiler/package bytes; records only this execution environment."""
    snapshot = {}
    for root, label in [(prefix, 'toolchain'), *[(p, 'packages/' + p.name) for p in packages]]:
        for directory, dirs, names in os.walk(root):
            dirs[:] = sorted(x for x in dirs if x not in ['.git', '__pycache__'])
            for name in sorted(names + [x for x in dirs if (Path(directory) / x).is_symlink()]):
                path = Path(directory) / name
                key = label + '/' + path.relative_to(root).as_posix()
                entry = {}
                if path.is_symlink(): entry['symlink'] = os.readlink(path)
                if path.is_file(): entry.update(bytes=path.stat().st_size, sha256=digest(path))
                if not entry: raise ValueError('Unexpected external file type: ' + key)
                snapshot[key] = entry
    return snapshot

def inspect_environment(lean, source_archives=None):
    version = command([str(lean), '--version'])
    if not re.search(r'Lean \(version 4\.19\.0(?:[, )])', version):
        raise ValueError('Expected Lean 4.19.0; received ' + version)
    prefix = Path(command([str(lean), '--print-prefix'])).resolve()
    pins = json.loads((ROOT / 'DEPENDENCY_PINS.json').read_text())
    packages = ROOT / 'project/.lake/packages'
    paths = []
    for package in pins['packages']:
        p = packages / package['name']
        if not p.is_dir():
            raise ValueError('Missing package: ' + package['name'])
        if source_archives:
            archive = source_archives / package['source_archive_filename']
            if archive.stat().st_size != package['bytes'] or digest(archive) != package['sha256']:
                raise ValueError('Source archive hash mismatch: ' + package['name'])
            with tarfile.open(archive, 'r:gz') as tar:
                for member in tar:
                    if not (member.isfile() or member.issym()): continue
                    relative = Path(member.name).parts[1:]
                    if not relative or '..' in relative:
                        raise ValueError('Unexpected source archive member')
                    target = p.joinpath(*relative)
                    if member.issym():
                        if not target.is_symlink() or os.readlink(target) != member.linkname:
                            raise ValueError('Installed source symlink differs: ' + str(target))
                        continue
                    expected = hashlib.sha256(tar.extractfile(member).read()).hexdigest()
                    if target.is_symlink() or not target.is_file() or digest(target) != expected:
                        raise ValueError('Installed source differs from verified archive: ' + str(target))
        else:
            head = command(['git', 'rev-parse', 'HEAD'], cwd=p)
            if head != package['git_revision']:
                raise ValueError('Incorrect package revision: ' + package['name'])
            subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=p, check=True)
        paths.append(p)
    return prefix, paths, {'lean_version': version,
                            'package_git_pins_checked': not bool(source_archives),
                            'pinned_source_archive_contents_checked': bool(source_archives),
                            'external_environment_rechecked_after_run': False}

def check_source_manifest(expected_hash):
    if digest(ROOT / 'SOURCE_MANIFEST.json') != expected_hash:
        raise ValueError('Source manifest changed during replay')


def check_exports(objects, accepted):
    """Bind available project object bytes to the hashes accepted by this run."""
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


def main():
    global ACTIVE_RUN
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', help='Lean executable; default: lean from PATH')
    parser.add_argument('--preflight', action='store_true', help='Check prerequisites, then exit without compiling')
    parser.add_argument('--source-archives', type=Path,
                        help='Directory of exact pinned dependency .tar.gz archives, as an alternative to Git checkouts')
    args = parser.parse_args()
    if sys.platform != 'linux': raise ValueError('This bounded helper currently supports Linux only')
    lean = args.lean or shutil.which('lean')
    if not lean: raise ValueError('Lean is not installed or not on PATH. See REPRODUCING.md.')
    lean = Path(lean).resolve()
    source_manifest_hash = digest(ROOT / 'SOURCE_MANIFEST.json')
    sources, edges = source_checks()
    check_source_manifest(source_manifest_hash)
    prefix, packages, environment = inspect_environment(lean, args.source_archives)
    check_source_manifest(source_manifest_hash)
    if args.preflight:
        print(json.dumps({'status': 'PREFLIGHT_PASS', **environment}, indent=2)); return
    parent = ROOT / 'replay'; parent.mkdir(exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='fresh-', dir=parent))
    objects = run / 'objects'; objects.mkdir()
    logs = run / 'logs'; logs.mkdir()
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = ':'.join(str(p) for p in [objects, *[p / '.lake/build/lib/lean' for p in packages], prefix / 'lib/lean', ROOT / 'project/.lake/packages/mathlib'])
    env['LEAN_SRC_PATH'] = ':'.join(str(p) for p in [ROOT / 'project', *packages, prefix / 'src/lean'])
    # No packaged or pre-existing project object directory is on LEAN_PATH.
    summary = {'status': 'RUNNING', 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'helper_sha256': digest(Path(__file__)), 'lean_executable_sha256': digest(lean),
               'environment': environment, 'flags': FLAGS, 'accepted': [], 'failure': None,
               'source_manifest_sha256': source_manifest_hash,
               'accepted_dependency_exports_checked': True,
               'final_project_exports_rechecked_after_run': False}
    accepted_exports = {}
    ACTIVE_RUN = (run, summary)
    summary['stage'] = 'Initial external inventory'
    def save(): (run / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
    save()
    external_before = snapshot_external(prefix, packages)
    external_path = run / 'external_environment.json'
    external_path.write_text(json.dumps({'scope': 'Observed compiler/package files at this fresh run; not an inventory of the whole operating system.', 'files': external_before}, indent=2) + '\n')
    summary['environment']['fresh_external_inventory_sha256'] = digest(external_path)
    summary['environment']['fresh_external_file_count'] = len(external_before)
    save()
    for module in sources['module_order']:
        summary['stage'] = 'Compile ' + module; save()
        check_source_manifest(source_manifest_hash)
        source = ROOT / 'project' / (module + '.lean')
        if digest(source) != sources['modules'][module]['sha256']:
            raise ValueError('Source changed before replay: ' + module)
        imported = dependency_hashes(objects, edges[module], accepted_exports)
        output = objects / (module + '.olean')
        log = logs / (module + '.log')
        cmd = [str(lean), *FLAGS, '-o', str(output), str(source)]
        start = time.monotonic(); peak = 0; stop = None
        with log.open('wb') as stream:
            child = subprocess.Popen(cmd, cwd=ROOT / 'project', env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, preexec_fn=limits, start_new_session=True)
            try:
                while child.poll() is None:
                    try:
                        pages = int(Path(f'/proc/{child.pid}/statm').read_text().split()[1])
                        peak = max(peak, pages * os.sysconf('SC_PAGE_SIZE'))
                    except (FileNotFoundError, ProcessLookupError): pass
                    if peak > RSS: stop = 'RSS_CAP'
                    if time.monotonic() - start > WALL: stop = 'WALL_CAP'
                    if stop:
                        try: os.killpg(child.pid, signal.SIGKILL)
                        except ProcessLookupError: pass
                    time.sleep(0.2)
            except BaseException:
                try: os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                child.wait(); raise
        receipt = {'module': module, 'returncode': child.returncode, 'external_stop': stop,
                   'elapsed_seconds': round(time.monotonic() - start, 3), 'sampled_peak_rss_bytes': peak,
                   'source_sha256': digest(source), 'log_sha256': digest(log),
                   'dependency_export_sha256': imported}
        passed = child.returncode == 0 and stop is None and output.is_file() and not output.is_symlink()
        passed = passed and receipt['source_sha256'] == sources['modules'][module]['sha256']
        check_source_manifest(source_manifest_hash)
        try:
            check_exports(objects, imported)
        except (ValueError, OSError) as error:
            passed = False
            receipt['verification_error'] = str(error)
        if passed and module in sources['audit_results']:
            try: check_audit(log.read_text(), sources['audit_results'][module])
            except ValueError: passed = False
        receipt['accepted'] = passed
        if passed: receipt['export_sha256'] = digest(output)
        (logs / (module + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({k: receipt[k] for k in ['module', 'accepted', 'elapsed_seconds']}), flush=True)
        if not passed:
            summary['status'] = 'FAILED'; summary['failure'] = module; save()
            raise ValueError('Replay failed for ' + module + '; inspect ' + str(log))
        accepted_exports[module] = receipt['export_sha256']
        summary['accepted'].append(module); save()
    # Recheck source pins and every accepted object, including terminal modules.
    summary['stage'] = 'Final source, project export and external inventory checks'; save()
    check_source_manifest(source_manifest_hash)
    source_checks()
    check_source_manifest(source_manifest_hash)
    check_exports(objects, accepted_exports)
    summary['final_project_exports_rechecked_after_run'] = True
    inspect_environment(lean, args.source_archives)
    if snapshot_external(prefix, packages) != external_before:
        summary['status'] = 'FAILED'; summary['failure'] = 'External environment changed'; save()
        raise ValueError('Compiler/package inventory or bytes changed during replay')
    check_source_manifest(source_manifest_hash)
    check_exports(objects, accepted_exports)
    summary['environment']['external_environment_rechecked_after_run'] = True
    summary['status'] = 'FRESH_REPLAY_PASS'; summary['stage'] = 'Complete'; save()
    print(str(run / 'result.json'))

if __name__ == '__main__':
    try: main()
    except BaseException as error:
        if ACTIVE_RUN is not None:
            run, summary = ACTIVE_RUN
            summary['status'] = 'INTERRUPTED' if isinstance(error, KeyboardInterrupt) else 'FAILED'
            summary['failure'] = str(error) or type(error).__name__
            (run / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
        if isinstance(error, SystemExit): raise
        print('REPLAY STOPPED: ' + str(error), file=sys.stderr)
        sys.exit(130 if isinstance(error, KeyboardInterrupt) else 1)
