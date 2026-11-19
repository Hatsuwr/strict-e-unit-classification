#!/usr/bin/env python3
# Modified for the source-focused edition, 12 November 2026.
"""Read-only distribution integrity and narrowly scoped source/audit checks."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = {'Mathlib', 'Lean', 'Std', 'Init', 'Batteries', 'Aesop', 'Qq',
            'ProofWidgets', 'Plausible', 'LeanSearchClient', 'ImportGraph', 'Cli'}

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def lean_code(text):
    """Remove nested comments and strings; a scan, not a complete Lean parser."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i): depth = 1; i += 2; out.append(' ')
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j; out.append(' ')
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(' ')
        else: out.append(text[i]); i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(out)


def imports_from_code(code):
    """Read the single-line import headers used by this frozen source tree."""
    imports = []
    for line in code.splitlines():
        if line.strip().startswith('import '):
            imports.extend(line.strip()[7:].split())
    return imports

def source_checks(root=ROOT):
    root = Path(root).resolve()
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    modules = manifest['modules']
    order = manifest['module_order']
    if any(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', module) is None for module in modules):
        raise ValueError('Invalid project module name')
    if len(order) != len(set(order)) or set(order) != set(modules):
        raise ValueError('Module order inventory mismatch')
    actual = {p.stem for p in (root / 'project').glob('*.lean') if p.name != 'lakefile.lean'}
    if actual != set(modules):
        raise ValueError('Project source inventory mismatch')
    seen, edges = set(), {}
    for module in order:
        path = root / 'project' / (module + '.lean')
        expected = modules[module]
        if path.is_symlink() or not path.is_file():
            raise ValueError('Invalid project source: ' + module)
        if path.stat().st_size != expected['bytes'] or digest(path) != expected['sha256']:
            raise ValueError('Source mismatch: ' + module)
        code = lean_code(path.read_text())
        if re.search(r'\b(?:sorry|sorryAx|admit|axiom|unsafe|implemented_by|native_decide)\b', code):
            raise ValueError('Disallowed source token: ' + module)
        for option, value in re.findall(r'\bset_option\s+(maxHeartbeats|synthInstance.maxHeartbeats)\s+(\S+)', code):
            cap = 200000 if option == 'maxHeartbeats' else 20000
            if not value.isdigit() or not 0 < int(value) <= cap:
                raise ValueError('Unexpected heartbeat setting: ' + module)
        if re.search(r'\bset_option\s+Elab.async\s+true', code):
            raise ValueError('Asynchronous elaboration enabled: ' + module)
        imports = imports_from_code(code)
        local = [x for x in imports if x.split('.')[0] not in EXTERNAL]
        if any(x not in seen for x in local):
            raise ValueError('Missing or non-topological local import: ' + module)
        edges[module] = local
        seen.add(module)
    return manifest, edges

def check_audit(log, expected):
    parsed = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S):
        found = sorted(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', axioms))
        if not set(found) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected reported axiom')
        if name in parsed and parsed[name] != found:
            raise ValueError('Conflicting duplicate axiom reports: ' + name)
        parsed[name] = found
    for name, axioms in expected.items():
        if parsed.get(name) != sorted(axioms):
            raise ValueError('Missing or unexpected axiom report: ' + name)
    for axioms in parsed.values():
        if not set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected reported axiom')
    return parsed

def verify(root=ROOT):
    root = Path(root).resolve()
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    for name, expected in manifest['files'].items():
        relative = Path(name)
        path = root / relative
        if (relative.is_absolute() or '..' in relative.parts or
                path.is_symlink() or not path.is_file() or
                not path.resolve().is_relative_to(root)):
            raise ValueError('Invalid distribution member: ' + name)
        if path.stat().st_size != expected['bytes'] or digest(path) != expected['sha256']:
            raise ValueError('Distribution member mismatch: ' + name)
    # Permit only documented generated working directories in an extracted tree.
    unexpected = []
    for path in root.rglob('*'):
        if not path.is_file() and not path.is_symlink(): continue
        name = path.relative_to(root).as_posix()
        if name == 'MANIFEST.json' or name in manifest['files']: continue
        if name == '.git' or name.startswith('.git/'): continue
        if name.startswith(('project/.lake/', 'replay/')): continue
        if '__pycache__' in path.parts: continue
        unexpected.append(name)
    if unexpected:
        raise ValueError('Unexpected distribution files: ' + ', '.join(unexpected[:10]))
    sources, _ = source_checks(root)
    return {'status': 'PACKAGE_INTEGRITY_PASS', 'source_modules': len(sources['modules']),
            'source_bytes_match_manifest': True,
            'fresh_Lean_replay_performed': False,
            'notice': 'Hash and source checks only. No Lean execution or historical replay-record check.'}



def main():
    print(json.dumps(verify(), indent=2))

if __name__ == '__main__':
    try: main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('CHECK FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
