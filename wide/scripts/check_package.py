#!/usr/bin/env python3
# Derived from the strict source-focused checker; modified for the broad v5
# source closure, 19 November 2026. The strict distribution is left unchanged.
# Original project attribution and Apache-2.0 terms are retained in NOTICE/LICENSE.
"""Read-only broad v5 package integrity and source checks; does not execute Lean."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = {'Mathlib', 'Lean', 'Std', 'Init', 'Batteries', 'Aesop', 'Qq',
            'ProofWidgets', 'Plausible', 'LeanSearchClient', 'ImportGraph', 'Cli'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_ROOTS = ['V5WideFinal140']
EXPECTED_MODULE_COUNT = 669
SOURCE_OPTIONS = {'maxHeartbeats', 'synthInstance.maxHeartbeats', 'maxRecDepth',
                  'Elab.async', 'linter.unusedSectionVars'}


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def lean_code(text):
    """Remove nested comments and strings; a scan, not a complete Lean parser."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            out.append(' ')
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            out.append(' ')
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('Unterminated Lean string')
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(out)


def imports_from_code(code):
    """Read the single-line import headers used by this frozen source closure."""
    imports = []
    for line in code.splitlines():
        if line.strip().startswith('import '):
            imports.extend(line.strip()[7:].split())
    return imports


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _options(code):
    return [{'name': name, 'value': value} for name, value in re.findall(
        r'\bset_option\s+([A-Za-z_][A-Za-z_0-9.]*)\s+(\S+)', code)]


def _safe_member(root, name):
    _require(isinstance(name, str) and '\\' not in name and '\x00' not in name,
             'Invalid distribution member name')
    relative = Path(name)
    _require(not relative.is_absolute() and '..' not in relative.parts and
             relative.as_posix() == name and name not in {'', '.'},
             'Invalid distribution member: ' + name)
    path = root / relative
    _require(path.is_file() and not path.is_symlink() and
             path.resolve().is_relative_to(root), 'Invalid distribution member: ' + name)
    for parent in path.parents:
        if parent == root:
            break
        _require(not parent.is_symlink(), 'Symlink ancestor: ' + name)
    return path


def source_checks(root=ROOT):
    root = Path(root).resolve()
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    modules, order, roots = manifest['modules'], manifest['module_order'], manifest['roots']
    _require(isinstance(modules, dict) and modules, 'Empty or invalid module inventory')
    _require(manifest.get('module_count', len(modules)) == len(modules), 'Source module count mismatch')
    _require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', m) for m in modules),
             'Invalid flat project module name')
    _require(len({m.casefold() for m in modules}) == len(modules), 'Case-colliding module names')
    _require(len(order) == len(set(order)) and set(order) == set(modules),
             'Module order inventory mismatch')
    _require(isinstance(roots, list) and roots and len(roots) == len(set(roots)) and
             all(m in modules for m in roots), 'Invalid root module list')
    project = root / 'project'
    _require(project.is_dir() and not project.is_symlink(), 'Invalid project directory')
    actual = {p.relative_to(project).as_posix() for p in project.rglob('*.lean')
              if '.lake' not in p.relative_to(project).parts and
              p.relative_to(project).as_posix() != 'lakefile.lean'}
    _require(actual == {m + '.lean' for m in modules}, 'Project source inventory mismatch')
    seen, edges, external = set(), {}, set()
    for module in order:
        record = modules[module]
        _require(record['path'] == 'project/' + module + '.lean', 'Unexpected source path: ' + module)
        path = _safe_member(root, record['path'])
        _require(path.stat().st_size == record['bytes'] and digest(path) == record['sha256'],
                 'Source mismatch: ' + module)
        code = lean_code(path.read_text())
        _require(not re.search(r'\b(?:sorry|sorryAx|admit|axiom|unsafe|implemented_by|native_decide)\b', code),
                 'Disallowed source token: ' + module)
        options = _options(code)
        expected_options = [{'name': x['name'], 'value': str(x['value'])} for x in record['options']]
        _require(options == expected_options, 'Source option inventory mismatch: ' + module)
        for option in options:
            name, value = option['name'], option['value']
            _require(name in SOURCE_OPTIONS, 'Unapproved source option: ' + module)
            if name in {'maxHeartbeats', 'synthInstance.maxHeartbeats', 'maxRecDepth'}:
                _require(value.isdigit() and int(value) > 0, 'Unbounded or invalid source limit: ' + module)
            elif name == 'Elab.async':
                _require(value == 'false', 'Asynchronous elaboration enabled: ' + module)
            else:
                _require(value in {'true', 'false'}, 'Invalid linter option: ' + module)
        imports = imports_from_code(code)
        _require(imports == record['imports'], 'Import inventory mismatch: ' + module)
        local = [m for m in imports if m.split('.')[0] not in EXTERNAL]
        _require(all(m in seen for m in local), 'Missing or non-topological local import: ' + module)
        external.update(m for m in imports if m.split('.')[0] in EXTERNAL)
        edges[module] = local
        seen.add(module)
    recorded_external = manifest['external_imports']
    _require(len(recorded_external) == len(set(recorded_external)) and set(recorded_external) == external,
             'External import inventory mismatch')
    closure = set()
    def visit(module):
        if module not in closure:
            closure.add(module)
            for dependency in edges[module]:
                visit(dependency)
    for module in roots:
        visit(module)
    _require(closure == set(modules), 'Unrelated source outside root dependency closure')
    total_bytes = sum(record['bytes'] for record in modules.values())
    _require(manifest.get('source_bytes', total_bytes) == total_bytes, 'Source byte count mismatch')
    expected_axioms = manifest.get('audit_results', {})
    _require(isinstance(expected_axioms, dict) and expected_axioms, 'Missing expected axiom reports')
    for module, reports in expected_axioms.items():
        _require(module in modules and isinstance(reports, dict) and reports, 'Invalid audit module')
        for name, axioms in reports.items():
            _require(isinstance(name, str) and isinstance(axioms, list) and
                     len(axioms) == len(set(axioms)) and set(axioms) <= ALLOWED_AXIOMS,
                     'Invalid expected axiom report')
    return manifest, edges


def check_audit(log, expected):
    """Validate reported axioms in a supplied Lean log; not proof execution."""
    _require(not re.search(r'\berror:|\bsorryAx\b|INTERNAL PANIC', log), 'Failed or incomplete Lean audit log')
    parsed = {}
    reports = [(name, re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', text))
               for name, text in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S)]
    reports += [(name, []) for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    for name, axioms in reports:
        found = sorted(axioms)
        _require(set(found) <= ALLOWED_AXIOMS, 'Unexpected reported axiom')
        _require(name not in parsed or parsed[name] == found, 'Conflicting duplicate axiom reports: ' + name)
        parsed[name] = found
    for name, axioms in expected.items():
        _require(parsed.get(name) == sorted(axioms), 'Missing or unexpected axiom report: ' + name)
    return parsed


def verify(root=ROOT):
    root = Path(root).resolve()
    distribution = json.loads((root / 'MANIFEST.json').read_text())
    files = distribution['files']
    _require(isinstance(files, dict) and files, 'Empty or invalid distribution manifest')
    _require('MANIFEST.json' not in files, 'Manifest cannot hash itself')
    _require(len({name.casefold() for name in files}) == len(files), 'Case-colliding distribution paths')
    for name, expected in files.items():
        path = _safe_member(root, name)
        _require(path.stat().st_size == expected['bytes'] and digest(path) == expected['sha256'],
                 'Distribution member mismatch: ' + name)
    unexpected = []
    for path in root.rglob('*'):
        if not path.is_file() and not path.is_symlink():
            continue
        name = path.relative_to(root).as_posix()
        if name == 'MANIFEST.json' or name in files:
            continue
        if name == '.git' or name.startswith('.git/'):
            continue
        if name.startswith(('.lake/', 'project/.lake/')) or '__pycache__' in path.parts:
            continue
        unexpected.append(name)
    _require(not unexpected, 'Unexpected distribution files: ' + ', '.join(sorted(unexpected)[:10]))
    sources, _ = source_checks(root)
    _require(len(sources['modules']) == EXPECTED_MODULE_COUNT and sources['roots'] == EXPECTED_ROOTS,
             'Canonical wide closure root or module count mismatch')
    return {'status': 'PACKAGE_INTEGRITY_PASS', 'source_modules': len(sources['modules']),
            'root_modules': sources['roots'], 'source_bytes_match_manifest': True,
            'fresh_Lean_replay_performed': False,
            'notice': 'Static hash, closure, source-option and token checks only. No Lean execution performed.'}


def main():
    print(json.dumps(verify(), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RecursionError) as error:
        print('CHECK FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
