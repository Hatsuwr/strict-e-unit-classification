#!/usr/bin/env python3
"""Validate the contract index's exact source bindings; does not elaborate Lean."""
import json
import re
import sys
from check_package import ROOT, digest, imports_from_code, lean_code


def require(condition, message):
    if not condition:
        raise ValueError(message)


def namespace_at(text, offset):
    """Track namespace/section commands used by the indexed frozen files."""
    stack = []
    for line in lean_code(text[:offset]).splitlines():
        opened = re.fullmatch(r'\s*(?:noncomputable\s+)?(namespace|section)(?:\s+(\S+))?\s*', line)
        closed = re.fullmatch(r'\s*end(?:\s+(\S+))?\s*', line)
        if opened:
            kind, name = opened.groups()
            require(kind != 'namespace' or name is not None, 'Unnamed namespace in contract source')
            stack.append((kind, name))
        elif closed:
            require(bool(stack), 'Unmatched namespace/section end in contract source')
            kind, name = stack.pop()
            require(closed[1] is None or closed[1] == name, 'Mismatched namespace/section end')
    return '.'.join(name for kind, name in stack if kind == 'namespace')


def verify(root=ROOT):
    index = json.loads((root / 'CONTRACTS.json').read_text())
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    require(index['schema_version'] == 1, 'Unsupported contract schema')
    require(index['source_manifest_sha256'] == digest(root / 'SOURCE_MANIFEST.json'),
            'Contract source-manifest binding differs')
    texts = {}
    require(bool(index['modules']), 'Empty contract module index')
    for module, record in index['modules'].items():
        require(module in manifest['modules'], 'Unknown contract module: ' + module)
        require(record['path'] == 'project/' + module + '.lean', 'Unexpected source path: ' + module)
        path = root / record['path']
        require(not path.is_symlink() and path.is_file(), 'Invalid contract source: ' + module)
        require(digest(path) == record['sha256'] == manifest['modules'][module]['sha256'],
                'Contract source hash differs: ' + module)
        texts[module] = path.read_text()
        require(imports_from_code(lean_code(texts[module])) == record['direct_imports'],
                'Contract direct imports differ: ' + module)

    fragment_keys = {'module', 'start_offset', 'end_offset', 'start_line', 'end_line', 'text'}
    fragments = 0
    def check_fragments(value):
        nonlocal fragments
        if isinstance(value, list):
            for child in value: check_fragments(child)
        elif isinstance(value, dict):
            if 'start_offset' in value or 'end_offset' in value or {'module', 'text'} <= value.keys():
                require(fragment_keys <= value.keys(), 'Incomplete source fragment')
                module = value['module']
                require(module in texts, 'Unbound fragment module: ' + module)
                text = texts[module]
                start, end = value['start_offset'], value['end_offset']
                require(type(start) is int and type(end) is int and 0 <= start < end <= len(text),
                        'Invalid source fragment offsets: ' + module)
                require(text[start:end] == value['text'], 'Source fragment differs: ' + module)
                require(value['start_line'] == 1 + text.count('\n', 0, start) and
                        value['end_line'] == 1 + text.count('\n', 0, end - 1),
                        'Source fragment lines differ: ' + module)
                fragments += 1
            for child in value.values(): check_fragments(child)
    check_fragments(index)

    def declaration(record, field):
        require(fragment_keys <= record[field].keys(), 'Incomplete declaration source fragment')
        kind = record['kind']
        require(kind in {'theorem', 'lemma', 'def', 'abbrev', 'structure', 'opaque'},
                'Unsupported declaration kind: ' + kind)
        fragment = record[field]
        found = re.search(r'\b' + re.escape(kind) + r'\s+([^\s:(]+)', lean_code(fragment['text']))
        require(found is not None,
                'Declaration name is not bound to its source: ' + record['name'])
        declared = found[1]
        namespace = namespace_at(texts[fragment['module']], fragment['start_offset'])
        qualified = declared[len('_root_.'):] if declared.startswith('_root_.') else '.'.join(
            part for part in (namespace, declared) if part)
        require(qualified == record['name'], 'Declaration name or namespace differs: ' + record['name'])

    contracts = index['declarations']
    ids = [record['id'] for record in contracts]
    require(ids and len(ids) == len(set(ids)), 'Missing or duplicate contract IDs')
    for record in contracts:
        declaration(record, 'signature')
        require(all(fragment_keys <= context.keys() for context in record['ambient_context']),
                'Incomplete ambient source context: ' + record['id'])
        require(set(record['related_contracts']) <= set(ids), 'Unknown related contract: ' + record['id'])
    literature = {key for record in contracts for key in record.get('literature', [])}
    if literature:
        bibliography = (root / 'references.bib').read_text()
        keys = re.findall(r'(?m)^@\w+\s*\{\s*([^,\s]+)\s*,', bibliography)
        require(len(keys) == len(set(keys)), 'Duplicate bibliography keys')
        require(literature <= set(keys), 'Unknown contract bibliography keys: ' +
                ', '.join(sorted(literature - set(keys))))
    for record in index['definitions']:
        declaration(record, 'source')
    for obligation in index['historical_obligations']:
        require(fragment_keys <= obligation['historical_source'].keys(), 'Incomplete historical source')
        closings = obligation['closing_declarations']
        for record in closings: declaration(record, 'signature')
        require(set(obligation['discharged_by']) <= {record['name'] for record in closings},
                'Historical obligation lacks a closing source declaration')
    return {'status': 'CONTRACT_SOURCE_BINDINGS_PASS', 'modules': len(texts),
            'contracts': len(contracts), 'definitions': len(index['definitions']),
            'historical_obligations': len(index['historical_obligations']),
            'referenced_literature_keys': len(literature),
            'exact_source_fragments': fragments, 'Lean_elaboration_performed': False}


if __name__ == '__main__':
    try:
        print(json.dumps(verify(), indent=2))
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('CONTRACT CHECK FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
