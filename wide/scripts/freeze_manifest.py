#!/usr/bin/env python3
# Wide v5 source packaging, 19 November 2026. Apache-2.0; see LICENSE and NOTICE.
"""Refresh only distribution-file hashes after reviewed documentation/tool changes.
Canonical proof-source hashes and imports must already pass; they are never rewritten.
"""
from pathlib import Path
import json
from check_package import ROOT, digest, source_checks


def main():
    source_checks()
    files = {}
    for path in sorted(ROOT.rglob('*')):
        if not path.is_file() and not path.is_symlink():
            continue
        rel = path.relative_to(ROOT).as_posix()
        if rel == 'MANIFEST.json':
            continue
        if path.is_symlink():
            raise ValueError('Do not package symlinks: ' + rel)
        if ('.git' in path.parts or '.lake' in path.parts or '__pycache__' in path.parts or
                path.suffix in {'.olean', '.ilean', '.pyc', '.log', '.o', '.trace', '.zip', '.gz', '.zst'}):
            raise ValueError('Generated/external/private working file in source package: ' + rel)
        if path.suffix == '.lean' and path.parent != ROOT / 'project':
            raise ValueError('Unrelated Lean source outside project/: ' + rel)
        files[rel] = {'bytes': path.stat().st_size, 'sha256': digest(path)}
    manifest = {'format': 1, 'package': 'wide-v5-source-preview',
                'source_manifest_sha256': digest(ROOT / 'SOURCE_MANIFEST.json'),
                'files': files}
    (ROOT / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'status': 'MANIFEST_FROZEN', 'files': len(files),
                      'fresh_Lean_execution_performed': False}, indent=2))


if __name__ == '__main__':
    main()
