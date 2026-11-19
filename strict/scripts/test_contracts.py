#!/usr/bin/env python3
"""Contract bindings reject altered excerpts and incomplete source locations."""
from pathlib import Path
import json
import tempfile
import unittest
from check_package import digest
from check_contracts import verify


class ContractBindings(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'project').mkdir()
        source = 'import Mathlib\nnamespace Example\ntheorem result : True := by trivial\nend Example\n'
        path = self.root / 'project/A.lean'
        path.write_text(source)
        manifest = {'modules': {'A': {'sha256': digest(path)}}}
        (self.root / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest))
        start = source.index('theorem')
        end = source.index(':=')
        self.fragment = {'module': 'A', 'start_offset': start, 'end_offset': end,
                         'start_line': 3, 'end_line': 3, 'text': source[start:end]}
        self.index = {
            'schema_version': 1,
            'source_manifest_sha256': digest(self.root / 'SOURCE_MANIFEST.json'),
            'modules': {'A': {'path': 'project/A.lean', 'sha256': digest(path),
                              'direct_imports': ['Mathlib']}},
            'declarations': [{'id': 'C01', 'name': 'Example.result', 'kind': 'theorem',
                              'signature': self.fragment, 'ambient_context': [],
                              'related_contracts': []}],
            'definitions': [], 'historical_obligations': []}

    def tearDown(self): self.temp.cleanup()

    def check(self):
        (self.root / 'CONTRACTS.json').write_text(json.dumps(self.index))
        return verify(self.root)

    def test_exact_source_passes(self):
        self.assertEqual(self.check()['contracts'], 1)

    def test_altered_signature_rejected(self):
        self.fragment['text'] = self.fragment['text'].replace('True', 'False')
        with self.assertRaisesRegex(ValueError, 'fragment differs'): self.check()

    def test_incomplete_location_rejected(self):
        del self.fragment['start_line']
        with self.assertRaisesRegex(ValueError, 'Incomplete source'): self.check()

    def test_wrong_declaration_name_rejected(self):
        self.index['declarations'][0]['name'] = 'Example.other'
        with self.assertRaisesRegex(ValueError, 'Declaration name'): self.check()

    def test_wrong_namespace_rejected(self):
        self.index['declarations'][0]['name'] = 'Other.result'
        with self.assertRaisesRegex(ValueError, 'namespace differs'): self.check()

    def test_unknown_bibliography_key_rejected(self):
        self.index['declarations'][0]['literature'] = ['missing-reference']
        (self.root / 'references.bib').write_text('@article{known-reference, title={Example}}\n')
        with self.assertRaisesRegex(ValueError, 'bibliography keys'): self.check()

    def test_unknown_related_contract_rejected(self):
        self.index['declarations'][0]['related_contracts'] = ['C99']
        with self.assertRaisesRegex(ValueError, 'Unknown related'): self.check()


if __name__ == '__main__': unittest.main()
