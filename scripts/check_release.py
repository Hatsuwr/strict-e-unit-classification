#!/usr/bin/env python3
# Modified for the source-focused edition, 12 November 2026.
"""Check package bytes, source contracts and offline regressions. Does not run Lean."""
import io
import json
import sys
import unittest
import zipfile
from check_package import ROOT, verify as verify_package
from check_contracts import verify as verify_contracts


def main():
    package = verify_package()
    contracts = verify_contracts()
    suite = unittest.defaultTestLoader.discover(str(ROOT / 'scripts'), pattern='test_*.py')
    output = io.StringIO()
    tests = unittest.TextTestRunner(stream=output).run(suite)
    if not tests.wasSuccessful() or tests.testsRun == 0 or tests.skipped or tests.expectedFailures:
        raise ValueError('Offline regressions did not all pass:\n' + output.getvalue())
    print(json.dumps({
        'status': 'SOURCE_RELEASE_CHECK_PASS',
        'package': package,
        'contracts': contracts,
        'offline_regressions': {'run': tests.testsRun, 'passed': tests.testsRun,
                                'failures': 0, 'errors': 0, 'skipped': 0},
        'fresh_Lean_execution_performed': False,
        'public_release_authorized': False
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, zipfile.BadZipFile) as error:
        print('RELEASE CHECK FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
