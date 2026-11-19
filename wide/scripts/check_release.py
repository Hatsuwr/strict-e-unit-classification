#!/usr/bin/env python3
# Wide v5 adaptation, 19 November 2026, of the strict offline release check.
# Apache-2.0; original attribution is retained in LICENSE and NOTICE.
"""Run package/source integrity checks and synthetic regressions, without Lean."""
import io
import json
import sys
import unittest
from check_package import ROOT, verify


def main():
    package = verify()
    suite = unittest.defaultTestLoader.discover(str(ROOT / 'scripts'), pattern='test_*.py')
    buffer = io.StringIO()
    result = unittest.TextTestRunner(stream=buffer).run(suite)
    if not result.wasSuccessful() or not result.testsRun or result.skipped or result.expectedFailures:
        raise ValueError('Offline regressions failed:\n' + buffer.getvalue())
    print(json.dumps({'status': 'STATIC_RELEASE_CHECK_PASS', 'package': package,
                      'offline_regressions': {'run': result.testsRun, 'passed': result.testsRun,
                                              'failures': 0, 'errors': 0, 'skipped': 0},
                      'fresh_Lean_execution_performed': False}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('STATIC RELEASE CHECK FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
