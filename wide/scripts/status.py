#!/usr/bin/env python3
# Wide v5 verification status reader, 19 November 2026. Apache-2.0.
"""Read a buffered replay result; does not execute Lean or promote partial results."""
import argparse
import datetime
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('run', type=Path)
a = p.parse_args()
x = json.loads((a.run / 'result.json').read_text())
updated = datetime.datetime.fromisoformat(x['last_updated_utc'])
age = (datetime.datetime.now(datetime.timezone.utc) - updated).total_seconds()
status = x['status']
if status == 'RUNNING' and age > x.get('limits', {}).get('wall_seconds_per_module', 600) + 120:
    status = 'RUNNING_UNCONFIRMED_STALE_RECEIPT'
print(json.dumps({'status': status, 'scope': x['scope'],
                  'accepted_modules': len(x.get('accepted', [])),
                  'source_modules': x['source_modules'], 'stage': x['stage'],
                  'last_updated_utc': x['last_updated_utc'],
                  'failure': x.get('failure')}, indent=2))
