#!/usr/bin/env python3
"""Record an actual source-fingerprinted local compilation of a core module."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('module')
args = parser.parse_args()
if not args.module.startswith('Complete') or not args.module.isidentifier():
    raise ValueError('Expected an existing Complete module basename.')
source = ROOT / 'verification/lean/SafeLearning' / (args.module + '.lean')
log = ROOT / 'book/coverage/checks' / (args.module + '.log')
record_path = log.with_name(args.module + '-standalone.json')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


before = sha(source)
command = ['lake', 'env', 'lean', 'SafeLearning/' + args.module + '.lean']
started = time.monotonic()
with log.open('wb') as output:
    result = subprocess.run(command, cwd=ROOT / 'verification/lean',
                            stdout=output, stderr=subprocess.STDOUT)
after = sha(source)
passed = result.returncode == 0 and before == after
record = {
    'status': 'passed' if passed else 'failed',
    'source': str(source.relative_to(ROOT)),
    'source_sha256_before': before, 'source_sha256_after': after,
    'source_unchanged': before == after, 'exit_code': result.returncode,
    'command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic() - started,
    'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
    'scope': 'Actual standalone compiler execution; aggregate build, kernel replay and axiom audit remain separate.'}
record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(0 if passed else 1)
