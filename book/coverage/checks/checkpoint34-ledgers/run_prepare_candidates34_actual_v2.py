"""Preserve the genuine owner34 candidate-preparation subprocess outcome."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
helper = BASE/'prepare_owner_candidates34_v2.py'
route = BASE/'correspondence_routes34_v1.py'
worker = BASE/'validate_candidates34_v1.py'
def ref(p):
    return {'file': str(p.relative_to(ROOT)), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
inputs = [ref(p) for p in [helper, route, worker, Path(__file__)]]
command = ['python3', '-B', str(helper),
    '--inventory', 'book/coverage/inventory-after-correction90.json',
    '--inventory-sha256', 'fa3edbc297c59878db2226a04dc91e66493f5bf9adb67535c05b60429e1ac254',
    '--composition-review', 'book/coverage/checks/checkpoint34-review/independent-current88-two-page-whole-correspondence-approval-v1.json',
    '--composition-review-sha256', '9cfd24dfd375b50eed7040a91d4a53d23ee63eb3e6d16bfe9847331e865538fe',
    '--component-review', 'book/coverage/checks/checkpoint34-review/independent-existing-component-impact-v1.json',
    '--component-review-sha256', '95f7f850553649253a106cacda7b05dd4dc0c127adbc0053aae763356fbf8454',
    '--readiness', 'book/coverage/checks/checkpoint34-preparation-root/three-future34-paired-packets-v1.json',
    '--readiness-sha256', '77d557aa493093a61f99da05124dfa09382015f6f7cbf74ede2ef87fc2056408',
    '--tag', 'v2']
log = BASE/'prepare-owner-candidates34-actual-v2.log'
receipt = BASE/'prepare-owner-candidates34-actual-v2.json'
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with log.open('xb') as raw:
    result = subprocess.run(command, cwd=ROOT, stdout=raw, stderr=subprocess.STDOUT, check=False)
elapsed = time.monotonic()-tick
finished = datetime.now(timezone.utc).isoformat()
record = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
          'actual_command': command, 'actual_workdir': str(ROOT), 'started_at_utc': started,
          'finished_at_utc': finished, 'elapsed_seconds': elapsed, 'helpers_before': inputs,
          'helpers_after': [ref(p) for p in [helper, route, worker, Path(__file__)]],
          'raw_log': ref(log), 'candidate_installation_performed': False, 'coverage_complete': False}
with receipt.open('x') as out:
    out.write(json.dumps(record, indent=2)+'\n')
for p in [helper, route, worker, Path(__file__), log, receipt]:
    p.chmod(0o444)
print(json.dumps(record), flush=True)
raise SystemExit(result.returncode)
