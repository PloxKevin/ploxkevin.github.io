from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
HELPER = Path('/tmp/check-checkpoint29-publication-four-helpers-independent-applied-v3.py')
RECORD = Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-actual-v3.json')
LOG = RECORD.with_suffix('.log')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
inventory = json.loads((ROOT/'book/coverage/inventory.json').read_bytes())
guards = {n: h for n, h in inventory['source_sha256'].items()}
for n in ('SafeLearning/style.css', 'SafeLearning/components.js', 'book/coverage/inventory.json', 'book/coverage/material-corrections.json',
          *('book/coverage/'+v+'.json' for v in ('core', 'foundations', 'modules', 'applied', 'applied-promotions'))):
    guards[n] = sha(ROOT/n)
def guard():
    for n, h in guards.items(): assert sha(ROOT/n) == h, n
guard()
before = {str(HELPER): sha(HELPER), str(Path(__file__)): sha(Path(__file__))}
command = ['python3', str(HELPER)]
start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
with LOG.open('xb') as output:
    process = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
errors = []
try: guard()
except Exception as e: errors.append(str(e))
after = {n: sha(Path(n)) for n in before}
passed = process.returncode == 0 and before == after and not errors
result = {'status': 'passed' if passed else 'failed', 'actual_exit_code': process.returncode,
          'actual_runner_exit_code': 0 if passed else 1, 'actual_command': command, 'actual_workdir': str(ROOT),
          'started_at_utc': start, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
          'elapsed_seconds': time.monotonic()-tick, 'helper_sha256_before': before, 'helper_sha256_after': after,
          'log': str(LOG), 'log_sha256': sha(LOG), 'protection_errors': errors,
          'actual_readonly_guarded_current_source_inputs': guards,
          'production_helper_invoked': False, 'git_or_publication_mutation': False,
          'scope': 'Measured independent code/guard review only. Pure functions use explicitly synthetic native records and TMP files; no actual audit29/docs/config/PUB preparation or delivery success is claimed.'}
with RECORD.open('x') as output: output.write(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'record': str(RECORD), 'actual_exit_code': process.returncode, 'protection_errors': errors}))
raise SystemExit(0 if passed else 1)
