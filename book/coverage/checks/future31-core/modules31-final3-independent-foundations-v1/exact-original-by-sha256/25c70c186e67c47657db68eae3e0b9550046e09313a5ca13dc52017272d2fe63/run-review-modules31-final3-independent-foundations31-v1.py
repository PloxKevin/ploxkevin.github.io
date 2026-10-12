from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CHECK = Path('/tmp/review-modules31-final3-independent-foundations31-v1.py')
OUT = Path('/tmp/modules31-final3-independent-foundations31-actual-v1.json')
LOG = OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(CONTEXT) == 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
context = json.loads(CONTEXT.read_bytes())
protected = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
assert all(sha(ROOT/n) == h for n, h in protected.items())
before = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT), str(Path(__file__)): sha(Path(__file__))}
started = datetime.now(timezone.utc).isoformat()
t = time.monotonic()
command = ['python3', str(CHECK)]
native = subprocess.run(command, cwd=ROOT, capture_output=True)
LOG.write_bytes(native.stdout+native.stderr)
after = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT), str(Path(__file__)): sha(Path(__file__))}
protection_errors = [n for n, h in protected.items() if sha(ROOT/n) != h]
d = {
    'status': 'passed' if native.returncode == 0 and not protection_errors and before == after else 'failed',
    'actual_command': command, 'actual_workdir': str(ROOT),
    'actual_exit_code': native.returncode,
    'started_at_utc': started, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic()-t,
    'helper_sha256_before': before, 'helper_sha256_after': after,
    'log': str(LOG), 'log_sha256': sha(LOG),
    'protected_inputs_sha256_before': protected,
    'protected_inputs_sha256_after': {n: sha(ROOT/n) for n in protected},
    'protection_errors': protection_errors,
    'scope': 'Actual independent Module31 final3 full owner forward/inverse, Integral39 four-whole/one-exercise, AST19 NF leaf and true two-pair mapping review; current81 guarded, no producer/compiler/current-owner or publication writes.',
}
OUT.write_text(json.dumps(d, indent=2)+'\n')
print(json.dumps({k: d[k] for k in ['status', 'actual_exit_code', 'elapsed_seconds', 'protection_errors']}))
raise SystemExit(0 if d['status'] == 'passed' else 1)
