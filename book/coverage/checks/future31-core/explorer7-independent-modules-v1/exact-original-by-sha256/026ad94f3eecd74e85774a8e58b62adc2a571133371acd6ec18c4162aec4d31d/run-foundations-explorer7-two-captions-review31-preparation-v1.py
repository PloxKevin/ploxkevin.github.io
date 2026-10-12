from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
CONTEXT = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
CHECK = Path('/tmp/prepare-foundations-explorer7-two-captions-review31-v1.py')
OUT = Path('/tmp/foundations-explorer7-two-captions-review31-preparation-actual-v1.json')
LOG = OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(CONTEXT) == '73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
context = json.loads(CONTEXT.read_bytes())
protected = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
assert all(sha(ROOT/n) == h for n, h in protected.items())
before = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT)}
started = datetime.now(timezone.utc).isoformat()
t = time.monotonic()
command = ['python3', str(CHECK)]
native = subprocess.run(command, cwd=ROOT, capture_output=True)
LOG.write_bytes(native.stdout+native.stderr)
after = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT)}
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
    'scope': 'Actual genuine7 explorer models/full1437-1452 captions review preparation with complete current HTML/JS and supplementary actual all200 horizon validation, all1242/31/raw30 guards; no Lean/source/owner/PUB mutation.',
}
OUT.write_text(json.dumps(d, indent=2)+'\n')
print(json.dumps({k: d[k] for k in ['status', 'actual_exit_code', 'elapsed_seconds', 'protection_errors']}))
raise SystemExit(0 if d['status'] == 'passed' else 1)
