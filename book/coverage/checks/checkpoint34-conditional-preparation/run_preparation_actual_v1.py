"""Capture the immutable Conditional28 preparation invocation and raw output."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
helper = BASE / 'prepare_conditional28_v1.py'
log = BASE / 'conditional28-preparation-actual-v1.log'
out = BASE / 'conditional28-preparation-actual-v1.json'
def ref(p):
    return {'file': str(p.relative_to(ROOT)), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
before = ref(helper)
wrapper = ref(Path(__file__))
command = ['python3', '-B', str(helper)]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with log.open('xb') as raw:
    result = subprocess.run(command, cwd=ROOT, stdout=raw, stderr=subprocess.STDOUT, check=False)
elapsed = time.monotonic() - tick
finished = datetime.now(timezone.utc).isoformat()
record = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_command': command,
          'actual_workdir': str(ROOT), 'actual_exit_code': result.returncode,
          'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
          'helper': before, 'helper_sha256_after': ref(helper)['sha256'],
          'wrapper': wrapper, 'wrapper_sha256_after': ref(Path(__file__))['sha256'],
          'raw_log': ref(log), 'coverage_complete': False}
with out.open('x') as f:
    f.write(json.dumps(record, indent=2) + '\n')
for p in [helper, Path(__file__), log, out]:
    p.chmod(0o444)
print(json.dumps(record), flush=True)
raise SystemExit(result.returncode)
