"""Preserve the actual full recorder invocation without editing its source."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
helper = BASE / 'install_and_compile_six_v2.py'
log = BASE / 'install-and-compile-six-v2-actual-v1.log'
receipt = BASE / 'install-and-compile-six-v2-actual-v1.json'
def ref(p):
    return {'file': str(p.relative_to(ROOT)), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
before = ref(helper)
wrapper = ref(Path(__file__))
command = ['python3', str(helper)]
started = datetime.now(timezone.utc).isoformat()
start = time.monotonic()
with log.open('xb') as raw:
    result = subprocess.run(command, cwd=ROOT, stdout=raw, stderr=subprocess.STDOUT, check=False)
elapsed = time.monotonic() - start
finished = datetime.now(timezone.utc).isoformat()
record = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_command': command,
          'actual_workdir': str(ROOT), 'actual_exit_code': result.returncode,
          'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
          'helper': before, 'helper_sha256_after': ref(helper)['sha256'],
          'wrapper': wrapper, 'wrapper_sha256_after': ref(Path(__file__))['sha256'],
          'raw_log': ref(log), 'coverage_complete': False}
with receipt.open('x') as out:
    out.write(json.dumps(record, indent=2) + '\n')
log.chmod(0o444)
receipt.chmod(0o444)
helper.chmod(0o444)
Path(__file__).chmod(0o444)
print(json.dumps(record), flush=True)
raise SystemExit(result.returncode)
