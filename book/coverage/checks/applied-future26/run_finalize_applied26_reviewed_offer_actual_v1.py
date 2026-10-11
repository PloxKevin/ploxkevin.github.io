from pathlib import Path
from datetime import datetime, timezone
import subprocess, json, hashlib, time
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/applied-future26'
helper = BASE / 'finalize_applied26_reviewed_offer_v1.py'
record = BASE / 'applied26-reviewed-offer-finalization-actual-v1.json'
log = record.with_suffix('.log')
assert not record.exists() and not log.exists()
cmd = ['python3', str(helper.relative_to(ROOT))]
start = datetime.now(timezone.utc).isoformat(); t = time.monotonic()
with log.open('xb') as f:
    result = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
out = {'actual_command': cmd, 'working_directory': str(ROOT), 'actual_exit_code': result.returncode,
       'started_at_utc': start, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
       'duration_seconds': time.monotonic()-t, 'raw_log': str(log.relative_to(ROOT)),
       'raw_log_sha256': H(log), 'helper_sha256': H(helper),
       'scope': 'Actual isolated offer finalization/exact peer byte copies only. Own then-open finalizer JSON/log deliberately excluded from the offer; no live owner/compiler/PUB/Git mutation.'}
record.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out)); print(log.read_text()[-4000:]); raise SystemExit(result.returncode)
