from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
SCRIPT=Path('/tmp/close-delivery5-and-gradient15-originals28-v1.py')
ACTUAL=Path('/tmp/delivery5-gradient15-original-evidence-closure28-actual-v1.json')
LOG=ACTUAL.with_suffix('.log')
assert not ACTUAL.exists() and not LOG.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();before=sha(SCRIPT);cmd=['python3',str(SCRIPT)]
with LOG.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
actual={'actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(SCRIPT),'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':{'file':__file__,'sha256':sha(__file__)}}
ACTUAL.write_text(json.dumps(actual,indent=2)+'\n')
print(json.dumps(actual));print(LOG.read_text())
raise SystemExit(r.returncode)
