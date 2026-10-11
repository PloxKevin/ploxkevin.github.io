from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
P=Path('/tmp/prepare-foundations-literal-partial7-full-review28-v3.py')
OUT=Path('/tmp/foundations-literal-partial7-packaging-actual-v3.json');LOG=OUT.with_suffix('.log')
assert not OUT.exists()and not LOG.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
before=sha(P);cmd=['python3',str(P)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
a={'actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(P),'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':{'file':__file__,'sha256':sha(Path(__file__))}}
OUT.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(a));print(LOG.read_text());raise SystemExit(r.returncode)
