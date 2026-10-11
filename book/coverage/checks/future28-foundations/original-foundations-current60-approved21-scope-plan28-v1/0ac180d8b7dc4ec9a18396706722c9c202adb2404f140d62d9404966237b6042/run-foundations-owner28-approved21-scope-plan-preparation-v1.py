from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/prepare-foundations-owner28-approved21-scope-plan-v1.py');actual=Path('/tmp/foundations-owner28-approved21-scope-plan-preparation-actual-v1.json');log=actual.with_suffix('.log');assert not actual.exists()and not log.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cmd=['python3',str(helper)];before=sha(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
a={'actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(helper),'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(log),'raw_log_sha256':sha(log)}
with actual.open('x')as f:json.dump(a,f,indent=2);f.write('\n')
assert a['helper_sha256_before']==a['helper_sha256_after'];print(json.dumps(a));raise SystemExit(r.returncode)
