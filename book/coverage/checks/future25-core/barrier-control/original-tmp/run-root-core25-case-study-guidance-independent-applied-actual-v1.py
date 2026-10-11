from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='/tmp/check-root-core25-case-study-guidance-independent-applied-v1.py'
PIN='a0b5ab4207bc01ca627a2faedb78542923292b7e81cdfcba99c1c5ed7138d2af'
BASE=Path('/tmp')
BASE.mkdir(parents=True,exist_ok=True)
OUT=BASE/'root-core25-case-study-guidance-independent-applied-actual-v1.json'
LOG=OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(ROOT/HELPER)==PIN
cmd=['python3',HELPER]
start=datetime.now(timezone.utc);t=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc)
d={'status':'passed' if p.returncode==0 else 'failed','actual_exit_code':p.returncode,'command':cmd,'actual_workdir':str(ROOT),
 'helper_sha256_before':PIN,'helper_sha256_after':sha(ROOT/HELPER),'log':str(LOG),
 'log_sha256':sha(LOG),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(__file__),
 'started_at_utc':start.isoformat(),'finished_at_utc':finish.isoformat(),'elapsed_seconds':time.monotonic()-t,
 'scope':'Actual independent full case-study five-literal/context classification and exact identity checker; no Lean run, live owner edit or aggregate claim.'}
with OUT.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'actual_record':str(OUT),'sha256':sha(OUT),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}))
raise SystemExit(p.returncode)
