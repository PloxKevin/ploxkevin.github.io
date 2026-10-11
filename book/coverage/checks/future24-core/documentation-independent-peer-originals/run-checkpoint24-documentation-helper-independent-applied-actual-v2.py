from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='/tmp/check-checkpoint24-documentation-independent-applied-v2.py'
PIN='2778ed4e33e1f95ec8b26a7f96bc66a99b38a40364e352624c0adfe9beaaed4b'
BASE=Path('/tmp')
BASE.mkdir(parents=True,exist_ok=True)
OUT=BASE/'checkpoint24-documentation-helper-independent-applied-actual-v2.json'
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
 'scope':'Actual independent read-only documentation code/AST/context checker. The Root documentation helper is not executed and no metadata/live/aggregate24 claim is made.'}
with OUT.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'actual_record':str(OUT),'sha256':sha(OUT),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}))
raise SystemExit(p.returncode)
