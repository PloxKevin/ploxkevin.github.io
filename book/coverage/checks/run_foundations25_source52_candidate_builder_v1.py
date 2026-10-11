"""Actual measured isolated Foundation25 candidate construction, no live write."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future25/source52';BASE.mkdir(parents=True,exist_ok=True)
H=ROOT/'book/coverage/build_foundations25_candidate_source52_v1.py'
OUT=BASE/'foundations25-isolated-candidate-builder-actual-execution-v1.json';LOG=OUT.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not LOG.exists()
cmd=['python3',H.relative_to(ROOT).as_posix()];before=sha(H);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:a=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if a.returncode==0 else 'failed','actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),
   'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
   'helper':H.relative_to(ROOT).as_posix(),'helper_sha256_before':before,'helper_sha256_after':sha(H),
   'log':LOG.relative_to(ROOT).as_posix(),'log_sha256':sha(LOG),'actual_runner':Path(__file__).relative_to(ROOT).as_posix(),
   'actual_runner_sha256':sha(Path(__file__)),
   'scope':'Genuine isolated future25 candidate builder only. No live24 owner, source HTML, inventory, selected/frozen24 or aggregate25 amendment.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(a.returncode)
