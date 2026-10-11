from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-modules-temporal25-canonical-bindings-independent-foundations-v1.py')
O=Path('/tmp/modules-temporal25-canonical-binding-independent-foundations-actual-v1.json');L=O.with_suffix('.log')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
t=time.monotonic();s=datetime.now(timezone.utc).isoformat();before=h(C);cmd=['python3',str(C)]
with L.open('xb') as f:a=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if a.returncode==0 else 'failed','actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(R),
   'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,
   'checker_sha256_before':before,'checker_sha256_after':h(C),'raw_log':str(L),'raw_log_sha256':h(L),
   'actual_runner':str(Path(__file__)),'actual_runner_sha256':h(Path(__file__)),
   'scope':'Actual measured independent read-only canonical evidence binding checker; no compiler or owner writes.'}
with O.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(a.returncode)
