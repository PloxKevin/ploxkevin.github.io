from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,os,sys
R=Path('/home/oxrexkevin/SafetyBased');P=Path('/tmp/check-root-tmp27-runner4-independent-modules-v1.py');J=Path('/tmp/root-tmp27-runner4-independent-modules-actual-v1.json');L=J.with_suffix('.log');assert not J.exists() and not L.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=[sys.executable,str(P)];env=dict(os.environ);env.pop('PYTHONHOME',None);t=time.monotonic();s=datetime.now(timezone.utc).isoformat()
with L.open('xb') as f:p=subprocess.run(c,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
d={'status':'actual_read_only_independent_runner4_checker_completed','actual_command':c,'actual_workdir':str(R),'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_exit_code':p.returncode,'checker':{'file':str(P),'sha256':sha(P)},'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(L),'raw_log_sha256':sha(L),'scope':'Read-only code/native guard and explicit synthetic fixtures, no compiler or producer execution.'}
with J.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(p.returncode)
