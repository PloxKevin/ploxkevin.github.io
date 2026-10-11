from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-applied25-canonical-binding-and-candidate-independent-foundations-v3.py');O=Path('/tmp/applied25-canonical-binding-and-candidate-independent-foundations-actual-v3.json');L=O.with_suffix('.log')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert not O.exists()and not L.exists();start=datetime.now(timezone.utc).isoformat();t=time.monotonic();before=H(C);cmd=['python3',str(C)]
with L.open('xb')as f:a=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':H(C),'raw_log':str(L),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only independent canonical-original binding and isolated candidate mechanical checker only; no compiler, owner installer, selector, Git or publication helper execution.'}
with O.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(a.returncode)
