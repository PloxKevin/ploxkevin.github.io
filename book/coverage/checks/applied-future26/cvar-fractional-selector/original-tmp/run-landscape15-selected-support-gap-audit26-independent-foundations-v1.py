from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-landscape15-selected-support-gap-audit26-independent-foundations-v1.py');O=Path('/tmp/landscape15-selected-support-gap-audit26-independent-foundations-actual-v1.json');L=O.with_suffix('.log')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();assert not O.exists()and not L.exists();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only source and selected-evidence checker, no Lean compiler or live/candidate mutation.'}
with O.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(p.returncode)
