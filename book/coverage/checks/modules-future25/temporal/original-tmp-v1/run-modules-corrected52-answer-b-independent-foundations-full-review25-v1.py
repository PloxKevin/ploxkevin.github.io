from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-modules-corrected52-answer-b-independent-foundations-full-review25-v1.py');O=Path('/tmp/modules-corrected52-answer-b-independent-foundations-full-review25-actual-v1.json');L=O.with_suffix('.log')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)];a=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with L.open('xb')as f:f.write(a.stdout)
with O.open('x')as f:f.write(json.dumps({'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Genuine read-only independent full-literal semantic identity checker; no compiler, live ledger, source HTML or canonical mutation.'},indent=2)+'\n')
print(a.stdout.decode());print(json.dumps({'actual_execution':str(O),'sha256':H(O),'exit_code':a.returncode}));raise SystemExit(a.returncode)
