from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-landscape15-source52-twelve-new-bodies-whole-review26-independent-foundations-v1.py');A=Path('/tmp/landscape15-source52-whole-review26-independent-foundations-actual-v1.json');L=A.with_suffix('.log');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not A.exists()and not L.exists();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
a={'status':'passed'if p.returncode==0 else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':h,'checker_sha256_after':H(C),'raw_log':str(L),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only semantic/source/evidence checker, no compiler or Root production execution.'};A.write_text(json.dumps(a,indent=2)+'\n');print(L.read_text());print(str(A),H(A));raise SystemExit(p.returncode)
