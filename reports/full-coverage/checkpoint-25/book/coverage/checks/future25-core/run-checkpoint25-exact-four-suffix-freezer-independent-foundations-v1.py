from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future25-core';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
CHECK=BASE/'check-checkpoint25-exact-four-suffix-freezer-independent-foundations-v1.py';ACT=BASE/'checkpoint25-exact-four-suffix-freezer-independent-foundations-actual-v1.json';LOG=ACT.with_suffix('.log')
assert not ACT.exists()and not LOG.exists();before=H(CHECK);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(CHECK)]
with LOG.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
a={'status':'passed'if p.returncode==0 else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':H(CHECK),'log':str(LOG.relative_to(ROOT)),'log_sha256':H(LOG),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual independent read-only code and guard-fixture checker. No producer freeze or publication execution.'};ACT.write_text(json.dumps(a,indent=2)+'\n');print(LOG.read_text());print(H(ACT));raise SystemExit(p.returncode)
