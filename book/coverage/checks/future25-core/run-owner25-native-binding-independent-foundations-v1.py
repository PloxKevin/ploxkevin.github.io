from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
CHECK=BASE/'check-owner25-native-binding-independent-foundations-v1.py'
ACT=BASE/'owner25-native-binding-independent-foundations-actual-v1.json'
LOG=ACT.with_suffix('.log')
assert not ACT.exists() and not LOG.exists()
before=H(CHECK)
start=datetime.now(timezone.utc).isoformat()
t=time.monotonic()
cmd=['python3',str(CHECK)]
with LOG.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed'if p.returncode==0 else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':H(CHECK),'log':str(LOG.relative_to(ROOT)),'log_sha256':H(LOG),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only output checker invocation. No Root integration/production writer, Lean/kernel or publication execution.'}
ACT.write_text(json.dumps(record,indent=2)+'\n')
print(LOG.read_text())
print(str(ACT.relative_to(ROOT)),H(ACT))
raise SystemExit(p.returncode)
