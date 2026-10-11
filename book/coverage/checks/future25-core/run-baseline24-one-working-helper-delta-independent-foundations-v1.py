from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
checker=BASE/'check-baseline24-one-working-helper-delta-independent-foundations-v1.py'
actual=BASE/'baseline24-one-working-helper-delta-independent-foundations-actual-v1.json'
log=actual.with_suffix('.log')
assert not actual.exists() and not log.exists()
before=H(checker)
start=datetime.now(timezone.utc).isoformat()
t=time.monotonic()
cmd=['python3',str(checker)]
with log.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed'if p.returncode==0 else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':H(checker),'log':str(log.relative_to(ROOT)),'log_sha256':H(log),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only helper delta/source/evidence checker; no original helper/Lean or Root production integration execution.'}
actual.write_text(json.dumps(d,indent=2)+'\n')
print(log.read_text())
print(str(actual.relative_to(ROOT)),H(actual))
raise SystemExit(p.returncode)
