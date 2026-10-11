from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
checker=Path('/tmp/check-applied-joint-density371-fifteen-bodies-independent-foundations-v2.py')
actual=Path('/tmp/applied-joint-density371-independent-foundations-actual25-v2.json')
log=actual.with_suffix('.log')
assert not actual.exists() and not log.exists()
before=H(checker)
start=datetime.now(timezone.utc).isoformat()
t=time.monotonic()
cmd=['python3',str(checker)]
with log.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed'if p.returncode==0 else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':H(checker),'log':str(log),'log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual independent read-only literal/body/evidence checker; no Lean, canonical/named, owner installation or publication execution.'}
actual.write_text(json.dumps(d,indent=2)+'\n')
print(log.read_text())
print(str(actual),H(actual))
raise SystemExit(p.returncode)
