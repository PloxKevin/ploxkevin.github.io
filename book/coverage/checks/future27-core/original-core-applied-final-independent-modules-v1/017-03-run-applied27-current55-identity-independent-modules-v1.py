from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/check-applied27-current55-identity-independent-modules-v1.py');record=Path('/tmp/applied27-current55-identity-independent-modules-actual-v1.json');log=record.with_suffix('.log');assert not record.exists() and not log.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python',str(helper)]
with log.open('xb') as f:p=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
d={'status':'actual_read_only_independent_identity_checker_completed','actual_command':command,'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':p.returncode,'checker':{'file':str(helper),'sha256':sha(helper)},'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(log),'raw_log_sha256':sha(log),'scope':'Independent read-only identity mechanics only; no producer/compiler/canonical/live writes.'}
with record.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(p.returncode)
