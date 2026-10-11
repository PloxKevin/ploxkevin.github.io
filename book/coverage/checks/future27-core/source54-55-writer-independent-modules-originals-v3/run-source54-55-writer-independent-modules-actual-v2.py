from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-source54-55-writer-independent-modules-v2.py');record=Path('/tmp/source54-55-writer-independent-modules-actual-v2.json');log=record.with_suffix('.log')
assert not record.exists() and not log.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python',str(checker)]
with log.open('xb') as f:r=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
d={'status':'actual_read_only_independent_checker_completed','actual_command':command,'working_directory':str(root),'started_at_utc':start,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tick,'actual_exit_code':r.returncode,'checker':{'file':str(checker),'sha256':sha(checker)},'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'log':str(log),'log_sha256':sha(log),'scope':'Read-only independent writer/helper/parser review. Production write_new replaced by explicit first-write sentinel; no Root application executed.'}
with record.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(r.returncode)
