from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,time,subprocess
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/check-module25-final-candidate-independent-applied-v1.py');log=Path('/tmp/module25-final-candidate-independent-applied-actual-v1.log');record=Path('/tmp/module25-final-candidate-independent-applied-actual-v1.json');assert not log.exists() and not record.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(['python3',str(helper)],cwd=root,stdout=f,stderr=subprocess.STDOUT)
out={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':['python3',str(helper)],'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(helper),'raw_log':str(log),'raw_log_sha256':sha(log)}
with record.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));raise SystemExit(r.returncode)
