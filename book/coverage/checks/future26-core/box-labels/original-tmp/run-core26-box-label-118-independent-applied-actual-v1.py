from pathlib import Path
import subprocess,json,hashlib,time
from datetime import datetime,timezone
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/check-core26-box-label-118-independent-applied-v1.py');log=Path('/tmp/core26-box-label-118-independent-applied-actual-v1.log');record=Path('/tmp/core26-box-label-118-independent-applied-actual-v1.json')
assert not log.exists() and not record.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:result=subprocess.run(['python3',str(helper)],cwd=root,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat()
out={'status':'passed' if result.returncode==0 else 'failed','actual_exit_code':result.returncode,'actual_command':['python3',str(helper)],'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(helper),'raw_log':str(log),'raw_log_sha256':sha(log)}
with record.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));raise SystemExit(result.returncode)
