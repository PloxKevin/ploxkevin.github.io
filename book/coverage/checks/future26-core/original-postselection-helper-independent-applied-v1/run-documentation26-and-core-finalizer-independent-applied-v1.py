from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/check-documentation26-and-core-finalizer-independent-applied-v1.py');p=Path('/tmp/documentation26-and-core-finalizer-independent-applied-actual-v1.json');log=p.with_suffix('.log');assert not p.exists() and not log.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=['python3',str(helper)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
p.write_text(json.dumps({'actual_command':cmd,'working_directory':str(root),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log),'raw_log_sha256':H(log),'helper_sha256':H(helper),'scope':'Actual full-code/delta and isolated guard-fixture checker for three unexecuted postselection26 helpers; no production helper, compiler, owner or publication writes.'},indent=2)+'\n');print(p.read_text());print(log.read_text());raise SystemExit(r.returncode)
