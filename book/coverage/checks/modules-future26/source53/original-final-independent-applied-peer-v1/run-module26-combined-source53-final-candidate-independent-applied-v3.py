from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/check-module26-combined-source53-final-candidate-independent-applied-v3.py');p=Path('/tmp/module26-combined-source53-final-candidate-independent-applied-actual-v3.json');log=p.with_suffix('.log');assert not p.exists()and not log.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=['python3',str(helper)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
p.write_text(json.dumps({'actual_command':cmd,'working_directory':str(root),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log),'raw_log_sha256':H(log),'helper_sha256':H(helper),'scope':'Measured read-only independent Module26 candidate mapping and evidence checks; no owner mutation.'},indent=2)+'\n');print(p.read_text());print(log.read_text()[-4000:]);raise SystemExit(r.returncode)
