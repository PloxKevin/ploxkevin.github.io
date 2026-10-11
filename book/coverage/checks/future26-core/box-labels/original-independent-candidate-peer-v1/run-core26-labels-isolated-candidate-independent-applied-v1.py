from pathlib import Path
from datetime import datetime,timezone
import json,time,subprocess,hashlib
root='/home/oxrexkevin/SafetyBased';stem=Path('/tmp/core26-labels-isolated-candidate-independent-applied-actual-v1');log=stem.with_suffix('.log');rec=stem.with_suffix('.json');assert not rec.exists() and not log.exists();cmd=['python3','/tmp/check-core26-labels-isolated-candidate-independent-applied-v1.py'];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:p=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
r={'command':cmd,'working_directory':root,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'actual_exit_code':p.returncode,'log':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'scope':'Measured independent mechanical checker; no production/helper/Lean execution.'};rec.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));print(log.read_text());raise SystemExit(p.returncode)
