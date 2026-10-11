from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
p=Path('/tmp/checkpoint25-plan-closer-independent-applied-actual-v3.json');log=p.with_suffix('.log');assert not p.exists() and not log.exists()
cmd=['python3','/tmp/check-checkpoint25-plan-closer-independent-applied-v3.py'];cwd='/home/oxrexkevin/SafetyBased';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:r=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
h=lambda n:hashlib.sha256(Path(n).read_bytes()).hexdigest()
d={'actual_command':cmd,'working_directory':cwd,'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'log':str(log),'raw_log_sha256':h(log),'checker_sha256':h(cmd[1]),'scope':'Genuine independent read-only checker with explicitly synthetic isolated fixtures; no production helper or owner action.'};p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());raise SystemExit(r.returncode)
