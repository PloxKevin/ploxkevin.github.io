from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
p=Path('/tmp/mpc-terminal-energy-convergence26-independent-applied-actual-v1.json');log=p.with_suffix('.log');assert not p.exists() and not log.exists();cmd=['python3','/tmp/check-mpc-terminal-energy-convergence26-independent-applied-v1.py'];cwd='/home/oxrexkevin/SafetyBased';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();d={'actual_command':cmd,'working_directory':cwd,'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log),'raw_log_sha256':H(log),'checker_sha256':H(cmd[1]),'scope':'Actual read-only three-new-body full proof/source/evidence checker only.'};p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());raise SystemExit(r.returncode)
