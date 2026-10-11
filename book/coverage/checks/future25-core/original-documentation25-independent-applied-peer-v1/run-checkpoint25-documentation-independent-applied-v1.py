from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
p=Path('/tmp/checkpoint25-documentation-independent-applied-actual-v1.json');log=p.with_suffix('.log')
assert not p.exists() and not log.exists()
cmd=['python3','/tmp/check-checkpoint25-documentation-independent-applied-v1.py']
cwd='/home/oxrexkevin/SafetyBased';started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
H=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
d={'actual_command':cmd,'working_directory':cwd,'actual_exit_code':r.returncode,
 'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tick,
 'raw_log':str(log),'raw_log_sha256':H(log),'checker_sha256':H(cmd[1]),
 'scope':'Actual read-only independent checker; production-schema simulations run only in isolated temporary roots, not on live owner metadata or PUB.'}
p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());raise SystemExit(r.returncode)
