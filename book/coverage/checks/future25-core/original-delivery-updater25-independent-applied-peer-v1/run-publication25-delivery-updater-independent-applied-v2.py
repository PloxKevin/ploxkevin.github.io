from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
out=Path('/tmp/publication25-delivery-updater-independent-applied-actual-v2.json');log=out.with_suffix('.log')
assert not out.exists() and not log.exists()
cmd=['python3','/tmp/check-publication25-delivery-updater-independent-applied-v2.py']
cwd='/home/oxrexkevin/SafetyBased';started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d={'actual_command':cmd,'working_directory':cwd,'actual_exit_code':r.returncode,
 'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tick,
 'raw_log':str(log),'raw_log_sha256':H(log),'checker_sha256':H(cmd[1]),
 'scope':'Measured read-only code review with synthetic-schema fixtures in isolated temporary roots; no production metadata or PUB mutation.'}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());raise SystemExit(r.returncode)
