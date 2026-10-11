from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
h=Path('/tmp/check-root-source53-writer-v2-independent-applied-v1.py')
p=Path('/tmp/root-source53-writer-v2-independent-applied-actual-v1.json');log=p.with_suffix('.log')
assert not p.exists()and not log.exists();cmd=['python3',str(h)];s=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd='/home/oxrexkevin/SafetyBased',stdout=f,stderr=subprocess.STDOUT)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d={'actual_command':cmd,'working_directory':'/home/oxrexkevin/SafetyBased','actual_exit_code':r.returncode,'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log),'raw_log_sha256':H(log),'helper_sha256':H(h),'scope':'Independent code/read-only guards and isolated parser only; no Root producer/source/PUB/Git execution.'}
p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text()[-2400:]);raise SystemExit(r.returncode)
