from pathlib import Path
import subprocess,json,hashlib,time
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
script=Path('/tmp/check-mpc-shift15-components-independent-foundations28-v1.py')
log=Path('/tmp/mpc-shift15-components-independent-foundations28-actual-v1.log')
record=Path('/tmp/mpc-shift15-components-independent-foundations28-actual-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not log.exists() and not record.exists()
start=datetime.now(timezone.utc).isoformat();tick=time.perf_counter()
command=['python3',str(script)]
with log.open('xb') as f:p=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
r={'actual_command':command,'actual_workdir':str(ROOT),'actual_exit_code':p.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.perf_counter()-tick,'script':{'file':str(script),'sha256':sha(script)},'raw_log':{'file':str(log),'sha256':sha(log)},'scope':'TMP-only independent semantic/native packet verification, no Lean or live parser or production mutation.'}
record.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));print(log.read_text());raise SystemExit(p.returncode)
