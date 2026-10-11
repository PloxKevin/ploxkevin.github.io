from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-publication26-delivery-updater-v3-new-native-guards-applied-v1.py');P=Path('/tmp/publication26-delivery-updater-v3-native-observation-applied-actual-v1.json');L=P.with_suffix('.log');assert not P.exists() and not L.exists();H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();cmd=['python3',str(C)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb')as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
P.write_text(json.dumps({'actual_command':cmd,'working_directory':str(R),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'raw_log':str(L),'raw_log_sha256':H(L),'checker_sha256':H(C),'scope':'Measured read-only isolated diagnostic fixtures; observation requires changes, not updater approval; no producer/PUB/Git/metadata writes.'},indent=2)+'\n');print(P.read_text());print(L.read_text());raise SystemExit(r.returncode)
