from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
root=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-publication26-two-stagers-independent-foundations-v2.py');out=Path('/tmp/publication26-two-stagers-independent-foundations-actual-v2.json');log=out.with_suffix('.log');assert not out.exists() and not log.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();before=sha(checker)
with log.open('xb') as f:r=subprocess.run(['python3',str(checker)],cwd=root,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':['python3',str(checker)],'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(checker),'log':str(log),'log_sha256':sha(log),'scope':'Actual independent publication code/native-schema read and isolated synthetic fixtures only; no production stage, PUB/Git/Pages or deployment execution.'}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));raise SystemExit(r.returncode)
