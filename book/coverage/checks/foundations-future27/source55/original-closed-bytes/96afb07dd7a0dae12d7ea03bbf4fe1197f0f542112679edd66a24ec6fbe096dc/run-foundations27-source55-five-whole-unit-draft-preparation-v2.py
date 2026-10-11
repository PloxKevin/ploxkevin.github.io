from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
root=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/prepare-foundations27-source55-five-whole-unit-draft-v2.py')
out=Path('/tmp/foundations27-source55-five-whole-unit-draft-preparation-actual-v2.json');log=out.with_suffix('.log')
assert not out.exists() and not log.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();before=sha(helper)
with log.open('xb') as f:r=subprocess.run(['python3',str(helper)],cwd=root,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':['python3',str(helper)],
 'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(helper),
 'log':str(log),'log_sha256':sha(log),'scope':'Actual TMP-only semantic mapping draft and unexecuted canonical plan preparation; no Root canonical/owner/source/PUB/Git or compiler mutation.'}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));raise SystemExit(r.returncode)
