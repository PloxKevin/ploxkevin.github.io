from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-core24-material-candidate-independent-applied-v1.py');prefix=Path('/tmp/core24-material-candidate-independent-applied-actual-v1');log=prefix.with_suffix('.log');record=prefix.with_suffix('.json');assert not log.exists() and not record.exists()
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cmd=['python3',str(checker)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic();before=h(checker)
with log.open('wb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record.write_text(json.dumps({'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker_sha256_before':before,'checker_sha256_after':h(checker),'log':str(log),'log_sha256':h(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':h(__file__),'scope':'Actual independent Python mechanics reader only; no candidate-builder/compiler/Git/PUB/live owner execution.'},indent=2)+'\n');print(log.read_text());print(record,h(record));raise SystemExit(r.returncode)
