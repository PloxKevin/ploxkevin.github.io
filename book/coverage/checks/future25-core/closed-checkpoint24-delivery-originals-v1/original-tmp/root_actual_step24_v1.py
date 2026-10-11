from pathlib import Path
from datetime import datetime,timezone
import sys,json,subprocess,time,hashlib
root=Path('/home/oxrexkevin/SafetyBased')
name=sys.argv[1];command=json.loads(sys.argv[2]);helpers=json.loads(sys.argv[3]) if len(sys.argv)>3 else []
assert isinstance(command,list) and all(isinstance(x,str) for x in command)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
record=root/name;log=record.with_suffix('.log');assert not record.exists() and not log.exists()
record.parent.mkdir(parents=True,exist_ok=True)
before={n:sha(root/n) for n in helpers};started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('wb') as f:r=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
after={n:sha(root/n) for n in helpers};passed=r.returncode==0 and before==after
result=dict(status='passed' if passed else 'failed',actual_exit_code=r.returncode,actual_command=command,actual_workdir=str(root),started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-tick,helper_sha256_before=before,helper_sha256_after=after,log=str(log.relative_to(root)),log_sha256=sha(log))
baseline=root/'reports/full-coverage/checkpoint-23-selection.json'
result['baseline_selection']={'file':str(baseline.relative_to(root)),'sha256':sha(baseline)}
sel=root/'reports/full-coverage/checkpoint-24-selection.json'
if sel.exists():result['selection_sha256']=sha(sel)
record.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(0 if passed else 1)
