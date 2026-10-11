"""Measure genuine isolated candidate/finalizer execution; do not infer Lean runs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=Path(sys.argv[1]);stem=Path(sys.argv[2]);record=stem.with_suffix('.json');log=stem.with_suffix('.log')
assert not record.exists() and not log.exists();record.parent.mkdir(parents=True,exist_ok=True)
cmd=['python3',str(helper)]+sys.argv[3:];before=H(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
row={'actual_command':cmd,'actual_workdir':str(R),'actual_exit_code':r.returncode,'started_at_utc':start,
 'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
 'actual_helper_sha256_before':before,'actual_helper_sha256_after':H(helper),'raw_log':str(log),
 'raw_log_sha256':H(log),'execution_kind':'actual_isolated_candidate_preparation',
 'scope':'Genuine isolated future24 candidate or immutable offer preparation. No live owner integration, source correction, Lean compilation or aggregate audit is claimed.'}
record.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'actual_exit_code':r.returncode,'record':str(record),'record_sha256':H(record),'raw_log':str(log),'raw_log_sha256':H(log)}));sys.exit(r.returncode)
