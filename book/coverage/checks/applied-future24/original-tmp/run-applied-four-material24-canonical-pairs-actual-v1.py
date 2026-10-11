from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');helper=ROOT/'book/coverage/checks/applied-future24/run_four_material24_canonical_pairs_v1.py';prefix=ROOT/'book/coverage/checks/applied-future24/four-material24-canonical-pairs-actual-execution-v1';record=prefix.with_suffix('.json');log=prefix.with_suffix('.log');assert not record.exists() and not log.exists()
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cmd=['python3',str(helper.relative_to(ROOT))];start=datetime.now(timezone.utc).isoformat();t=time.monotonic();before=H(helper)
with log.open('wb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record.write_text(json.dumps({'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':H(helper),'log':str(log.relative_to(ROOT)),'log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(__file__),'scope':'Actual serialized new canonical future24 compiler pair runner. Aggregate24/kernel replay/selection/live owner amendment remain separate.'},indent=2)+'\n');print(log.read_text());print(record.relative_to(ROOT),H(record));raise SystemExit(r.returncode)
