from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');helper=ROOT/'book/coverage/checks/applied-future24/build_applied24_material_candidate_v1.py';prefix=ROOT/'book/coverage/checks/applied-future24/applied24-isolated-material-candidate-actual-v1';record=prefix.with_suffix('.json');log=prefix.with_suffix('.log');assert not record.exists() and not log.exists()
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cmd=['python3',str(helper.relative_to(ROOT))];start=datetime.now(timezone.utc).isoformat();t=time.monotonic();before=H(helper)
with log.open('wb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record.write_text(json.dumps({'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':H(helper),'log':str(log.relative_to(ROOT)),'log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(__file__),'scope':'Actual isolated future24 candidate creation only. Live owner mutation, global24 validation, aggregate audit and publication remain separate.'},indent=2)+'\n');print(log.read_text());print(record.relative_to(ROOT),H(record));raise SystemExit(r.returncode)
