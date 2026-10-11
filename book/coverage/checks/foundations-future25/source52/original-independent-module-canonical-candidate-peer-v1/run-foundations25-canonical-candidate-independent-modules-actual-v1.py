from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-foundations25-canonical-and-candidate-independent-modules-v1.py');record=Path('/tmp/foundations25-canonical-candidate-independent-modules-actual-v1.json');log=record.with_suffix('.log');assert not record.exists() and not log.exists()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=h(checker);cmd=['python',str(checker)];t=time.monotonic();start=datetime.now(timezone.utc).isoformat()
with log.open('wb') as f:r=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
b={'execution_kind':'actual_independent_read_only_canonical_binding_and_isolated_candidate_mechanics','actual_command':cmd,'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_exit_code':r.returncode,'helper_sha256_before':before,'helper_sha256_after':h(checker),'raw_log':str(log),'raw_log_sha256':h(log),'actual_runner':__file__,'actual_runner_sha256':h(Path(__file__))};record.write_text(json.dumps(b,indent=2)+'\n');print(json.dumps(b));raise SystemExit(r.returncode)
