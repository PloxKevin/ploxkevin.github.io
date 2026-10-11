from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[5]
BASE=ROOT/'book/coverage/checks/modules-future25/source52'
HELPER='book/coverage/build_modules25_candidate_source52_v1.py'
BINDING='book/coverage/checks/modules-future25/temporal/original-canonical-binding-peer-v1/modules-temporal25-canonical-name-body-and-pair-independent-foundations-binding-v1.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=BASE/'module25-candidate-builder-actual-execution-v1.json';log=record.with_suffix('.log');assert not record.exists() and not log.exists()
cmd=['python',HELPER,BINDING];before=H(ROOT/HELPER);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
body={'execution_kind':'actual_isolated_Module25_candidate_construction','scope':'Genuine isolated review mapping construction only; no Lean compilation, live owner installation, global validator or aggregate audit.','actual_command':cmd,'working_directory':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'actual_exit_code':r.returncode,'helper':HELPER,'helper_sha256_before':before,'helper_sha256_after':H(ROOT/HELPER),'raw_log':str(log.relative_to(ROOT)),'raw_log_sha256':H(log),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__))}
record.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps(body));raise SystemExit(r.returncode)
