from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=Path(sys.argv[1]);stem=Path(sys.argv[2]);out=stem.with_suffix('.json');log=stem.with_suffix('.log');assert not out.exists() and not log.exists()
cmd=['python3',str(p)]+sys.argv[3:];before=H(p);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'actual_command':cmd,'actual_workdir':str(R),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'actual_helper_sha256_before':before,'actual_helper_sha256_after':H(p),'raw_log':str(log),'raw_log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'execution_kind':'actual_read_only_independent_pages25_config_code_or_output_review','scope':'Genuine independent reader execution only. No producer, Lean compile, audit, staging, deployment or live result is inferred.'}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'record':str(out),'actual_exit_code':r.returncode,'sha256':H(out),'raw_log_sha256':H(log)}));sys.exit(r.returncode)
