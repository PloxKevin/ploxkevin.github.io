from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib
cwd=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/modules-tanh52-proposal-independent-foundations-check-v3.py');out=Path('/tmp/modules-tanh52-proposal-independent-foundations-actual-v3.json');log=out.with_suffix('.log')
assert not out.exists()and not log.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();before=H(checker);cmd=['python3',str(checker)]
r=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(r.stdout)
out.write_text(json.dumps({'actual_command':cmd,'actual_workdir':str(cwd),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'actual_exit_code':r.returncode,'actual_checker_sha256_before':before,'actual_checker_sha256_after':H(checker),'log':str(log),'log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__))},indent=2)+'\n')
print(r.stdout.decode());print(out.read_text());raise SystemExit(r.returncode)
