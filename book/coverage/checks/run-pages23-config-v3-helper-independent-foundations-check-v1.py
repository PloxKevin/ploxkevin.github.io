from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
CHECK=ROOT/'book/coverage/checks/pages23-config-v3-helper-independent-foundations-check-v1.py'
JSON=ROOT/'book/coverage/checks/pages23-config-v3-helper-independent-foundations-actual-v1.json'
LOG=JSON.with_suffix('.log');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not JSON.exists()and not LOG.exists()
command=['python',str(CHECK)];before=H(CHECK);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat()
with LOG.open('xb')as f:f.write(r.stdout)
d={'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':time.monotonic()-t,'actual_checker':CHECK.relative_to(ROOT).as_posix(),'actual_checker_sha256_before':before,'actual_checker_sha256_after':H(CHECK),'actual_runner':Path(__file__).relative_to(ROOT).as_posix(),'actual_runner_sha256':H(Path(__file__)),'raw_log':LOG.relative_to(ROOT).as_posix(),'raw_log_sha256':H(LOG),'scope':'Genuine independent read-only code/prospective-budget checker execution; preparation helper not executed.'}
with JSON.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
print(r.stdout.decode());print(json.dumps(d));raise SystemExit(r.returncode)
