from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/future24-core/owner24-integration-v2-independent-foundations-code-check-v1.py';OUT=ROOT/'book/coverage/checks/future24-core/owner24-integration-v2-independent-foundations-code-actual-v1.json';LOG=OUT.with_suffix('.log');assert not OUT.exists()and not LOG.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();before=H(HELPER);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(HELPER)]
r=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);LOG.write_bytes(r.stdout)
OUT.write_text(json.dumps({'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':before,'actual_checker_sha256_after':H(HELPER),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':H(LOG),'scope':'Genuine independent read-only integration24 helper code and focused schema fixtures; no Root integration main/dry/apply or compiler rerun.'},indent=2)+'\n')
print(r.stdout.decode());print(OUT.read_text());raise SystemExit(r.returncode)
