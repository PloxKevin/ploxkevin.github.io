from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
HELPER=ROOT/'book/coverage/build_foundations24_candidate_source52_identity_v1.py'
BASE=ROOT/'book/coverage/checks/foundations-future24/source52';BASE.mkdir(parents=True,exist_ok=True)
JSON=BASE/'identity-builder-actual-execution-source52-v1.json';LOG=BASE/'identity-builder-actual-execution-source52-v1.log'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not JSON.exists()and not LOG.exists()
command=['python3',str(HELPER),'--inventory-sha256','38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3','--root-authorized-source52-identity-rebase'];before=H(HELPER);started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat()
with LOG.open('xb')as f:f.write(r.stdout)
record={'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-t,'actual_helper':HELPER.relative_to(ROOT).as_posix(),'actual_helper_sha256_before':before,'actual_helper_sha256_after':H(HELPER),'actual_runner':Path(__file__).relative_to(ROOT).as_posix(),'actual_runner_sha256':H(Path(__file__)),'raw_log':LOG.relative_to(ROOT).as_posix(),'raw_log_sha256':H(LOG),'scope':'Actual isolated unchanged-literal inventory identity preparation only. Original source51 full semantic/proof bodies and times are retained; no compiler rerun, new mathematical decision or live installation.'}
with JSON.open('x')as f:f.write(json.dumps(record,indent=2)+'\n')
print(r.stdout.decode());print(json.dumps(record));raise SystemExit(r.returncode)
