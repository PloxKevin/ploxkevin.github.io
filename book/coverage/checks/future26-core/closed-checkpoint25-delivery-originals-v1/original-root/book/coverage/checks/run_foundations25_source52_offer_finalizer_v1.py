from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[3];HELPER=ROOT/'book/coverage/finalize_foundations25_source52_offer_v1.py';BASE=ROOT/'book/coverage/checks/foundations-future25/source52';OUT=BASE/'offer-finalizer-actual-execution-source52-v1.json';LOG=OUT.with_suffix('.log')
assert not OUT.exists()and not LOG.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();before=H(HELPER);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(HELPER)]
with LOG.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
with OUT.open('x')as f:json.dump({'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_helper':str(HELPER.relative_to(ROOT)),'actual_helper_sha256_before':before,'actual_helper_sha256_after':H(HELPER),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'raw_log':str(LOG.relative_to(ROOT)),'raw_log_sha256':H(LOG),'scope':'Genuine isolated offer finalization only; no compiler, live installation, selection or publication execution.'},f,indent=2);f.write('\n')
print(LOG.read_text());print(OUT.read_text());raise SystemExit(r.returncode)
