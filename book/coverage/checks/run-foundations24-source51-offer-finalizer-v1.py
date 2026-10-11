from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[3];HELPER=ROOT/'book/coverage/finalize_foundations24_source51_offer_v1.py';BASE=ROOT/'book/coverage/checks/foundations-future24/source51';OUT=BASE/'offer-finalizer-actual-execution-source51-v1.json';LOG=OUT.with_suffix('.log')
assert not OUT.exists()and not LOG.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();before=H(HELPER);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(HELPER)]
r=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);LOG.write_bytes(r.stdout)
OUT.write_text(json.dumps({'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_helper':str(HELPER.relative_to(ROOT)),'actual_helper_sha256_before':before,'actual_helper_sha256_after':H(HELPER),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'raw_log':str(LOG.relative_to(ROOT)),'raw_log_sha256':H(LOG),'scope':'Genuine isolated offer evidence finalization only; no compiler, live installation, selection or publication execution.'},indent=2)+'\n')
print(r.stdout.decode());print(OUT.read_text());raise SystemExit(r.returncode)
