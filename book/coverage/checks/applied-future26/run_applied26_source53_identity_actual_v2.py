from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path(__file__).resolve().parents[4];B=R/'book/coverage/checks/applied-future26/source53-v2';B.mkdir(parents=True,exist_ok=True)
p=B/'source53-identity-preparation-actual-v2.json';log=p.with_suffix('.log');assert not p.exists()and not log.exists()
helper='book/coverage/checks/applied-future26/prepare_applied26_source53_identity_v2.py';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=['python3',helper,'--root-authorized-source53-identity-rebase','--inventory-sha256','4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'];before=H(R/helper);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
p.write_text(json.dumps({'actual_command':cmd,'working_directory':str(R),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log.relative_to(R)),'raw_log_sha256':H(log),'helper_sha256_before':before,'helper_sha256_after':H(R/helper),'scope':'Actual isolated identity preparation only; no live ledger, HTML, proof, aggregate or compiler mutation.'},indent=2)+'\n');print(p.read_text());print(log.read_text()[-3000:]);raise SystemExit(r.returncode)
