from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path(__file__).resolve().parents[4];B=R/'book/coverage/checks/applied-future26/source53-v2';p=B/'reviewed-offer-finalization-actual-v2.json';log=p.with_suffix('.log');assert not p.exists()and not log.exists();helper='book/coverage/checks/applied-future26/finalize_applied26_source53_reviewed_offer_v2.py';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=['python3',helper];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
p.write_text(json.dumps({'actual_command':cmd,'working_directory':str(R),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log.relative_to(R)),'raw_log_sha256':H(log),'helper_sha256':H(R/helper),'scope':'Actual isolated reviewed-offer closure only. Its then-open own JSON/log are intentionally not hashed into the offer.'},indent=2)+'\n');print(p.read_text());print(log.read_text()[-3000:]);raise SystemExit(r.returncode)
