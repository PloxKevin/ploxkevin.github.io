from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[4];B=ROOT/'book/coverage/checks/applied-future26';p=B/'scalar-scenario-canonical-source-preparation-actual-v2.json';log=p.with_suffix('.log');assert not p.exists()and not log.exists();helper=B/'prepare_scalar_scenario_canonical_sources_v2.py';cmd=['python3',str(helper.relative_to(ROOT))];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();d={'actual_command':cmd,'working_directory':str(ROOT),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-t,'raw_log':str(log.relative_to(ROOT)),'raw_log_sha256':H(log),'helper_sha256':H(helper),'scope':'Actual canonical exactsource/history metadata preparation only; no compiler/live owner/PUB mutation.'};p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());raise SystemExit(r.returncode)
