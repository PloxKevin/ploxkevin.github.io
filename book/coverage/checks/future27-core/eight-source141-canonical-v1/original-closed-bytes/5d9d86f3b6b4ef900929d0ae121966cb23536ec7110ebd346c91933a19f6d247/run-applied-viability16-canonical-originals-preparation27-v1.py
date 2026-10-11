from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');p=Path('/tmp/prepare-applied-viability16-canonical-originals27-v1.py');out=Path('/tmp/applied-viability16-canonical-originals-preparation-actual27-v1.json');log=out.with_suffix('.log');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();assert not out.exists() and not log.exists()
start=datetime.now(timezone.utc).isoformat();t=time.monotonic();h=H(p)
with log.open('xb')as f:r=subprocess.run(['python3',str(p)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
out.write_text(json.dumps({'status':'actual_tmp_only_viability16_source_history_preparation','actual_exit_code':r.returncode,'actual_command':['python3',str(p)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':h,'helper_sha256_after':H(p),'raw_log':str(log),'raw_log_sha256':H(log),'scope':'TMP-only source/original-history preparation; no canonical source, owner, HTML, inventory, PUB/Git, compiler or current26 edit.'},indent=2)+'\n');print(json.dumps({'actual':str(out),'sha256':H(out),'actual_exit_code':r.returncode,'log':str(log),'log_sha256':H(log)}));raise SystemExit(r.returncode)
