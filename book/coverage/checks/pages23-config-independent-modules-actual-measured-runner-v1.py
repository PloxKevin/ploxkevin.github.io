from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
helper=Path(sys.argv[1]);stem=Path(sys.argv[2]);root=Path('/home/oxrexkevin/SafetyBased');h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();command=['python3',str(helper)]+sys.argv[3:]
record=stem.with_suffix('.json');log=stem.with_suffix('.log');assert not record.exists() and not log.exists();before=h(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as out:r=subprocess.run(command,cwd=root,stdout=out,stderr=subprocess.STDOUT)
row={'actual_command':command,'actual_workdir':str(root),'actual_exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'actual_checker_sha256_before':before,'actual_checker_sha256_after':h(helper),'log':str(log),'log_sha256':h(log),'scope':'Actual independent read-only review checker execution; no reviewed production helper was executed.'};record.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'actual_exit_code':r.returncode,'record':str(record),'record_sha256':h(record),'log':str(log),'log_sha256':h(log)}));sys.exit(r.returncode)
