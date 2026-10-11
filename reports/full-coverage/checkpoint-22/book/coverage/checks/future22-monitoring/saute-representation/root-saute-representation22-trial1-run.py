from pathlib import Path
import subprocess,time,json,hashlib
from datetime import datetime,timezone
p=Path('/tmp/root-saute-representation22-trial1.lean');log=p.with_suffix('.log');out=p.with_suffix('.json');assert not log.exists() and not out.exists()
cmd=['lake','env','lean',str(p)];t=time.monotonic();started=datetime.now(timezone.utc).isoformat()
with log.open('wb') as f:r=subprocess.run(cmd,cwd='/home/oxrexkevin/SafetyBased/verification/lean',stdout=f,stderr=subprocess.STDOUT)
out.write_text(json.dumps(dict(command=cmd,started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-t,exit_code=r.returncode,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()),indent=2)+'\n')
print(log.read_text());raise SystemExit(r.returncode)
