from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[5];B=ROOT/'book/coverage/checks/applied-future26/changed-optimizer-support'
helper=B/'run_support5_canonical_pair_source53_v2.py';record=B/'support5-canonical-pair-actual-v2.json';log=record.with_suffix('.log')
assert not record.exists() and not log.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
command=['python3',str(helper.relative_to(ROOT))];before=H(helper);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as stream:result=subprocess.run(command,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
out={'actual_command':command,'working_directory':str(ROOT),'actual_exit_code':result.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tick,'raw_log':str(log.relative_to(ROOT)),'raw_log_sha256':H(log),'helper_sha256_before':before,'helper_sha256_after':H(helper),'scope':'Actual guarded serial canonical support5 standalone/named commands; no aggregate or live owner/HTML writes.'}
with record.open('x') as stream:stream.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));print(log.read_text()[-4000:]);raise SystemExit(result.returncode)
