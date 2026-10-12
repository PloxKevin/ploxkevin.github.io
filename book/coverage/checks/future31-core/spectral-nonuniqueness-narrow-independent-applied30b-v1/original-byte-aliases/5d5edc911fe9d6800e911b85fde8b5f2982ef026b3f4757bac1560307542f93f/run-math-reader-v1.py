from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
P=Path('/tmp/applied31b-spectral11-reviews-v1');helper=P/'independent-spectral11-math-reader-v1.py';log=P/'math-reader-actual-v1.log';record=P/'math-reader-actual-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not log.exists() and not record.exists();before=sha(helper);cmd=['python3',str(helper)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(cmd,cwd='/home/oxrexkevin/SafetyBased',stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();after=sha(helper)
d={'status':'passed_actual_read_only_independent_reader' if r.returncode==0 and before==after else 'failed_actual_independent_reader','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':{str(helper):before},'helper_sha256_after':{str(helper):after},'raw_log':str(log),'raw_log_sha256':sha(log),'producer_or_compiler_invoked':False}
with record.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(r.returncode if before==after else 1)
