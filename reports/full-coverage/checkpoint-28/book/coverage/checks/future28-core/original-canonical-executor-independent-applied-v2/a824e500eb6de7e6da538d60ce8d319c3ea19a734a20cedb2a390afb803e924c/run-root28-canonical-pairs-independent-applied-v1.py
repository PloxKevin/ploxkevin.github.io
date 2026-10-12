from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');CHECK=Path('/tmp/check-root28-canonical-pairs-independent-applied-v1.py');REC=Path('/tmp/root28-canonical-pairs-independent-applied-actual-v1.json');LOG=REC.with_suffix('.log');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not REC.exists()and not LOG.exists();tick=time.monotonic();start=datetime.now(timezone.utc).isoformat();before=H(CHECK)
with LOG.open('xb')as f:r=subprocess.run([sys.executable,str(CHECK)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
out={'status':'passed_actual_readonly_checker'if r.returncode==0 else'failed_actual_readonly_checker','actual_exit_code':r.returncode,'actual_command':[sys.executable,str(CHECK)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':{str(CHECK):before},'helper_sha256_after':{str(CHECK):H(CHECK)},'log':str(LOG),'log_sha256':H(LOG),'producer_apply':False,'compiler_run':False}
REC.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));sys.exit(r.returncode)
