from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');HELP=Path('/tmp/check-owner28-installer-independent-applied-v2.py');REC=Path('/tmp/owner28-installer-independent-applied-actual-v2.json');LOG=REC.with_suffix('.log');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not REC.exists()and not LOG.exists();before=H(HELP);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb')as f:r=subprocess.run([sys.executable,str(HELP)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed_actual_independent_owner28_installer_reader'if r.returncode==0 else'failed_actual_independent_owner28_installer_reader','actual_exit_code':r.returncode,'actual_command':[sys.executable,str(HELP)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':{str(HELP):before},'helper_sha256_after':{str(HELP):H(HELP)},'log':str(LOG),'log_sha256':H(LOG),'live_source_owner_or_report_write':False}
with REC.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));sys.exit(r.returncode)
