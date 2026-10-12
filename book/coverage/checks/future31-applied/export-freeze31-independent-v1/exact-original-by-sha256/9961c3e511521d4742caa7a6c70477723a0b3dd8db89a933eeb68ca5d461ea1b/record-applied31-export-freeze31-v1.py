from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
CMD=['python3','/tmp/review-applied31-export-freeze31-v1.py','--context','/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json','--context-sha256','0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c']
SELF=Path(__file__);HELPER=Path(CMD[1]);LOG=Path('/tmp/applied31-export-freeze31-v1-actual.log');OUT=Path('/tmp/applied31-export-freeze31-v1-actual.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not LOG.exists() and not OUT.exists()
before={str(SELF):sha(SELF),str(HELPER):sha(HELPER)};start=datetime.now(timezone.utc);tick=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(CMD,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc);after={str(SELF):sha(SELF),str(HELPER):sha(HELPER)}
d={'status':'passed' if p.returncode==0 and before==after else 'failed','actual_exit_code':p.returncode,'actual_command':CMD,'actual_workdir':str(ROOT),'started_at_utc':start.isoformat(),'finished_at_utc':end.isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(LOG),'log_sha256':sha(LOG),'protection_errors':[] if before==after else ['review helper changed'],'scope':'Actual full code and finalized audit input review under the released actual Source81/installed owner31 context. No exporter, freezer, compiler or publication invoked.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'actual_exit_code':p.returncode,'native':str(OUT),'native_sha256':sha(OUT),'elapsed_seconds':d['elapsed_seconds']}));sys.exit(p.returncode)
