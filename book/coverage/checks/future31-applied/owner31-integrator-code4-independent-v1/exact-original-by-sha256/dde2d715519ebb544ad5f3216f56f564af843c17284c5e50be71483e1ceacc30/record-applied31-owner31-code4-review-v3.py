from pathlib import Path
from datetime import datetime, timezone
import subprocess,hashlib,json,time,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
CMD=['python3','/tmp/review-applied31-owner31-integrator-code4-v3.py']
SELF=Path(__file__);INNER=Path(CMD[1])
LOG=Path('/tmp/applied31-owner31-code4-review-v3-actual.log')
OUT=Path('/tmp/applied31-owner31-code4-review-v3-actual.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not LOG.exists() and not OUT.exists()
helpers={str(SELF):sha(SELF),str(INNER):sha(INNER)}
start=datetime.now(timezone.utc);tick=time.monotonic()
with LOG.open('xb') as f:process=subprocess.run(CMD,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc);elapsed=time.monotonic()-tick
after={str(SELF):sha(SELF),str(INNER):sha(INNER)}
d={'status':'passed' if process.returncode==0 and helpers==after else 'failed','actual_exit_code':process.returncode,'actual_command':CMD,'actual_workdir':str(ROOT),'started_at_utc':start.isoformat(),'finished_at_utc':end.isoformat(),'elapsed_seconds':elapsed,'helper_sha256_before':helpers,'helper_sha256_after':after,'log':str(LOG),'log_sha256':sha(LOG),'protection_errors':[] if helpers==after else ['reader helper changed'],'scope':'Actual independent read-only schema, byte, proof-metadata and isolated full-coverage validator execution. No producer or compiler executed.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'actual_exit_code':process.returncode,'actual_native':str(OUT),'actual_native_sha256':sha(OUT),'elapsed_seconds':elapsed}))
sys.exit(process.returncode)
