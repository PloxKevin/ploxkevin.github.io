import hashlib,json,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path('/home/oxrexkevin/SafetyBased');cmd=['python3','/tmp/prepare-foundations-source64-qualifiers29-v1.py'];log=Path('/tmp/foundations-source64-preparation29-actual-v1.log');out=Path('/tmp/foundations-source64-preparation29-actual-v1.json');assert not log.exists() and not out.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=datetime.now(timezone.utc).isoformat();t=time.monotonic();r=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(r.stdout);d={'status':'passed' if r.returncode==0 else 'failed','actual_command':cmd,'actual_workdir':str(ROOT),'actual_exit_code':r.returncode,'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper':{'file':cmd[1],'sha256':sha(cmd[1])},'runner':{'file':__file__,'sha256':sha(__file__)},'raw_log':{'file':str(log),'sha256':sha(log)},'source64_applied':False,'coverage_complete':False};out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));raise SystemExit(r.returncode)
