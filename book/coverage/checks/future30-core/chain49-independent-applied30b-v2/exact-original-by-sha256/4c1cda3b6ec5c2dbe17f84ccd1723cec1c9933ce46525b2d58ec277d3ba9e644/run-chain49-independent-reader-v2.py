from pathlib import Path
from datetime import datetime, timezone
import subprocess,time,json,hashlib,sys
D=Path('/tmp/applied-recovery30b-chain49-v1')
s=D/'review-chain49-independent-v2.py';n=D/'chain49-independent-reader-actual-v2.json';log=n.with_suffix('.log');assert not n.exists() and not log.exists()
hash=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=hash(s);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run([sys.executable,str(s)],stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();out={'status':'passed_actual_independent_whole_reader' if r.returncode==0 else 'failed_actual_independent_whole_reader','actual_exit_code':r.returncode,'actual_command':[sys.executable,str(s)],'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'executed_script':{'file':str(s),'sha256_before':before,'sha256_after':hash(s)},'raw_log':{'file':str(log),'sha256':hash(log)},'original_actual_runner':{'file':'/tmp/root_tmp_lean_current65_owner29_runner_v1.py','sha256':'5eca9a664c2c81d8c67c412a20be5782f6e84ec124a193233a5a2700e602575c'},'actual_source65_installed29_context':{'file':'/tmp/root_tmp_lean_current65_owner29_context_v1.json','sha256':'ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'},'coverage_complete':False}
n.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'actual_exit_code':r.returncode,'native':str(n),'raw':str(log),'elapsed_seconds':out['elapsed_seconds']}));raise SystemExit(r.returncode)
