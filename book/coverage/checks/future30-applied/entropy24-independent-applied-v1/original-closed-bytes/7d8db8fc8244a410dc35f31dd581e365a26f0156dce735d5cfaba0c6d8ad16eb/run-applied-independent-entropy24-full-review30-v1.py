from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,time,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/applied-independent-entropy24-full-review30-v1.py');N=Path('/tmp/applied-independent-entropy24-full-review30-actual-v1.json');L=N.with_suffix('.log');assert not N.exists() and not L.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
h=sha(H);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
assert sha(H)==h
n={'status':'passed_actual_independent_full_semantic_reader_only' if r.returncode==0 else 'failed_actual_independent_full_semantic_reader','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':elapsed,'review_helper':{'file':str(H),'sha256':h},'wrapper':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':{'file':str(L),'sha256':sha(L)},'compiler_started':False,'producer_or_owner_changes':False,'coverage_complete':False}
N.write_text(json.dumps(n,indent=2)+'\n');print(json.dumps({'record':str(N),'sha256':sha(N),'actual_exit_code':r.returncode,'elapsed_seconds':elapsed}));raise SystemExit(r.returncode)
