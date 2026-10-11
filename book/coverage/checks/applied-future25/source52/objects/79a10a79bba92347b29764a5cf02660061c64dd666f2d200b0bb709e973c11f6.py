from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
C=Path('/tmp/check-applied-conditioning-alarm25-independent-foundations-full-review-v1.py');O=Path('/tmp/applied-conditioning-alarm25-independent-foundations-full-review-actual-v1.json');L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)];a=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with L.open('xb') as f:f.write(a.stdout)
with O.open('x') as f:f.write(json.dumps({'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual author-independent TMP semantic evidence checker only; no new compiler, named/canonical pair, production interface, owner or source write.'},indent=2)+'\n')
print(a.stdout.decode());print(O.read_text());raise SystemExit(a.returncode)
