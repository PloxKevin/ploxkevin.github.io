from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
C=BASE/'check-owner24-live-interface-schema-independent-foundations-v3.py';O=BASE/'owner24-live-interface-schema-independent-foundations-actual-v3.json';L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)];a=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with L.open('xb') as f:f.write(a.stdout)
with O.open('x') as f:f.write(json.dumps({'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual author-independent read-only code fixture only; synthetic additions object is explicitly a test, no production/live interface/main or mathematical execution.'},indent=2)+'\n')
print(a.stdout.decode());print(O.read_text());raise SystemExit(a.returncode)
