from pathlib import Path
from datetime import datetime,timezone
import subprocess,hashlib,json,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-root-tmp-lean28-runner4-independent-modules-v1.py');J=Path('/tmp/modules-runner28-v4-independent-code-actual-v1.json');L=J.with_suffix('.log');O=Path('/tmp/modules-runner28-v4-independent-code-review-v1.json')
assert all(not p.exists() for p in (J,L,O))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
h=sha(C);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(C)]
with L.open('xb') as f:p=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();body={'actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'actual_helper':{'file':str(C),'sha256':h},'helper_sha256_before':h,'helper_sha256_after':sha(C),'raw_log':str(L),'raw_log_sha256':sha(L),'actual_runner':{'file':__file__,'sha256':sha(Path(__file__))}}
with J.open('x') as f:f.write(json.dumps(body,indent=2)+'\n')
if p.returncode==0:
 result=json.loads(Path('/tmp/modules-runner28-v4-independent-code-check-result-v1.json').read_bytes());result['actual_independent_code_review']={'file':str(J),'sha256':sha(J)};result['actual_independent_reader']={'file':str(C),'sha256':h};result['actual_independent_runner']={'file':__file__,'sha256':sha(Path(__file__))};result['closed_evidence_sha256'].update({str(z):sha(z) for z in (C,J,L,Path(__file__),Path('/tmp/modules-runner28-v4-independent-code-check-result-v1.json'))})
 with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'peer':str(O),'sha256':sha(O),'fixture_count':result['fixture_count'],'native_prefix_ready':result['native_prefix_ready'],'actual_exit_code':p.returncode}))
else:print(json.dumps({'actual_exit_code':p.returncode,'actual_record':str(J),'raw_log':str(L)}))
raise SystemExit(p.returncode)
