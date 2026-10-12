from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-pages27-config5-output-closure-correction-independent-modules-v1.py');J=Path('/tmp/pages27-config5-output-closure-correction-independent-modules-actual-v1.json');L=J.with_suffix('.log');O=Path('/tmp/pages27-config5-output-closure-final-independent-modules-review-v1.json');RESULT=Path('/tmp/pages27-config5-output-closure-corrected-independent-modules-review-v1.json')
assert all(not p.exists() for p in (J,L,O,RESULT));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();h=sha(C);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(C)]
with L.open('xb') as f:q=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();v={'actual_exit_code':q.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'actual_helper':{'file':str(C),'sha256':h},'helper_sha256_before':h,'helper_sha256_after':sha(C),'raw_log':str(L),'raw_log_sha256':sha(L),'actual_runner':{'file':__file__,'sha256':sha(Path(__file__))}}
with J.open('x') as f:f.write(json.dumps(v,indent=2)+'\n')
if q.returncode==0:
 result=json.loads(RESULT.read_bytes());result['actual_independent_closure_correction']={'file':str(J),'sha256':sha(J)};result['independent_closure_checker']={'file':str(C),'sha256':h};result['independent_closure_runner']={'file':__file__,'sha256':sha(Path(__file__))};result['closed_evidence_sha256'].update({str(p):sha(p) for p in [C,J,L,Path(__file__),RESULT]})
 with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'passed','peer':str(O),'sha256':sha(O),'config_sha256':result['config_sha256'],'excluded_count':result['excluded_count'],'included_bytes':result['actual_current_included_website_bytes']}))
else:print(json.dumps({'actual_exit_code':q.returncode,'actual_record':str(J),'raw_log':str(L)}))
raise SystemExit(q.returncode)
