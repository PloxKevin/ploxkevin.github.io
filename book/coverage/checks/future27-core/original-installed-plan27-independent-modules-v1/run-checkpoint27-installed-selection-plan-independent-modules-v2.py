from pathlib import Path
from datetime import datetime,timezone
import os,sys,json,hashlib,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');P=Path('/tmp/check-checkpoint27-installed-selection-plan-independent-modules-v2.py');J=Path('/tmp/checkpoint27-installed-selection-plan-independent-modules-actual-v2.json');L=J.with_suffix('.log');OUT=Path('/tmp/checkpoint27-installed-selection-plan-independent-modules-confirmation-v2.json');RESULT=Path('/tmp/checkpoint27-installed-selection-plan-independent-modules-check-result-v2.json');assert not J.exists() and not L.exists() and not OUT.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
c=[sys.executable,str(P)];env=dict(os.environ);env.pop('PYTHONHOME',None);s=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb') as f:p=subprocess.run(c,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
d={'status':'actual_independent_selection_plan27_read_only_preflight_reader_completed','actual_command':c,'actual_workdir':str(R),'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_exit_code':p.returncode,'checker':ref(P),'actual_runner':ref(Path(__file__)),'raw_log':str(L),'raw_log_sha256':sha(L),'scope':'Read-only complete concrete pending plan and controlled in-memory selector prepare(apply=False); no selection, content-map, freeze, compiler or owner writes.'}
with J.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
if p.returncode==0:
 q=json.loads(RESULT.read_bytes());q['actual_independent_execution']=ref(J);q['actual_runner']=ref(Path(__file__));q['checker']=ref(P);q['raw_log']=ref(L);q['original_check_result']=ref(RESULT)
 for x in [J,L,P,Path(__file__),RESULT]:q['closed_evidence_sha256'][str(x)]=sha(x)
 with OUT.open('x') as f:f.write(json.dumps(q,indent=2)+'\n')
 print(json.dumps({'status':'passed','peer':ref(OUT),'actual':ref(J),'raw_log':ref(L)}))
else:print(json.dumps(d))
raise SystemExit(p.returncode)
