from pathlib import Path
import hashlib,json,subprocess,time
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
DRIVER=Path('/tmp/modules-crown-other-radii28-panel-a-driver-v1.cjs')
OUT=Path('/tmp/modules-crown-other-radii28-panel-a-actual-v1.json')
LOG=OUT.with_suffix('.log')
RESULT=Path('/tmp/modules-crown-other-radii28-panel-a-result-v1.json')
assert all(not p.exists() for p in (OUT,LOG,RESULT))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
sel=ROOT/'reports/full-coverage/checkpoint-27-selection.json'
assert sha(sel)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
S=json.loads(sel.read_text());proofs={ROOT/k:v['sha256'] for k,v in S['proof_files'].items()};assert len(proofs)==1175
held={p:sha(p) for p in [DRIVER,Path(__file__),sel,ROOT/'SafeLearning/verification.html',ROOT/'book/coverage/modules.json',ROOT/'book/coverage/inventory.json']}
held.update(proofs)
for p,h in held.items():assert sha(p)==h
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['node',str(DRIVER)]
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();errors=[]
for p,h in held.items():
 if sha(p)!=h:errors.append(str(p))
if r.returncode==0:
 result=json.loads(LOG.read_bytes());assert result['status']=='passed_actual_current55_panel_a_runtime_at_two_requested_radii'
 RESULT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
out={'status':'passed_actual_panel_a_runtime_only' if r.returncode==0 and not errors else 'failed_actual_panel_a_runtime_or_protection','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'driver':ref(DRIVER),'runner':ref(Path(__file__)),'raw_log':ref(LOG),'result':ref(RESULT) if RESULT.exists() else None,'selection':ref(sel),'protected_selected_proof_count':1175,'source_unchanged':not errors,'protection_errors':errors,'lean_kernel_or_semantic_whole_approval_claimed':False}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));raise SystemExit(0 if r.returncode==0 and not errors else 1)
