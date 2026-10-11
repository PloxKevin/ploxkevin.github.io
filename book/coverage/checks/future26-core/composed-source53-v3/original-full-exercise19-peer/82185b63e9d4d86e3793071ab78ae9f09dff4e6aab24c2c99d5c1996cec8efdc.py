from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/applied-future23/lyapunov-scenario/continuous-risk'
BASE.mkdir(exist_ok=False)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':H(p)}
objects=BASE/'original-tmp-objects';objects.mkdir()
seeds=[Path('/tmp/applied-lyapunov-scenario-continuous-risk23-independent-review-request-v1.json'),Path('/tmp/lyapunov-scenario-continuous-risk23-independent-foundations-components-review-v2.json')]
seeds+=list(Path('/tmp').glob('applied-lyapunov-scenario-continuous-risk23-trial1*'))
seeds+=list(Path('/tmp').glob('lyapunov-scenario-continuous-risk23-independent-foundations-*'))
seeds+=[Path('/tmp/run-lyapunov-scenario-continuous-risk23-trial.py'),Path('/tmp/review-lyapunov-scenario-continuous-risk23-independent-foundations-v1.py'),Path('/tmp/review-lyapunov-scenario-continuous-risk23-independent-foundations-v2.py'),Path('/tmp/prepare-lyapunov-continuous-risk23-readiness-v1.py')]
def strings(v):
 if isinstance(v,str):yield v
 elif isinstance(v,list):
  for x in v:yield from strings(x)
 elif isinstance(v,dict):
  for x in v.values():yield from strings(x)
aliases={};queue=list(seeds)
while queue:
 p=queue.pop()
 if not p.is_file() or str(p) in aliases:continue
 sha=H(p);out=objects/(sha+p.suffix)
 if not out.exists():out.write_bytes(p.read_bytes())
 assert H(out)==sha;aliases[str(p)]={**ref(out),'original_file':str(p)}
 if p.suffix=='.json':
  for s in strings(json.loads(p.read_text())):
   if s.startswith('/tmp/') and Path(s).is_file():queue.append(Path(s))
aliasfile=BASE/'original-tmp-path-aliases-v1.json';aliasfile.write_text(json.dumps({'status':'exact_original_tmp_byte_copies_no_time_or_body_changes','created_at_utc':datetime.now(timezone.utc).isoformat(),'aliases':aliases},indent=2)+'\n')
manifest=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';m=json.loads(manifest.read_text())
for p,row in m['proof_files'].items():assert H(ROOT/p)==row['sha256']
name='CompleteLyapunovScenarioContinuousRisk23';sha='5ef92bc81062d544e4fd1ce6ba3959595a99ead2d0bcc858c7424b5341ff0699'
original=Path('/tmp')/(name+'.lean');assert H(original)==sha
canonical=ROOT/'verification/lean/SafeLearning'/(name+'.lean');assert not canonical.exists();canonical.write_bytes(original.read_bytes())
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
names=[d['name'] for d in declarations(canonical.read_text()) if d['kind'] in ['theorem','lemma']];assert len(names)==6
records=[]
for mode,cmd in [('standalone',['lake','env','lean','SafeLearning/'+name+'.lean']),('named-build',['lake','build','SafeLearning.'+name])]:
 snapshot=BASE/(name+'-'+mode+'-source.lean');snapshot.write_bytes(canonical.read_bytes());pre=H(canonical)
 start=datetime.now(timezone.utc).isoformat();clock=time.monotonic();p=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT);elapsed=time.monotonic()-clock;done=datetime.now(timezone.utc).isoformat();log=BASE/(name+'-'+mode+'.log');log.write_bytes(p.stdout)
 row={'status':'actual_'+mode+'_lean_execution','source':ref(canonical)['file'],'source_file':ref(canonical)['file'],'source_sha256_before':pre,'source_sha256_after':H(canonical),'source_unchanged':pre==H(canonical),'source_snapshot':ref(snapshot)['file'],'source_snapshot_sha256':H(snapshot),'command':cmd,'actual_command':cmd,'cwd':str(ROOT/'verification/lean'),'actual_workdir':str(ROOT/'verification/lean'),'started_at':start,'completed_at':done,'elapsed_seconds':elapsed,'actual_exit_code':p.returncode,'exit_code':p.returncode,'raw_log_file':ref(log)['file'],'raw_log_sha256':H(log),'log':ref(log)['file'],'log_sha256':H(log),'runner_file':str(Path(__file__)),'runner_sha256':H(Path(__file__)),'compiler_scope':'Genuine new immutable canonical future23 component execution; no aggregate23 or whole-exercise claim.'}
 rp=BASE/(name+'-'+mode+'.json');rp.write_text(json.dumps(row,indent=2)+'\n');records.append(ref(rp));print(json.dumps({'mode':mode,'actual_exit_code':p.returncode,'record':ref(rp)}),flush=True)
 assert pre==sha==H(canonical)==H(snapshot)
 if p.returncode:raise SystemExit(p.returncode)
for p,row in m['proof_files'].items():assert H(ROOT/p)==row['sha256']
runnercopy=BASE/'actual-canonical-paired-build-runner-v1.py';runnercopy.write_bytes(Path(__file__).read_bytes())
ready={'status':'new_continuous_iid_scalar_risk_component_canonical_actual_standalone_and_named_zero','created_at_utc':datetime.now(timezone.utc).isoformat(),'proof_source':ref(canonical),'original_tmp_source':ref(original),'public_declarations':names,'public_theorem_count':6,'actual_paired_records':records,'actual_runner':ref(runnercopy),'original_tmp_archives':ref(aliasfile),'preserved_original_independent_review':aliases[str(seeds[1])],'original_four37_pack':ref(ROOT/'book/coverage/checks/applied-future23/lyapunov-scenario/four-source37-export-canonical-readiness-v2.json'),'current_inventory':ref(ROOT/'book/coverage/inventory-after-correction50.json'),'protected_selected22':{'manifest':ref(manifest),'proof_count':len(m['proof_files']),'all_exact':True},'whole_unit_approved':False,'whole_exercise_approved':False,'limits':['Precise continuous common-law iid scalar lower-bound optimizer only; no general Campi–Garatti optimizer theorem.','Original standalone/semantic review times and first checker failure are preserved byte-exact.','No current22 ledger, production selector, aggregate23 or publication claim.']}
rp=BASE/'continuous-risk-six-export-canonical-readiness-v1.json';rp.write_text(json.dumps(ready,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'readiness':ref(rp),'status':ready['status']}),flush=True)
