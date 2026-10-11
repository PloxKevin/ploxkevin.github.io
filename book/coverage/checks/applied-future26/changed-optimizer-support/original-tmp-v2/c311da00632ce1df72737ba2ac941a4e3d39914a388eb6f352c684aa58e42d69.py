from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,sys,time,re,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/applied-future23/lyapunov-scenario';BASE.mkdir(parents=True,exist_ok=False);OBJECTS=BASE/'original-tmp-objects';OBJECTS.mkdir()
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rel=lambda p:str(Path(p).relative_to(ROOT));ref=lambda p:{'file':rel(p) if Path(p).is_relative_to(ROOT) else str(p),'sha256':h(p)}
seeds=[Path('/tmp/'+n) for n in ['applied-lyapunov-scenario-validation23-two-source-readiness-v1.json','lyapunov-scenario-validation23-independent-foundations-components-review-v2.json','applied-lyapunov-scenario-support23-independent-review-request-v1.json','lyapunov-scenario-support23-independent-foundations-components-review-v1.json','applied-lyapunov-scenario-convex-support23-independent-review-request-v1.json','lyapunov-scenario-convex-support23-independent-foundations-components-review-v1.json','applied-lyapunov-scenario-validation-precision-proposal23-v1.json','lyapunov-precision-proposal23-independent-foundations-semantic-review-v1.json','applied-lyapunov-scenario-precision-proposal23-preparation-execution-v1.json','prepare-lyapunov-scenario-validation23-readiness-v1.py','prepare-lyapunov-scenario-support23-readiness-v1.py','prepare-lyapunov-scenario-precision-proposal23-v1.py','run-lyapunov-scenario-precision-proposal23-v1.py']]
for pat in ['applied-lyapunov-scenario-numbers23-trial*','applied-lyapunov-validation-bridge23-trial*','applied-lyapunov-scenario-support23-trial*','applied-lyapunov-scenario-convex-support23-trial*']:
 seeds+=list(Path('/tmp').glob(pat))
queue=list(seeds);aliases={};seen=set()
def strings(value):
 if isinstance(value,str):yield value
 elif isinstance(value,list):
  for item in value:yield from strings(item)
 elif isinstance(value,dict):
  for item in value.values():yield from strings(item)
while queue:
 p=queue.pop()
 if str(p) in seen or not p.is_file():continue
 seen.add(str(p));sha=h(p);dest=OBJECTS/(sha+p.suffix)
 if not dest.exists():dest.write_bytes(p.read_bytes())
 assert h(dest)==sha
 aliases[str(p)]={'file':rel(dest),'sha256':sha,'original_file':str(p)}
 if p.suffix=='.json':
  obj=json.loads(p.read_text())
  for s in strings(obj):
   if s.startswith('/tmp/') and Path(s).is_file():queue.append(Path(s))
aliasfile=BASE/'original-tmp-path-aliases-v1.json';aliasfile.write_text(json.dumps({'status':'byte_exact_original_tmp_artifacts_copied_without_body_or_time_changes','created_at_utc':datetime.now(timezone.utc).isoformat(),'aliases':aliases,'limits':['Original TMP records/peers/checker failures and current source bodies are immutable; these are exact archival copies, not new executions or corrected historical results.']},indent=2)+'\n')
manifest=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';m=json.loads(manifest.read_text());before={p:row['sha256'] for p,row in m['proof_files'].items()}
for p,sha in before.items():assert h(ROOT/p)==sha
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
rows=[]
for name,expectedsha,count in [('CompleteLyapunovScenarioNumbers23','dfeda6956da8cfc4a8d814bc666b765c865153d73496e1c755b822df8e38c147',20),('CompleteLyapunovValidationBridge23','209b1161ff6d388517cbd695faa163b8a3db80a33f21d9fae3b28625dcce1147',5),('CompleteLyapunovScenarioSupport23','038615c0dacea25bfb8eb28b4770ac8f523a290ec20e1804f3848194f95ba38d',9),('CompleteLyapunovScenarioConvexSupport23','bb1ae9729ca1d098c9e8505db1cb3776f4edfc4d3cb335d29bf8f52d2d4c9b47',3)]:
 original=Path('/tmp/'+name+'.lean');assert h(original)==expectedsha
 canonical=ROOT/'verification/lean/SafeLearning'/ (name+'.lean');assert not canonical.exists();canonical.write_bytes(original.read_bytes());assert h(canonical)==expectedsha
 decls=[d['name'] for d in declarations(canonical.read_text()) if d['kind'] in ['theorem','lemma']];assert len(decls)==count
 records=[]
 for mode,cmd in [('standalone',['lake','env','lean','SafeLearning/'+name+'.lean']),('named-build',['lake','build','SafeLearning.'+name])]:
  snapshot=BASE/(name+'-'+mode+'-source.lean');snapshot.write_bytes(canonical.read_bytes());pre=h(canonical)
  start=datetime.now(timezone.utc).isoformat();clock=time.monotonic();proc=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT);elapsed=time.monotonic()-clock;done=datetime.now(timezone.utc).isoformat();log=BASE/(name+'-'+mode+'.log');log.write_bytes(proc.stdout)
  r={'status':'actual_'+mode+'_lean_execution','source':rel(canonical),'source_file':rel(canonical),'source_sha256_before':pre,'source_sha256_after':h(canonical),'source_unchanged':pre==h(canonical),'source_snapshot':rel(snapshot),'source_snapshot_sha256':h(snapshot),'actual_command':cmd,'command':cmd,'cwd':str(ROOT/'verification/lean'),'actual_workdir':str(ROOT/'verification/lean'),'started_at':start,'completed_at':done,'elapsed_seconds':elapsed,'actual_exit_code':proc.returncode,'exit_code':proc.returncode,'raw_log_file':rel(log),'raw_log_sha256':h(log),'log':rel(log),'log_sha256':h(log),'runner_file':str(Path(__file__)),'runner_sha256':h(Path(__file__)),'compiler_scope':'Genuine observed execution of this unchanged new future23 source; no aggregate/kernel/axiom audit or literal whole-exercise approval.'}
  record=BASE/(name+'-'+mode+'.json');record.write_text(json.dumps(r,indent=2)+'\n');records.append(ref(record));print(json.dumps({'source':name,'mode':mode,'actual_exit_code':proc.returncode,'record':ref(record),'raw_log_sha256':h(log)}),flush=True)
  if proc.returncode!=0:print(proc.stdout.decode(),flush=True);raise SystemExit(proc.returncode)
  assert pre==expectedsha==h(snapshot)==h(canonical)
 rows.append({'proof_source':ref(canonical),'original_tmp_source':{'file':str(original),'sha256':expectedsha},'original_source_alias':aliases.get(str(original)),'public_theorem_count':count,'public_declarations':decls,'actual_paired_records':records})
for p,sha in before.items():assert h(ROOT/p)==sha
readiness={'status':'four_new_immutable_scenario23_sources_genuine_canonical_standalone_and_named_zero','created_at_utc':datetime.now(timezone.utc).isoformat(),'proof_rows':rows,'new_source_count':4,'public_theorem_count':37,'actual_paired_record_count':8,'original_tmp_archives':ref(aliasfile),'original_tmp_file_count':len(aliases),'preserved_original_component_peer_paths':[str(p) for p in seeds if 'independent-foundations' in p.name and p.suffix=='.json'],'inventory':ref(ROOT/'book/coverage/inventory-after-correction49.json'),'protected_selected22':{'manifest':ref(manifest),'proof_count':len(before),'all_exact':True},'current22_owner_ledger_changed':False,'limits':['Actual new canonical executions supplement preserved original TMP executions; original bodies/logs/times remain byte-exact.','Only individually reviewed mathematical components are supplied. General optimizer scenario risk/Campi, GP posterior construction, original false decimals and wholeexercise approval remain separate.','The independently compiled continuous-law risk model is a distinct fifth TMP-only supplement, not included in this37-export pack.']}
rfile=BASE/'four-source37-export-canonical-readiness-v1.json';rfile.write_text(json.dumps(readiness,indent=2)+'\n');print(json.dumps({'status':readiness['status'],'readiness':ref(rfile),'archived_files':len(aliases)}),flush=True)
