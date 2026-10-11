from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,re
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'book/coverage/checks/applied-future24'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':H(p)}
prepared=BASE/'four-material24-canonical-source-and-original-history-preparation-v1.json';binding=read(prepared);protected=binding['protected_current_inputs_sha256']
def guard():
 for n,h in protected.items():assert H(ROOT/n)==h,n
assert binding['public_theorem_count']==29 and len(binding['proof_sources'])==4
guard();rows=[]
result=BASE/'four-material24-canonical-paired-build-readiness-v1.json';assert not result.exists()
for row in binding['proof_sources']:
 p=ROOT/row['source']['file'];name=p.stem;digest=row['source']['sha256'];assert H(p)==digest
 for suffix in ['-standalone.json','.log','-named-build.json','-named-build.log']:
  assert not (ROOT/'book/coverage/checks'/(name+suffix)).exists(),name+suffix
 for helper in ['book/coverage/check_core_standalone.py','book/coverage/check_core_named_build.py']:
  actual=subprocess.run(['python3',helper,name],cwd=ROOT,check=False);guard();assert H(p)==digest
  if actual.returncode:raise SystemExit(actual.returncode)
 pairs=[]
 for suffix in ['-standalone.json','-named-build.json']:
  q=ROOT/'book/coverage/checks'/(name+suffix);a=read(q)
  assert a['exit_code']==0 and a['source_unchanged'] and a['source_sha256_before']==a['source_sha256_after']==digest
  assert H(ROOT/a['log'])==a['log_sha256']
  pairs.append({'record':ref(q),'entire_original_actual_record':a,'raw_log':{'file':a['log'],'sha256':a['log_sha256']},'source_snapshot':row['source_snapshot']})
 rows.append(dict(row,actual_canonical_pair=pairs))
result.write_text(json.dumps({'status':'passed_genuine_four_canonical_standalone_and_named_pairs_unselected_future24','completed_at_utc':datetime.now(timezone.utc).isoformat(),'canonical_preparation':ref(prepared),'proof_sources':rows,'public_theorem_count':29,'actual_canonical_execution_count':8,'protected_frozen23_source_count':1131,'current_source_asset_count':31,'scope':'All canonical source bytes exactly original TMP full semantic reviews. Eight fresh actual local compiler executions only; old failures/warnings and original semantic times remain exact. Future24 aggregate/axiom audit/selection/live owner coverage and deployment are separate.','coverage_complete':False},indent=2)+'\n')
guard();print(json.dumps({'status':'passed','readiness':str(result.relative_to(ROOT)),'sha256':H(result),'sources':4,'actual_compiler_records':8,'public_theorems':29}))
