from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'book/coverage/checks/applied-future26/cvar-fractional-selector'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
ref=lambda p:{'file':str(p.relative_to(ROOT)),'sha256':H(p)}
prepared=BASE/'one-source8-canonical-source-and-original-history-preparation-v1.json';binding=read(prepared);protected=binding['protected_current_inputs_sha256']
def guard():
 for n,h in protected.items():assert H(ROOT/n)==h,n
assert len(binding['proof_sources'])==1 and binding['public_theorem_count']==8
guard();rows=[];result=BASE/'one-source8-canonical-paired-build-readiness-v1.json';assert not result.exists()
for row in binding['proof_sources']:
 p=ROOT/row['source']['file'];name=p.stem;digest=row['source']['sha256'];assert H(p)==digest
 for suffix in ['-standalone.json','.log','-named-build.json','-named-build.log']:assert not(ROOT/'book/coverage/checks'/(name+suffix)).exists()
 for helper in ['book/coverage/check_core_standalone.py','book/coverage/check_core_named_build.py']:
  a=subprocess.run(['python3',helper,name],cwd=ROOT,check=False);guard();assert H(p)==digest
  if a.returncode:raise SystemExit(a.returncode)
 pairs=[]
 for suffix in ['-standalone.json','-named-build.json']:
  q=ROOT/'book/coverage/checks'/(name+suffix);a=read(q)
  assert type(a['exit_code'])is int and a['exit_code']==0 and a['source_unchanged'] and a['source_sha256_before']==a['source_sha256_after']==digest
  assert H(ROOT/a['log'])==a['log_sha256'];pairs.append({'record':ref(q),'entire_original_actual_record':a,'raw_log':{'file':a['log'],'sha256':a['log_sha256']},'source_snapshot':row['source_snapshot']})
 rows.append(dict(row,actual_canonical_pair=pairs))
result.write_text(json.dumps({'status':'passed_genuine_one_canonical_standalone_and_named_pairs_unselected_future26','completed_at_utc':datetime.now(timezone.utc).isoformat(),'canonical_preparation':ref(prepared),'proof_sources':rows,'public_theorem_count':8,'actual_canonical_execution_count':2,'protected_selected25_source_count':1156,'current_source_asset_count':31,'installed25_owner_count':5,'scope':'Two genuine new actual canonical compiler executions; exact original eight CVaR component and separate Landscape15 whole semantic bodies/times, TMP passes/failures/warnings archived. No future26 aggregate or selected/live coverage claim, no fixed25 amendment.','coverage_complete':False},indent=2)+'\n');guard();print(json.dumps({'status':'passed','readiness':ref(result),'sources':1,'actual_compiler_records':2,'public_theorems':8}))
