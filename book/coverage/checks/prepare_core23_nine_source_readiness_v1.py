"""Bind nine original actual paired proofs without approving source correspondence."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
sha=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
read=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':sha(n)}
M=read('reports/full-coverage/checkpoint-22-manifest.json')
INV='book/coverage/inventory-after-correction51.json';IS='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert sha(INV)==sha('book/coverage/inventory.json')==IS
assert read('reports/full-coverage/source51-apply-execution-v1.json')['actual_exit_code']==0
assert read('book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json')['actual_exit_code']==0
held={n:M['working_inputs_sha256'][n] for n in ['book/coverage/'+s+'.json' for s in ['core','applied','modules','foundations','applied-promotions']]}
for n,h in held.items():assert sha(n)==h,n
for n,p in M['proof_files'].items():assert sha(n)==p['sha256'],n
roots=['root-monitoring23-canonical-readiness-v1.json','root-monitoring-face23-canonical-readiness-v1.json','root-monitoring-shift23-canonical-readiness-v1.json','root-monitoring-exposed23-canonical-readiness-v1.json']
rows={};readiness=[]
for name in roots:
 n='book/coverage/checks/future23-monitoring/'+name;d=read(n);readiness.append(ref(n));rows[d['source']['file']]={'sha256':d['source']['sha256'],'actual_refs':[{'file':x['file'],'sha256':x['sha256']} for x in d['actual_canonical_pair']]}
n='book/coverage/checks/applied-future23/lyapunov-scenario/four-source37-export-canonical-readiness-v2.json';d=read(n);readiness.append(ref(n))
for x in d['proof_rows']:rows[x['proof_source']['file']]={'sha256':x['proof_source']['sha256'],'actual_refs':x['actual_paired_records']}
n='book/coverage/checks/applied-future23/lyapunov-scenario/continuous-risk/continuous-risk-six-export-canonical-readiness-v1.json';d=read(n);readiness.append(ref(n));rows[d['proof_source']['file']]={'sha256':d['proof_source']['sha256'],'actual_refs':d['actual_paired_records']}
proofs={};counts={};extra={}
for n,row in rows.items():
 assert n not in M['proof_files'] and sha(n)==row['sha256'],n
 ds=declarations((R/n).read_text());counts[n]=sum(x['kind'] in {'theorem','lemma'} for x in ds)
 pairs=[];ev={}
 for i,r in enumerate(row['actual_refs']):
  assert sha(r['file'])==r['sha256'];a=read(r['file'])
  assert a['exit_code']==0 and a['source_unchanged'] is True
  assert a['source']==n and a['source_sha256_before']==a['source_sha256_after']==row['sha256']
  assert a['actual_workdir']==str(R/'verification/lean')
  cmd=['lake','env','lean',str(Path(n).relative_to('verification/lean'))] if i==0 else ['lake','build','SafeLearning.'+Path(n).stem]
  assert a['command']==cmd,(n,a['command'])
  assert sha(a['log'])==a['log_sha256'];ev[r['file']]=r['sha256'];ev[a['log']]=a['log_sha256']
  pairs.append({'actual_record':r,'raw_log':ref(a['log']),'source_snapshot':ref(n),'actual_exit_code':0})
 proofs[n]={'sha256':row['sha256'],'evidence_sha256':ev,'actual_paired_records':pairs,'declarations':ds}
assert len(proofs)==9 and sum(counts.values())==88
for base in ['book/coverage/checks/future23-monitoring','book/coverage/checks/future23-monitoring-source51','book/coverage/checks/applied-future23/lyapunov-scenario']:
 for p in sorted((R/base).rglob('*')):
  if p.is_file():extra[str(p.relative_to(R))]={'sha256':sha(str(p.relative_to(R))),'scope':'immutable_audit_or_local_source_evidence'}
for n in ['reports/full-coverage/source49-apply-execution-v1.json','reports/full-coverage/source49-apply-execution-v1.log','reports/full-coverage/source50-apply-execution-v1.json','reports/full-coverage/source50-apply-execution-v1.log','reports/full-coverage/source51-apply-execution-v1.json','reports/full-coverage/source51-apply-execution-v1.log']:
 extra[n]={'sha256':sha(n),'scope':'immutable_audit_or_local_source_evidence'}
for n,h in held.items():assert sha(n)==h,n
out='book/coverage/checks/future23-core/core23-nine-source88-export-actual-readiness-v1.json';p=R/out;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
p.write_text(json.dumps({'status':'passed_nine_exact_sources_eighteen_original_actual_compilers_requires_fresh_source_mapping_and_aggregate23','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'current_inventory':ref(INV),'proof_files':proofs,'new_proof_source_count':9,'public_theorem_count':88,'public_theorems_by_source':counts,'readiness_references':readiness,'additional_exact_original_provenance':extra,'held22_working_owner_sha256':held,'protected_selected22_source_count':1113,'whole_material_or_exercise_approved':False,'coverage_complete':False,'scope':'Original compiler commands, logs and times remain immutable. This new binding is neither a semantic review nor an aggregate Lean/kernel/axiom audit.'},indent=2)+'\n')
print(json.dumps({'status':'passed_actual_pair_bindings','readiness':ref(out),'proof_sources':9,'public_theorems':88,'original_provenance_files':len(extra)}))
