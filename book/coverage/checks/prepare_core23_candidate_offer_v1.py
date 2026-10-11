"""Prepare a reviewable isolated Core23 offer from completed original evidence."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[3];B='book/coverage/checks/future23-core'
sha=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();read=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':n,'sha256':sha(n)}
C=B+'/core23-source51-candidate-v2.json';I=B+'/core23-source51-candidate-integrity-v2.json';P=B+'/core23-reviewed-source51-packet-v1.json';READY=B+'/core23-nine-source88-export-actual-readiness-v1.json';EXEC='reports/full-coverage/core23-candidate-builder-execution-v2.json'
c=read(C);i=read(I);pkt=read(P);ready=read(READY);actual=read(EXEC)
assert actual['actual_exit_code']==0 and actual['actual_command']==['python3','book/coverage/core_source51_candidate23_v2.py']
assert actual['helper_sha256_before']==actual['helper_sha256_after']
assert sha(actual['log'])==actual['log_sha256']
assert i['candidate']==ref(C) and i['packet']==ref(P) and i['baseline166_proof_rows_exact']
assert sha('book/coverage/core.json')==pkt['baseline_ledger']['sha256']
for n,h in ready['held22_working_owner_sha256'].items():assert sha(n)==h
for e in c['material_claims']:
 if e['kind']=='independently_reviewed_literal_material_unit' and e.get('original_complete_literal_review_record',{}).get('whole_unit_approved'):assert e['statement_in_prose']==e['source_text']
ev={n:r['sha256'] for n,r in ready['additional_exact_original_provenance'].items()}
for n in [C,I,P,READY,EXEC,actual['log'],'book/coverage/core_source51_candidate23_v1.py','book/coverage/core_source51_candidate23_v2.py',B+'/core23-source51-candidate-v1.json',B+'/core23-source51-candidate-integrity-v1.json',B+'/core23-candidate-v1-literal-statement-consistency-root-observation-v1.json','reports/full-coverage/core23-candidate-builder-execution-v1.json','reports/full-coverage/core23-candidate-builder-execution-v1.log',i['identity']['file']]:ev[n]=sha(n)
for p in (R/B/'original-tmp').iterdir():
 if p.is_file():ev[str(p.relative_to(R))]=sha(str(p.relative_to(R)))
for n,h in ev.items():assert sha(n)==h,n
proofs=copy.deepcopy(ready['proof_files'])
for p in proofs.values():
 for n,h in p['evidence_sha256'].items():assert sha(n)==h
out=B+'/core-audit23-candidate-source51-additions-v1.json';p=R/out;assert not p.exists()
d={'status':'isolated_core23_source51_candidate_ready_for_independent_final_mapping_review','created_at_utc':datetime.now(timezone.utc).isoformat(),'baseline_selection':'reports/full-coverage/checkpoint-22-selection.json','baseline_selection_sha256':sha('reports/full-coverage/checkpoint-22-selection.json'),'actual_passing_baseline_audit':'reports/full-coverage/lean-checkpoint-22/verification-original.json','actual_passing_baseline_audit_sha256':sha('reports/full-coverage/lean-checkpoint-22/verification-original.json'),'proof_files':proofs,'proof_file_count':9,'local_theorem_count':88,'mapped_ledger':C,'mapped_ledger_sha256':sha(C),'builder_sha256':sha('book/coverage/core_source51_candidate23_v2.py'),'actual_builder':EXEC,'actual_builder_sha256':sha(EXEC),'current_inventory':'book/coverage/inventory-after-correction51.json','current_inventory_sha256':sha('book/coverage/inventory-after-correction51.json'),'source_sha256':read('book/coverage/inventory.json')['source_sha256'],'review_sha256':{pkt[k]['file']:pkt[k]['sha256'] for k in ['monitoring_review','lyapunov_identity_component_review','lyapunov_whole_review']},'candidate_packet':ref(P),'candidate_integrity':ref(I),'baseline22_owner_assets':ready['held22_working_owner_sha256'],'counts':c['counts'],'fresh_material_unit_keys':i['whole_material_units'],'changed_exercise_keys':i['changed_exercises'],'changed_exercise_statuses':{e['inventory_key']:e['status'] for e in c['exercises'] if e['inventory_key'] in i['changed_exercises']},'public_theorems_by_source':ready['public_theorems_by_source'],'required_evidence_artifacts_sha256':ev,'original_failure_history':[ref(B+'/core23-candidate-v1-literal-statement-consistency-root-observation-v1.json')],'coverage_complete':False,'live_owner_assets_mutated':False,'limits':['Exact independent whole material decisions only; both parent exercises remain partial. Original false decimal contrast export is not a positive current-source claim.','All old proof rows and original semantic/hypothesis/time bodies remain archived exactly. A fresh final candidate peer and actual global aggregate23 audit remain required.']}
p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'status':'prepared_for_independent_review','offer':ref(out),'candidate':ref(C),'required_completed_evidence':len(ev)}))
