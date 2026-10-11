from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
ROOT=Path(__file__).resolve().parents[5]
BASE='book/coverage/checks/modules-future25/source52'
H=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
J=lambda n:json.loads((ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
CAND=BASE+'/modules25-candidate-source52-v2.json';INPUT=BASE+'/modules25-source52-input-bindings-v2.json';INT=BASE+'/modules25-source52-candidate-integrity-v2.json';ACT=BASE+'/module25-candidate-builder-actual-execution-v2.json'
assert J(ACT)['actual_exit_code']==0 and H(J(ACT)['raw_log'])==J(ACT)['raw_log_sha256']
c=J(CAND);i=J(INPUT);ready=J(i['canonical_readiness']['file']);old=J(i['baseline24_module_ledger']['file'])
assert H('book/coverage/modules.json')==i['baseline24_module_ledger']['sha256']
assert i['current_inventory']['sha256']==H('book/coverage/inventory.json')
required={}
for root in ['book/coverage/checks/modules-future25/temporal',BASE]:
 for p in (ROOT/root).rglob('*'):
  if p.is_file() and p.suffix in {'.json','.log','.lean','.py','.txt','.cjs'} and '__pycache__' not in p.parts:
   n=p.relative_to(ROOT).as_posix();required[n]=H(n)
for n in ['book/coverage/build_modules25_candidate_source52_v1.py','book/coverage/build_modules25_candidate_source52_v2.py']:
 required[n]=H(n)
for n,row in i['proof_files'].items():
 for f,d in row['evidence_sha256'].items():assert H(f)==d;required[f]=d
supp=i['entire_selected_generic_order_evidence_supplement_body_and_time']
for k in ['canonical_record','canonical_raw_log','canonical_source_snapshot']:
 r=supp['actual_original_standalone'][k];assert H(r['file'])==r['sha256'];required[r['file']]=r['sha256']
selected=J('reports/full-coverage/checkpoint-24-selection.json')
reused={n:row['sha256'] for n,row in c['proof_files'].items() if n not in old['proof_files'] and n not in i['proof_files']}
assert len(reused)==1
for n,d in reused.items():assert selected['proof_files'][n]['sha256']==H(n)==d
proofs=i['proof_files']
for row in proofs.values():assert len(row['actual_paired_records'])==2
out={'schema_version':1,'status':'isolated_actual25_candidate_with_full_answer_b_and_precise_temporal_groups_pending_independent_final_mechanics','created_at_utc':datetime.now(timezone.utc).isoformat(),'current_inventory':i['current_inventory']['file'],'current_inventory_sha256':i['current_inventory']['sha256'],'module_ledger':CAND,'module_ledger_sha256':H(CAND),'mapped_ledger':CAND,'mapped_ledger_sha256':H(CAND),'module_builder':'book/coverage/build_modules25_candidate_source52_v2.py','module_builder_sha256':H('book/coverage/build_modules25_candidate_source52_v2.py'),'actual_builder':ref(ACT),'actual_builder_raw_log':ref(J(ACT)['raw_log']),'proof_files':proofs,'proof_selection_owner':'Modules25','new_proof_file_count':2,'new_theorem_or_lemma_count':9,'baseline24_module_ledger':i['baseline24_module_ledger'],'base_selection':'reports/full-coverage/checkpoint-24-selection.json','base_selection_sha256':H('reports/full-coverage/checkpoint-24-selection.json'),'actual_passing_baseline_audit':'reports/full-coverage/lean-checkpoint-24/verification-original.json','actual_passing_baseline_audit_sha256':H('reports/full-coverage/lean-checkpoint-24/verification-original.json'),'candidate_input_bindings':ref(INPUT),'candidate_binding_integrity':ref(INT),'source_sha256':c['source_sha256'],'original_full_or_precise_source_reviews':[ready[k] for k in ['original_whole_answer_b_peer','original_selected_universal_monotonicity_supplement','original_component_peer']],'canonical_original_body_binding_peer':i['canonical_temporal_binding_peer'],'fresh_whole_exercise_keys':[],'fresh_partial_exercise_keys':['nn-in-the-loop.html::exercise-20'],'fresh_whole_material_unit_keys':['nn-in-the-loop.html::node-1260'],'fresh_precise_material_unit_keys':['nn-in-the-loop.html::node-1262'],'reused_selected24_proof_sources_sha256':reused,'required_external_import_dependencies':{'verification/lean/SafeLearning/CompleteModulesNNDoublyHyperdominant25.lean':H('verification/lean/SafeLearning/CompleteModulesNNDoublyHyperdominant25.lean')},'required_evidence_artifacts_sha256':required,'additional_frozen_inputs':required,'counts':c['counts'],'independent_final_candidate_mapping_peer_pending':True,'live_owner_assets_mutated':False,'coverage_complete':False,'scope_limits':['Whole corrected52 answer(b) only, with encoded selected universal weak-order bridge and original static16 retained.','Three original independently approved temporal components only; exact original hypotheses, reasons, gaps and review times retained through explicit namespace aliases.','Whole answer(c), full Exercise20, FIR filter/window realization, general local slope transformations/cross-channel and odd scope remain pending.','Actual isolated mapping construction and two genuine new compiler pairs; no installed owner25 or aggregate25/live claim.']}
n=BASE+'/modules-audit25-candidate-source52-additions-draft-v1.json';assert not (ROOT/n).exists();(ROOT/n).write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'offer':ref(n),'candidate':ref(CAND),'input':ref(INPUT),'builder_actual':ref(ACT),'required_artifacts':len(required)}))
