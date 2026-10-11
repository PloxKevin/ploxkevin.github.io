"""Isolated25 candidate: full corrected answer(b), three scoped temporal groups.

This never installs modules.json or changes HTML/inventory. Old24 review bodies,
proof rows, declaration prefix and all prior positive atoms remain immutable.
"""
from pathlib import Path
from datetime import datetime,timezone
import collections,copy,hashlib,json,re,sys
from lean_names import declarations
ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/modules-future25/source52'
READY='book/coverage/checks/modules-future25/temporal/two-source-nine-export-canonical-paired-readiness25-v1.json'
READY_SHA='ece72891d687f9d6ea937121ec59b8477b613526a58708ebe5d4726f8150e578'
LIVE='book/coverage/modules.json';LIVE_SHA='1d4395c5b7cb9dc18217b0c4236a04868f67a2445d0ffed18f3a77215d3b2c90'
INV='book/coverage/inventory-after-correction52.json';INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
H=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
J=lambda n:json.loads((ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,body):
 p=ROOT/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(body,indent=2,ensure_ascii=False)+'\n')
def declarations_rows(out,n,names):
 text=(ROOT/n).read_text()
 for name in names:
  m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m,name
  out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()})
def main(binding_path):
 assert H(LIVE)==LIVE_SHA and H(INV)==H('book/coverage/inventory.json')==INV_SHA and H(READY)==READY_SHA
 old=J(LIVE);inventory=J(INV);ready=J(READY);selection=J('reports/full-coverage/checkpoint-24-selection.json')
 assert len(selection['proof_files'])==1144
 for f,row in selection['proof_files'].items():assert H(f)==row['sha256'],f
 prep=J(ready['source_preparation']['file']);assert H(ready['source_preparation']['file'])==ready['source_preparation']['sha256']
 protected=prep['current24_owner_inventory_sha256_before_after_exact']
 for f,sha in protected.items():assert H(f)==sha
 baseline=BASE+'/pre-candidate24/modules.json';p=ROOT/baseline;p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_bytes((ROOT/LIVE).read_bytes())
 assert H(baseline)==LIVE_SHA
 binding=J(binding_path);assert binding['errors']==[] and 'passed' in binding['status']
 reviews={k:J(ready[k]['file']) for k in ['original_component_peer','original_whole_answer_b_peer','original_selected_universal_monotonicity_supplement']}
 for k in reviews:assert H(ready[k]['file'])==ready[k]['sha256']
 temporal=reviews['original_component_peer'];whole=reviews['original_whole_answer_b_peer'];supp=reviews['original_selected_universal_monotonicity_supplement']
 assert temporal['errors']==whole['errors']==supp['errors']==[]
 assert supp['entire_original_peer_body_decisions_and_time']==whole
 assert whole['whole_mathematical_units_approved']==['nn-in-the-loop.html::node-1260']
 aliases={old:new for old,new in [('SafeLearning.CompleteModulesNNDoublyHyperdominant24','SafeLearning.CompleteModulesNNDoublyHyperdominant25'),('SafeLearning.CompleteModulesNNTemporalDiagonal24','SafeLearning.CompleteModulesNNTemporalDiagonal25')]}
 mapped=lambda xs:[next((n.replace(a,b) for a,b in aliases.items() if n.startswith(a+'.')),n) for n in xs]
 assert binding['canonical_readiness']==ref(READY)
 assert binding['entire_original_component_peer_body_and_time']==temporal
 expected_aliases={name:mapped([name])[0] for source in ready['source_files'] for name in [next((new.replace(b,a) for a,b in aliases.items() if new.startswith(b+'.')),new) for new in source['public_theorems']]}
 assert binding['old_to_new_public_declaration_names']==expected_aliases
 assert [row['canonical_source'] for row in binding['canonical_sources']]==[row['source'] for row in ready['source_files']]
 assert binding['public_export_count']==9 and binding['source_count']==2 and not binding['whole_c_or_exercise_approved']
 out=copy.deepcopy(old);unitmap={u['key']:u for u in inventory['material_source_units']};exmap={e['key']:e for e in inventory['exercises']}
 b=whole['material_units'][0];c=temporal['material_units'][0];assert unitmap[b['key']]==b['entire_inventory_record'] and unitmap[c['key']]==c['entire_inventory_record']
 exkey='nn-in-the-loop.html::exercise-20';e=next(e for e in out['exercises'] if e['inventory_key']==exkey)
 assert e['status']=='partial' and temporal['exercise']['entire_inventory_record']==exmap[exkey]
 prior_ex=copy.deepcopy(e);target=next(u for u in out['material_claims'] if u['id']==b['key']+'::claim-review');prior_b=copy.deepcopy(target);assert target['status']=='pending'
 support=supp['selected_lean_declarations'];chain=supp['source']['file'];assert H(chain)==supp['source']['sha256']==selection['proof_files'][chain]['sha256']
 wholedecl=list(dict.fromkeys(b['lean_declarations']+support));hyp=b['hypotheses']+supp['hypotheses'];reason=b['per_component_reason']+' '+supp['binding_reason']
 target.update(status='proved',kind='independently_reviewed_complete_mathematical_source_unit',lean_declarations=wholedecl,hypotheses=hyp,correspondence=reason,remaining_gaps=[],independent_source_review=ready['original_whole_answer_b_peer'],selected_universal_monotonicity_evidence_supplement=ready['original_selected_universal_monotonicity_supplement'],prior_source52_pending_claim_body_preserved=prior_b,entire_original_whole_unit_review_body_and_time=whole)
 e['claims'].append({'id':exkey+'::source52-reviewed25-whole-answer-b','kind':'independently_reviewed_complete_answer_unit','statement_in_prose':unitmap[b['key']]['source_text'],'status':'proved','lean_declarations':wholedecl,'hypotheses':hyp,'correspondence':reason,'remaining_gaps':[],'source_unit_keys':[b['key']],'independent_source_review':ready['original_whole_answer_b_peer'],'selected_universal_monotonicity_evidence_supplement':ready['original_selected_universal_monotonicity_supplement'],'entire_original_unit_review_body_and_time':b})
 groups=[]
 for g in c['components']:
  assert g['missing_clauses']==[]
  atom={'id':exkey+'::source52-reviewed25-temporal-component-'+g['component_id'],'kind':'independently_reviewed_precise_mathematical_component','statement_in_prose':g['per_component_reason'],'status':'proved','lean_declarations':mapped(g['lean_declarations']),'hypotheses':g['hypotheses'],'correspondence':g['per_component_reason'],'remaining_gaps':[],'source_unit_keys':[c['key']],'independent_source_review':ready['original_component_peer'],'entire_original_component_body_and_time_preserved':copy.deepcopy(g),'original_component_review_time':temporal['reviewed_at_utc'],'explicit_namespace_prefix_aliases':aliases,'canonical_source_original_body_binding_peer':ref(binding_path)}
  e['claims'].append(copy.deepcopy(atom));material=copy.deepcopy(atom);material['id']=exkey+'::material-source52-reviewed25-temporal-component-'+g['component_id'];out['material_claims'].append(material);groups.append(atom)
 assert len(groups)==3
 pending_c=next(u for u in out['material_claims'] if u['id']==c['key']+'::claim-review');prior_c=copy.deepcopy(pending_c);assert pending_c['status']=='pending'
 pending_c['remaining_gaps']=copy.deepcopy(c['remaining_gaps']);pending_c['independent_source_review25']=ready['original_component_peer'];pending_c['prior_source52_claim_body_preserved25']=prior_c
 e['independent_source_reviews25']=[ready[k] for k in reviews];e['canonical_temporal_binding_peer25']=ref(binding_path);e['remaining_whole_source_gaps25']=c['remaining_gaps']
 assert e['status']=='partial'
 newproofs={};all_new=[]
 for src in ready['source_files']:
  n=src['source']['file'];assert n not in old['proof_files'] and H(n)==src['source']['sha256']
  public=[d['name'] for d in declarations((ROOT/n).read_text()) if d['kind'] in ('theorem','lemma')];assert public==src['public_theorems']
  pairs=[p for p in ready['actual_paired_records'] if p['source']['file']==n];assert len(pairs)==2
  for pair,kind in zip(pairs,['standalone','named-build']):
   for key in ['actual_record','raw_log','source_snapshot']:assert H(pair[key]['file'])==pair[key]['sha256']
   ar=J(pair['actual_record']['file']);assert ar['actual_exit_code']==0 and pair['actual_exit_code']==0 and pair['kind']==kind
   assert ar['source']==n and ar['source_sha256_before']==ar['source_sha256_after']==H(n)==ar['source_snapshot_sha256']
   assert ar['raw_log_sha256']==pair['raw_log']['sha256']
   cmd=['lake','env','lean',n.removeprefix('verification/lean/')] if kind=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
   assert ar['actual_command']==cmd
  st=pairs[0];compile_evidence={'file':n,'sha256':H(n),'exit_code':0,'source_unchanged':True,'log':st['raw_log']['file'],'log_sha256':st['raw_log']['sha256'],'compiler_manifest':st['actual_record']['file'],'compiler_manifest_sha256':st['actual_record']['sha256']}
  out['proof_files'][n]={'sha256':H(n),'selection_scope':'independently_reviewed_precise_temporal25_component_source','proof_selection_owner':'Modules25','standalone_compile_status':'passed','standalone_compile_evidence':compile_evidence,'actual_paired_records':pairs,'declarations':public}
  newproofs[n]={'sha256':H(n),'declarations':public,'actual_paired_records':pairs,'evidence_sha256':{pair[k]['file']:pair[k]['sha256'] for pair in pairs for k in ['actual_record','raw_log','source_snapshot']}}
  declarations_rows(out,n,public);all_new+=public
 assert len(newproofs)==2 and len(all_new)==9
 assert set(sum([g['lean_declarations'] for g in groups],[]))==set(all_new)
 original=supp['actual_original_standalone'];ar=original['canonical_record'];lr=original['canonical_raw_log'];ss=original['canonical_source_snapshot']
 for rr in [ar,lr,ss]:assert H(rr['file'])==rr['sha256']
 all_chain=[d['name'] for d in declarations((ROOT/chain).read_text()) if d['kind'] in ('theorem','lemma')];assert set(support)<=set(all_chain)
 out['proof_files'][chain]={'sha256':H(chain),'selection_scope':'exact_selected24_generic_weak_order_source_reused_for_fresh_whole_answer_b','proof_selection_owner':'original_Foundations_selected24_reused_by_Modules25','standalone_compile_status':'passed','standalone_compile_evidence':{'file':chain,'sha256':H(chain),'exit_code':0,'source_unchanged':True,'log':lr['file'],'log_sha256':lr['sha256'],'compiler_manifest':ar['file'],'compiler_manifest_sha256':ar['sha256']},'declarations':all_chain,'original_selected24_row_identity':{'source':chain,'sha256':selection['proof_files'][chain]['sha256']},'independent_selected_order_evidence_supplement':ready['original_selected_universal_monotonicity_supplement']}
 declarations_rows(out,chain,support)
 out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
 out['reviewed_work_integration25_candidate']={'baseline24_module_ledger':ref(baseline),'current_inventory':ref(INV),'original_whole_answer_b_peer':ready['original_whole_answer_b_peer'],'selected_universal_monotonicity_evidence_supplement':ready['original_selected_universal_monotonicity_supplement'],'original_temporal_component_peer':ready['original_component_peer'],'canonical_temporal_binding_peer':ref(binding_path),'original_namespace_prefix_aliases':aliases,'fresh_whole_material_units':[b['key']],'fresh_precise_temporal_component_count':3,'new_source_files':list(newproofs),'new_public_exports':9,'reused_selected24_generic_order_source':chain,'whole_answer_c_or_exercise_promoted':False,'live_owner_assets_mutated':False}
 out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
 olde={e['inventory_key']:e for e in old['exercises']};oldu={c['id']:c for c in old['material_claims']}
 for e in out['exercises']:
  if e['inventory_key']!=exkey:assert e==olde[e['inventory_key']]
 assert next(e for e in out['exercises'] if e['inventory_key']==exkey)['claims'][:len(prior_ex['claims'])]==prior_ex['claims']
 for u in out['material_claims'][:len(old['material_claims'])]:
  if u['id'] not in {b['key']+'::claim-review',c['key']+'::claim-review'}:assert u==oldu[u['id']]
 for n,row in old['proof_files'].items():assert out['proof_files'][n]==row
 assert out['declarations'][:len(old['declarations'])]==old['declarations']
 for f,sha in protected.items():assert H(f)==sha
 for f,row in selection['proof_files'].items():assert H(f)==row['sha256']
 inputpath=BASE+'/modules25-source52-input-bindings-v1.json';put(inputpath,{'status':'exact_original_whole_and_precise_component_review_bindings_for_isolated25','current_inventory':ref(INV),'baseline24_module_ledger':ref(baseline),'canonical_readiness':ref(READY),'canonical_temporal_binding_peer':ref(binding_path),'entire_original_whole_answer_b_review_body_and_time':whole,'entire_selected_generic_order_evidence_supplement_body_and_time':supp,'entire_original_temporal_component_review_body_and_time':temporal,'explicit_namespace_prefix_aliases':aliases,'proof_files':newproofs,'selected24_reused_order_source':ref(chain),'protected_live_owner_inventory_sha256':protected})
 candidate=BASE+'/modules25-candidate-source52-v1.json';put(candidate,out)
 integrity=BASE+'/modules25-source52-candidate-integrity-v1.json';put(integrity,{'status':'passed_exact_isolated25_whole_answer_b_and_scoped_temporal_mapping','errors':[],'candidate':ref(candidate),'input_bindings':ref(inputpath),'baseline24_module_ledger':ref(baseline),'current_inventory':ref(INV),'fresh_whole_material_unit_keys':[b['key']],'precise_temporal_component_count':3,'original12_static_component_bodies_and_old_positive_atoms_preserved':True,'old_exercise_bodies_preserved_except_append_only_reviewed_atoms':216,'old_material_bodies_preserved':len(old['material_claims'])-2,'old_proof_rows_preserved':len(old['proof_files']),'old_declaration_prefix_preserved':True,'new_sources':2,'new_exports':9,'actual_new_compiler_records':4,'reused_selected24_source_count':1,'whole_answer_c_or_exercise_promoted':False,'live_owner_assets_mutated':False})
 print(json.dumps({'candidate':ref(candidate),'integrity':ref(integrity),'input_bindings':ref(inputpath),'counts':out['counts']}))
if __name__=='__main__':
 assert len(sys.argv)==2,'Canonical binding peer path required'
 main(sys.argv[1])
