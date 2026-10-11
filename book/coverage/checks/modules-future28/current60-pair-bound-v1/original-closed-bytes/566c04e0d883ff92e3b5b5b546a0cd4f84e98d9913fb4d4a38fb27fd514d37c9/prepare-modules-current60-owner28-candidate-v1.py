from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,re,collections
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUTDIR=Path('/tmp/modules-current60-owner28-candidate-v1');assert not OUTDIR.exists();OUTDIR.mkdir()
CAND=OUTDIR/'modules-current60-owner28-pending-canonical-pairs.json'
IDENTITY=OUTDIR/'modules-current55-to60-full-owned-literal-identities28-v1.json'
REPORT=OUTDIR/'modules-current60-owner28-candidate-preparation-v1.json'
PLAN=Path('/tmp/modules-owner28-approved-scope-plan-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def object_sha(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
assert sha(PLAN)=='e7dd4b6488bd1ec796bf9289655b1e49f4a7fcf60c85dc48e046ec3c79a3a440'
assert sha(ROOT/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert sha(ROOT/'book/coverage/modules.json')==sha(ROOT/'reports/full-coverage/checkpoint-27/book/coverage/modules.json')=='7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487'
I=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());H=json.loads((ROOT/'book/coverage/inventory-after-correction55.json').read_bytes())
BASE=json.loads((ROOT/'book/coverage/modules.json').read_bytes()); O=copy.deepcopy(BASE);plan=json.loads(PLAN.read_bytes())
BASECLAIMS={c['id']:c for e in BASE['exercises'] for c in e['claims']};BASECLAIMS.update({c['id']:c for c in BASE['material_claims']})
APP=json.loads((ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json').read_bytes());NATIVE=json.loads((ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json').read_bytes())
assert APP['status']=='passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending'
assert NATIVE['actual_exit_code']==0 and type(NATIVE['actual_exit_code']) is int and APP['coverage_complete'] is False
assert [r['correction_id'] for r in APP['applications']]==[56,57,58,59,60]
ex={r['key']:r for r in I['exercises']};oldex={r['key']:r for r in H['exercises']}
units={r['key']:r for r in I['material_source_units']};oldunits={r['key']:r for r in H['material_source_units']}
assert set(ex)==set(oldex) and set(units)==set(oldunits)
ownedex={k:r for k,r in ex.items() if r['source'] in O['scope_pages']};ownedunits={k:r for k,r in units.items() if r['source'] in O['scope_pages']}
assert len(ownedex)==217 and len(ownedunits)==4977
exchanged={k for k in ownedex if ex[k]['text_sha256']!=oldex[k]['text_sha256']}
unitchanged={k for k in ownedunits if units[k]['text_sha256']!=oldunits[k]['text_sha256']}
assert exchanged=={'lipsdp.html#book-m12-b1'} and unitchanged=={'verification.html::node-193','lipsdp.html::node-998'}
for row in plan['exercise_scope']:
 assert ex[row['inventory_key']]['text_sha256']==row['expected_text_sha256']
for row in plan['material_scope']:
 assert units[row['inventory_key']]['text_sha256']==row['expected_text_sha256']
for row in plan['proof_source_scope']:
 assert sha(row['original_tmp_proof']['file'])==row['original_tmp_proof']['sha256']
 assert not (ROOT/row['proposed_root_canonical_destination']).exists()
ident={'status':'prepared_exact_actual_current60_all_owned_literal_rebase_with_three_reviewed_changed_literals','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_frozen_owner27':ref(ROOT/'reports/full-coverage/checkpoint-27/book/coverage/modules.json'),'original_inventory55':ref(ROOT/'book/coverage/inventory-after-correction55.json'),'actual_inventory60':ref(ROOT/'book/coverage/inventory.json'),'actual_application':ref(ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json'),'actual_application_native':ref(ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json'),'owned_exercises':{k:{'original55_text_sha256':oldex[k]['text_sha256'],'actual60_text_sha256':v['text_sha256'],'unchanged_literal':k not in exchanged} for k,v in ownedex.items()},'owned_material_units':{k:{'original55_text_sha256':oldunits[k]['text_sha256'],'actual60_text_sha256':v['text_sha256'],'unchanged_literal':k not in unitchanged} for k,v in ownedunits.items()},'exact_changed_full_inventory_records':{'lipsdp.html#book-m12-b1':{'original55':oldex['lipsdp.html#book-m12-b1'],'actual60':ex['lipsdp.html#book-m12-b1']},**{k:{'original55':oldunits[k],'actual60':units[k]} for k in sorted(unitchanged)}},'conditional_prospective_peers_freshly_bound_to_actual_applied_literals':[{ 'inventory_key':r['inventory_key'],'expected_and_actual60_text_sha256':r['expected_text_sha256'],'unchanged_original_semantic_peer':r['whole_peer']} for r in plan['exercise_scope']+plan['material_scope'] if r['inventory_key'] in exchanged|unitchanged],'original_peer_timestamps_or_bodies_reinterpreted':False,'global_coverage_or_canonical_pair_or_owner_application_claimed':False}
IDENTITY.write_text(json.dumps(ident,indent=2,ensure_ascii=False)+'\n')
idref=ref(IDENTITY)
for e in O['exercises']:
 key=e['inventory_key'];u=ex[key]
 e['source60_literal_identity']=idref
 e['source_sha256']=u['source_sha256'];e['source_text_sha256']=u['text_sha256']
for c in O['material_claims']:
 assert all(k in ownedunits for k in c.get('source_unit_keys',[]))
 c['source60_literal_identity']=idref
 if c['id'] in {k+'::claim-review' for k in unitchanged}:
  assert c['status']=='pending' and len(c['source_unit_keys'])==1
  c['statement_in_prose']=units[c['source_unit_keys'][0]]['source_text']
O['source_sha256']={n:I['source_sha256'][n] for n in O['scope_pages']}
O['chapter_fragment_sha256']={n:sha(ROOT/n) for n in BASE['chapter_fragment_sha256']}
O['current_inventory']='book/coverage/inventory-after-correction60.json';O['current_inventory_sha256']=sha(ROOT/'book/coverage/inventory.json')
O['inventory_identity_rebase60']=idref
O['current_identity_binding_validation']={'status':'prepared_exact_current60_identity_candidate_pending_canonical_pair_and_owner_integration','inventory':ref(ROOT/'book/coverage/inventory.json'),'identity':idref,'canonical_owner_integrated':False}
changes=[]
def use_components(e,claim,groups,peer):
 original=copy.deepcopy(BASECLAIMS[claim['id']])
 claim['status']='proved';claim['lean_declarations']=list(dict.fromkeys(n for g in groups for n in g['lean_declarations']))
 assert claim['lean_declarations']
 claim['hypotheses']=list(dict.fromkeys(h for g in groups for h in g.get('hypotheses',[])))
 claim['correspondence']=' '.join(g['correspondence'] for g in groups)
 claim['remaining_gaps']=[];claim['independent_source_review']=peer
 claim['reviewed_owner28_transition']={'original_owner':ident['original_frozen_owner27'],'original_claim_id':original['id'],'original_claim_canonical_json_sha256':object_sha(original),'whole_exercise_full_literal_peer':peer,'canonical_pair_pending':True}
 changes.append({'id':claim['id'],'original_status':original['status'],'candidate_status':'proved'})
for row in plan['exercise_scope']:
 e=next(e for e in O['exercises'] if e['inventory_key']==row['inventory_key']);pending=[c for c in e['claims'] if c['status']=='pending']
 key=row['inventory_key'];groups=row.get('components',[])
 if key=='verification.html::exercise-15':mapping=[[0],[0,1],[2,3]]
 elif key=='verification.html::exercise-16':mapping=[[0,1,2,3],[]]
 elif key=='lipsdp.html#book-m12-b1':mapping=[[0],[0],[0,1,2,3],[1,2,3]]
 else:mapping=None
 if mapping is not None:assert len(pending)==len(mapping)
 for i,c in enumerate(pending):
  if key=='verification.html::exercise-16' and i==1:
   original=copy.deepcopy(BASECLAIMS[c['id']]);g=groups[-1];assert g['approved'] and g['lean_declarations']==[]
   c.update({'status':'not_a_formal_claim','kind':'explicitly_scoped_empirical_panel_verification','lean_declarations':[],'hypotheses':g['hypotheses'],'correspondence':g['correspondence'],'remaining_gaps':[],'independent_source_review':row['whole_peer']})
   c['reviewed_owner28_transition']={'original_owner':ident['original_frozen_owner27'],'original_claim_id':original['id'],'original_claim_canonical_json_sha256':object_sha(original),'actual_runtime_record':ref('/tmp/modules-crown-other-radii28-panel-a-actual-v2.json'),'actual_runtime_result':ref('/tmp/modules-crown-other-radii28-panel-a-result-v2.json')}
   changes.append({'id':c['id'],'original_status':original['status'],'candidate_status':c['status']})
  elif mapping is not None:use_components(e,c,[groups[j] for j in mapping[i]],row['whole_peer'])
  else:use_components(e,c,[{'lean_declarations':row['lean_declarations'],'hypotheses':row['hypotheses'],'correspondence':row['correspondence']}],row['whole_peer'])
 e['status']='complete_math';e['entire_literal_closure28']={'whole_exercise_approved':True,'remaining_gaps':[],'actual_current60_text_sha256':ex[key]['text_sha256'],'unchanged_original_semantic_peer':row['whole_peer'],'canonical_pair_and_owner_integration_pending':True}
for row in plan['material_scope']:
 key=row['inventory_key'];candidates=[c for c in O['material_claims'] if c['id']==key+'::claim-review']
 assert len(candidates)==1 and candidates[0]['status']=='pending' and candidates[0]['source_unit_keys']==[key]
 c=candidates[0];assert c['statement_in_prose']==units[key]['source_text']
 use_components(None,c,[row],row['whole_peer'])
 c['whole_current60_source_unit_approved']=True;c['actual_current60_text_sha256']=units[key]['text_sha256']
newdecls=[];pendingproofs=[]
for row in plan['proof_source_scope']:
 source=Path(row['original_tmp_proof']['file']);s=source.read_text();namespace=re.search(r'^namespace ([A-Za-z0-9_.]+)',s,re.M).group(1)
 matches=list(re.finditer(r'^theorem ([A-Za-z0-9_]+)',s,re.M));names=[]
 for m in matches:
  name=namespace+'.'+m.group(1);names.append(name)
  end=s.find(':=',m.end());assert end!=-1
  newdecls.append({'name':name,'file':row['proposed_root_canonical_destination'],'line':s.count('\n',0,m.start())+1,'statement':s[m.start():end].rstrip()})
 destination=row['proposed_root_canonical_destination'];assert destination not in O['proof_files']
 O['proof_files'][destination]={'sha256':row['original_tmp_proof']['sha256'],'selection_scope':'direct_reviewed_reference','standalone_compile_status':'pending_actual_root_canonical_pairs','declarations':names,'original_tmp_source':row['original_tmp_proof'],'original_tmp_trial':row['original_tmp_trial'],'canonical_pair_evidence_directory_assigned_by_root':'book/coverage/checks/future28-core/current60-canonical-pairs-v1/','canonical_paired_evidence_not_yet_available':True}
 pendingproofs.append({'canonical_source':destination,'sha256':row['original_tmp_proof']['sha256'],'public_theorem_count':len(names),'canonical_actual_pair_pending':True})
assert len(newdecls)==136 and not ({r['name'] for r in newdecls}&{r['name'] for r in BASE['declarations']})
O['declarations'].extend(newdecls)
O['counts']={'exercises':len(O['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in O['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in O['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in O['material_claims'])),'new_declarations':len(O['declarations'])}
assert O['counts']['exercise_status']=={'complete_math':187,'pending':19,'partial':11}
assert O['counts']['exercise_claim_status']=={'proved':744,'pending':108,'not_a_formal_claim':24}
assert O['counts']['material_claim_status']=={'not_a_formal_claim':536,'pending':3585,'proved':1079}
assert all(O['proof_files'][k]==v for k,v in BASE['proof_files'].items())
assert O['declarations'][:len(BASE['declarations'])]==BASE['declarations']
assert {c['id'] for c in O['material_claims']}=={c['id'] for c in BASE['material_claims']}
assert {c['id'] for e in O['exercises'] for c in e['claims']}=={c['id'] for e in BASE['exercises'] for c in e['claims']}
O['reviewed_work_integration28_current60_candidate']={'status':'prepared_independent_four_whole_exercises_and24_material_scope_pending_actual_canonical_pairs','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'scope_plan':ref(PLAN),'original_installed27_owner':ident['original_frozen_owner27'],'actual_source60_identity':idref,'changed_pending_claim_records':changes,'new_public_declarations':136,'pending_actual_canonical_pairs':pendingproofs,'old_proof_metadata_and_declarations_retained_exact':True,'live_owner_or_selection_or_aggregate_audit_or_publication_changed':False,'commissioning972_974_excluded_until_fresh_full17_peer':True}
O['generated_at_utc']=datetime.now(timezone.utc).isoformat();O['status']='prepared_current60_owner28_candidate_pending_actual_canonical_pairs_and_root_integration'
CAND.write_text(json.dumps(O,indent=2,ensure_ascii=False)+'\n')
report={'status':'prepared_current60_owner28_candidate_with_explicit_pending_canonical_pairs','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(CAND),'identity':idref,'original_owner':ident['original_frozen_owner27'],'actual_inventory60':ref(ROOT/'book/coverage/inventory.json'),'approved_scope_plan':ref(PLAN),'counts':O['counts'],'pending_pair_count':4,'new_public_declaration_count':136,'whole_exercises_proposed':4,'whole_material_units_proposed':24,'old_proof_metadata_and_original_declarations_retained_exact':True,'all_original_claim_ids_and_history_fields_retained':True,'source60_unchanged_owned_exercises':216,'source60_unchanged_owned_material_units':4975,'source60_changed_owned_exercises':1,'source60_changed_owned_material_units':2,'only_peer_approved_pending_claims_or_panel_reference_transitioned':True,'canonical_pair_evidence_or_kernel_or_owner_application_or_aggregate_or_publication_claimed':False,'changed_claims':changes}
REPORT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(ref(REPORT)));print(json.dumps(report['counts']))
