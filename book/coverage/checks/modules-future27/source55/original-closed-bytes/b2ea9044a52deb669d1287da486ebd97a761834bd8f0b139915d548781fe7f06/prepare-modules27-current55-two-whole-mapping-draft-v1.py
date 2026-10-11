from pathlib import Path
from datetime import datetime,timezone
import collections,copy,hashlib,json,re,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/modules27-current55-two-whole-mapping-draft-v1');assert not BASE.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':str(n),'sha256':sha(n)}
LIVE='book/coverage/modules.json';LIVE_SHA='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231';INV='book/coverage/inventory-after-correction55.json';INV_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
PREP='/tmp/modules-conformal45-canonical-byte-history27-v3/conformal45-reviewed-source-and-history-preparation27-v3.json';PREP_SHA='d52eca2dcb4d7abd77732a56e8b80a181968ab18da3101ea73c2edb71215ecc2';PEER='/tmp/modules-conformal45-source55-independent-foundations-full-whole-review27-v1.json';PEER_SHA='554fcbf844cbb8ef0f79e2df86cc0a09a42e009e94408f416cdf61666dc5d3f5'
VPEER='/tmp/applied-viability16-actual42-independent-foundations-full-source-review27-v1.json';VPEER_SHA='7248d63a4dd8948d614cd567002b84db955c65af703fb3f55ce658ece9b121f5';SUPPLY='/tmp/applied-viability16-current55-proof-supply-v1/viability16-42-current55-whole-literal-proof-supply-v1.json';SUPPLY_SHA='3bf9a4668415ff29c31eb056aee6205fc6f398a9559c4fdef7d9961f90220079';VPREP='/tmp/applied-viability16-canonical-preparation27-v2/viability16-42-source-original-whole-review-canonical-preparation-v2.json'
APP='reports/full-coverage/source54-55-corrections-application-v1.json';APP_SHA='845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528';WRAP='reports/full-coverage/source54-55-corrections-application-execution-v1.json'
for n,h in [(LIVE,LIVE_SHA),(INV,INV_SHA),('book/coverage/inventory.json',INV_SHA),(PREP,PREP_SHA),(PEER,PEER_SHA),(VPEER,VPEER_SHA),(SUPPLY,SUPPLY_SHA),(APP,APP_SHA)]:assert sha(n)==h,n
old=read(LIVE);iv=read(INV);prep=read(PREP);peer=read(PEER);vp=read(VPEER);vs=read(SUPPLY);vprep=read(VPREP);app=read(APP);wrapper=read(WRAP)
for k in ['actual_exit_code','exit_code']:
 if k in wrapper:assert type(wrapper[k]) is int and wrapper[k]==0
log=wrapper.get('log',wrapper.get('raw_log'));lh=wrapper.get('log_sha256',wrapper.get('raw_log_sha256'));assert log and sha(log)==lh
assert peer['errors']==[] and peer['source55_virtual_exercise']['whole_exercise_approved'] is True and peer['source55_virtual_exercise']['missing_clauses']==[]
assert vp['errors']==[] and vp['exercise']['whole_exercise_approved'] is True and vp['exercise']['missing_clauses']==[]
assert prep['entire_original_full_whole_peer_body_and_time']==peer and vprep['entire_original_whole_source_peer_body_and_time']==vp
em={e['key']:e for e in iv['exercises']};um={u['key']:u for u in iv['material_source_units']}
old_iv_path='/tmp/modules-conformal45-canonical-byte-history27-v1/original-root/book/coverage/inventory.json';old_iv=read(old_iv_path);assert sha(old_iv_path)=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
old_em={e['key']:e for e in old_iv['exercises']};old_um={u['key']:u for u in old_iv['material_source_units']}
owned=set(old['scope_pages']);owned_ex=[e for e in old_iv['exercises'] if e['source'] in owned];owned_units=[u for u in old_iv['material_source_units'] if u['source'] in owned]
changes={}
for rows,index,field in [(owned_ex,em,'exercises'),(owned_units,um,'material_source_units')]:
 changed=[]
 for a in rows:
  b=index[a['key']];x=copy.deepcopy(a);y=copy.deepcopy(b);x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:changed.append(a['key'])
 changes[field]=changed
assert changes=={'exercises':['verification.html::exercise-17'],'material_source_units':['verification.html::node-1184']}
assert peer['source55_virtual_exercise']['entire_inventory_record']==em['verification.html::exercise-17']
assert vp['exercise']['entire_inventory_record']==em['viability.html::exercise-16']
units=peer['material_units']+vp['material_units'];keys=[u['source_unit_key'] for u in units]
assert len(keys)==len(set(keys))==8
for u in units:assert u['whole_unit_approved'] is True and u['missing_clauses']==[] and u['entire_inventory_record']==um[u['source_unit_key']]
sel=read('reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
manifest=read('reports/full-coverage/checkpoint-26-manifest.json');assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for row in app['applications']:assets[row['source_after']['file']]=row['source_after']['sha256']
protected={n:r['sha256'] for n,r in sel['proof_files'].items()};protected.update(assets)
for owner in ['core','foundations','applied','modules','applied-promotions']:
 n='book/coverage/'+owner+'.json';protected[n]=sha(n)
protected['book/coverage/inventory.json']=INV_SHA;protected['book/coverage/material-corrections.json']='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
for n,h in protected.items():assert sha(n)==h,n
out=copy.deepcopy(old);priorrows={};exdecisions=[('verification.html::exercise-17',peer['source55_virtual_exercise'],peer,ref(PEER),peer['source55_virtual_exercise']['reviewed_components']),('viability.html::exercise-16',vp['exercise'],vp,ref(VPEER),vp['precise_component_groups'])]
for key,decision,review,reviewref,groups in exdecisions:
 e=next(e for e in out['exercises'] if e['inventory_key']==key);prior=copy.deepcopy(e);priorrows[key]=prior;assert e['status']=='partial'
 claims=[]
 for i,g in enumerate(groups,1):
  assert g['missing_clauses']==[]
  claims.append({'id':key+'::current55-full-source27-complete-clause-'+str(i),'statement_in_prose':g['component_id'],'kind':'independently_reviewed_complete_current55_whole_exercise_clause','status':'proved','lean_declarations':copy.deepcopy(g['lean_declarations']),'hypotheses':copy.deepcopy(g['hypotheses']),'correspondence':g['per_component_reason'],'remaining_gaps':[],'source_unit_keys':[u['source_unit_key'] for u in units if u['entire_inventory_record']['source']==e['source']],'independent_source_review':reviewref,'entire_original_component_body_and_review_time':copy.deepcopy(g),'original_full_review_time':review['reviewed_at_utc']})
 e.update(status='complete_math',claims=claims,source_sha256=em[key]['source_sha256'],source_text_sha256=em[key]['text_sha256'],prior_installed26_partial_exercise_body_and_all_old_claims_preserved27=prior,independent_current55_full_source_review27=reviewref,entire_original_full_source_review_body_and_time_preserved27=copy.deepcopy(review),entire_original_whole_exercise_decision=copy.deepcopy(decision))
for u in units:
 k=u['source_unit_key'];row=next(c for c in out['material_claims'] if c['id']==k+'::claim-review');assert row['status']=='pending';prior=copy.deepcopy(row);priorrows[row['id']]=prior
 review=peer if k.startswith('verification.html') else vp;reviewref=ref(PEER) if k.startswith('verification.html') else ref(VPEER)
 row.update(statement_in_prose=um[k]['source_text'],kind='independently_reviewed_complete_current55_mathematical_source_unit',status='proved',lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],remaining_gaps=[],source_unit_keys=[k],independent_source_review=reviewref,entire_original_literal_decision_and_review_time=copy.deepcopy(u),original_full_review_time=review['reviewed_at_utc'],prior_installed26_pending_claim_body_preserved27=prior)
# These rows are explicit pending canonical plans, not fabricated paired successes.
proofplans=[]
for row in prep['sources']:
 proofplans.append({'canonical_source':row['intended_canonical_source'],'source_sha256':row['original_source']['sha256'],'exact_original_tmp_source':row['original_source'],'public_theorem_count':row['public_theorem_count'],'all_public_declarations':row['all_public_declarations'],'source_provider':'Modules27','original_true_tmp_standalone':row['original_true_tmp_standalone'],'whole_peer':ref(PEER)})
vrow=vprep['prospective_canonical_source'];proofplans.append({'canonical_source':vrow['intended_root_destination'],'source_sha256':vrow['sha256'],'exact_original_tmp_source':vp['proof_source'],'public_theorem_count':42,'all_public_declarations':vp['all_public_declarations'],'source_provider':'Applied27 explicit cross-owner supply selected only by Modules27','original_true_tmp_standalone':vprep['actual_original_standalone'],'whole_peer':ref(VPEER),'current55_whole_record_supply':ref(SUPPLY)})
assert len(proofplans)==4 and sum(p['public_theorem_count'] for p in proofplans)==87
for plan in proofplans:
 n=plan['canonical_source'];assert not path(n).exists() and n not in out['proof_files']
 assert sha(plan['exact_original_tmp_source']['file'])==plan['source_sha256']
 out['proof_files'][n]={'sha256':plan['source_sha256'],'proof_selection_owner':'Modules27 planned, not selected','source_provider':plan['source_provider'],'declarations':copy.deepcopy(plan['all_public_declarations']),'standalone_compile_status':'canonical_and_named_execution_pending','actual_paired_records':[],'original_passed_tmp_source_evidence':copy.deepcopy(plan['original_true_tmp_standalone']),'canonical_pair_execution_claimed':False}
 text=path(plan['exact_original_tmp_source']['file']).read_text()
 for name in plan['all_public_declarations']:
  assert name not in {d['name'] for d in out['declarations']}
  m=re.search(r'^theorem\s+'+re.escape(name.rsplit('.',1)[-1])+r'\b',text,re.M);assert m,name
  out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip(),'canonical_source_execution_pending':True})
for e0,e1 in zip(old['exercises'],out['exercises']):
 if e0['inventory_key'] not in [r[0] for r in exdecisions]:assert e0==e1
for c0,c1 in zip(old['material_claims'],out['material_claims']):
 if c0['id'] not in {k+'::claim-review' for k in keys}:assert c0==c1
for n,r in old['proof_files'].items():assert out['proof_files'][n]==r
assert out['declarations'][:len(old['declarations'])]==old['declarations']
oldfields={k:copy.deepcopy(old[k]) if k in old else None for k in ['generated_at_utc','source_sha256','current_inventory','current_inventory_sha256','counts']}
out['source_sha256']={n:iv['source_sha256'][n] for n in old['scope_pages']};out['current_inventory']=INV;out['current_inventory_sha256']=INV_SHA;out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
identity={'status':'prepared_exact_current55_owned_literal_identity_with_one_fresh_source55_scope_mapping','baseline_source53_inventory':ref(old_iv_path),'current_source55_inventory':ref(INV),'actual_source54_55_application':ref(APP),'actual_source54_55_execution':ref(WRAP),'entire_original_source_application_body_and_time':app,'owned_exercise_record_count':len(owned_ex),'owned_material_record_count':len(owned_units),'exact_changed_owned_literal_keys':changes,'all_other_owned_literal_records_equal_except_updated_verification_page_sha256':True,'original_full_owned_exercise_records':owned_ex,'current_full_owned_exercise_records':[em[e['key']] for e in owned_ex],'original_full_owned_material_records':owned_units,'current_full_owned_material_records':[um[u['key']] for u in owned_units],'preserved_original_top_level_fields':oldfields}
out['reviewed_current55_two_whole_mapping_draft27']={'status':'draft_math_mapping_approved_canonical_pairs_not_executed_not_integration_ready','baseline26_module_ledger':ref(LIVE),'source55_identity':identity,'original_conformal_whole_peer':ref(PEER),'entire_original_conformal_whole_review_body_and_time':peer,'original_viability_whole_peer':ref(VPEER),'entire_original_viability_whole_review_body_and_time':vp,'actual_current55_cross_owner_viability_supply':ref(SUPPLY),'entire_original_current55_viability_supply_body_and_time':vs,'original_two_whole_exercise_and_eight_pending_material_rows':priorrows,'planned_four_new_sources':proofplans,'new_source_count':4,'new_public_export_count':87,'fresh_whole_exercise_keys':[r[0] for r in exdecisions],'fresh_whole_material_unit_keys':keys,'old_other_exercise_bodies_exact':215,'old_other_material_bodies_exact':len(old['material_claims'])-8,'old_proof_rows_exact':len(old['proof_files']),'old_declaration_prefix_exact':len(old['declarations']),'canonical_pairs_required':8,'canonical_pairs_executed':0,'production_installation_ready':False,'installed_owner_mutation':False}
# Mechanical inverse includes every complete original partial claim and source53 identity.
inverse=copy.deepcopy(out);inverse.pop('reviewed_current55_two_whole_mapping_draft27')
for key,_,_,_,_ in exdecisions:
 idx=next(i for i,e in enumerate(inverse['exercises']) if e['inventory_key']==key);inverse['exercises'][idx]=priorrows[key]
for k in keys:
 cid=k+'::claim-review';idx=next(i for i,c in enumerate(inverse['material_claims']) if c['id']==cid);inverse['material_claims'][idx]=priorrows[cid]
for p in proofplans:inverse['proof_files'].pop(p['canonical_source'])
inverse['declarations']=inverse['declarations'][:len(old['declarations'])]
for k,v in oldfields.items():
 if k in old:inverse[k]=v
 else:inverse.pop(k,None)
assert inverse==old
for n,h in protected.items():assert sha(n)==h,n
BASE.mkdir(parents=True)
def put(name,d):p=BASE/name;p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');return ref(str(p))
candidate=put('modules27-current55-two-whole-mapping-draft-v1.json',out)
side=put('modules27-current55-owned-literal-identity-and-mapping-inputs-v1.json',identity)
commands=[{'source':p['canonical_source'],'source_provider':p['source_provider'],'standalone_command':['python3','book/coverage/check_core_standalone.py',Path(p['canonical_source']).stem],'named_command':['python3','book/coverage/check_core_named_build.py',Path(p['canonical_source']).stem],'execution_status':'not_executed','source_sha256':p['source_sha256']} for p in proofplans]
planning=put('modules27-current55-four-source-canonical-pair-planning-request-v1.json',{'status':'planned_only_current55_four_sources_eight_real_commands_required','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_mapping_draft':candidate,'source55_identity':side,'source_plans':proofplans,'command_plans':commands,'required_new_protected_runner_scope':'actual Source54+55/current55/five installed26 owners/all1167 selected26 sources/31 site assets','full_current55_source_reviews':[ref(PEER),ref(VPEER)],'current55_actual_source_application':ref(APP),'canonical_or_named_execution_count':0,'integration_ready':False,'scope':'Planning request only. Module owns both exercises and eight units. Three conformal sources are Module supplied; the fourth42-export source is explicitly Applied supplied and selected only once by Modules. Actual independent canonical byte/pair binding and final candidate mechanics remain required.'})
print(json.dumps({'status':'prepared_tmp_mapping_and_pair_plan_not_integration_ready','candidate':candidate,'identity':side,'pair_plan':planning,'new_sources':4,'new_exports':87,'fresh_wholes':2,'fresh_units':8,'original_inverse_exact':True,'counts':out['counts']}))
