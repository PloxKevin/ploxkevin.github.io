from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,collections,re
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules27-current55-two-whole-mapping-draft-v1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def path(n): return Path(n) if Path(n).is_absolute() else R/n
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':str(n),'sha256':sha(path(n))}
def checked(r):assert sha(path(r['file']))==r['sha256'],r;return read(r['file'])
def zero(x):
 a=[x[k] for k in ('actual_exit_code','exit_code') if k in x];assert a and all(type(v)is int and v==0 for v in a)
D=B/'modules27-current55-two-whole-mapping-draft-v1.json';I=B/'modules27-current55-owned-literal-identity-and-mapping-inputs-v1.json';P=B/'modules27-current55-four-source-canonical-pair-planning-request-v1.json'
assert sha(D)=='1926ee49a419d5c9ef97f9859767b7481652eb24f3a7f022f83c4d3a9a93455c'
assert sha(I)=='8b5373d686641fa9eecb876d2a90ba0fb3db53d19d0fe0f1d2427636260e1880'
assert sha(P)=='bca767b0a7f2b1c24a502ed81a3c84cae34940e0c80bc7537a7c52653a2bb71b'
d=read(D);i=read(I);p=read(P);s=d['reviewed_current55_two_whole_mapping_draft27'];old=checked(s['baseline26_module_ledger'])
assert s['baseline26_module_ledger']['sha256']=='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231'
assert s['source55_identity']==i and checked(p['candidate_mapping_draft'])==d and checked(p['source55_identity'])==i
iv=checked(i['current_source55_inventory']);assert i['current_source55_inventory']['sha256']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf';assert sha(R/'book/coverage/inventory.json')==i['current_source55_inventory']['sha256']
old_iv=checked(i['baseline_source53_inventory']);assert i['baseline_source53_inventory']['sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
app=checked(i['actual_source54_55_application']);actual=checked(i['actual_source54_55_execution']);zero(actual)
assert app==i['entire_original_source_application_body_and_time'];assert app['coverage_complete'] is False;assert sha(path(actual['log']))==actual['log_sha256'];assert actual['helper_sha256_before']==actual['helper_sha256_after']==app['helper']['sha256'];checked(app['helper']) if app['helper']['file'].endswith('.json') else None
assert actual['actual_workdir']==str(R) and actual['actual_command'][1]==app['helper']['file']
owned=set(old['scope_pages']);em={x['key']:x for x in iv['exercises']};um={x['key']:x for x in iv['material_source_units']}
changes={}
for field,oldrows,newrows,label in [('exercises',i['original_full_owned_exercise_records'],i['current_full_owned_exercise_records'],'exercises'),('material_source_units',i['original_full_owned_material_records'],i['current_full_owned_material_records'],'material_source_units')]:
 expected_old=[x for x in old_iv[field] if x['source'] in owned];expected_new=[x for x in iv[field] if x['source'] in owned]
 assert oldrows==expected_old and newrows==expected_new and len(oldrows)==len(newrows)
 dif=[]
 for a,b in zip(oldrows,newrows):
  assert a['key']==b['key'];aa=copy.deepcopy(a);bb=copy.deepcopy(b);aa.pop('source_sha256');bb.pop('source_sha256')
  if aa!=bb:dif.append(a['key'])
 changes[label]=dif
assert changes==i['exact_changed_owned_literal_keys']=={'exercises':['verification.html::exercise-17'],'material_source_units':['verification.html::node-1184']}
assert len(i['original_full_owned_exercise_records'])==i['owned_exercise_record_count']==217 and len(i['original_full_owned_material_records'])==i['owned_material_record_count']==4977
assert d['source_sha256']=={n:iv['source_sha256'][n] for n in old['scope_pages']}
peers=[checked(s['original_conformal_whole_peer']),checked(s['original_viability_whole_peer'])]
assert peers[0]==s['entire_original_conformal_whole_review_body_and_time'] and peers[1]==s['entire_original_viability_whole_review_body_and_time']
vs=checked(s['actual_current55_cross_owner_viability_supply']);assert vs==s['entire_original_current55_viability_supply_body_and_time'] and vs['errors']==[] and vs['entire_original_whole_peer_body_and_time']==peers[1]
assert vs['public_theorem_count']==42 and vs['canonical_standalone_execution'] is None and vs['canonical_named_execution'] is None
for peer in peers:assert peer['errors']==[] and peer['reviewed_at_utc']
exkeys=['verification.html::exercise-17','viability.html::exercise-16'];units=peers[0]['material_units']+peers[1]['material_units'];keys=[u['source_unit_key'] for u in units]
assert len(keys)==len(set(keys))==8 and keys==s['fresh_whole_material_unit_keys'] and exkeys==s['fresh_whole_exercise_keys']
prior=s['original_two_whole_exercise_and_eight_pending_material_rows'];assert len(prior)==10
for key,peer,decision,groups,reviewref in [(exkeys[0],peers[0],peers[0]['source55_virtual_exercise'],peers[0]['source55_virtual_exercise']['reviewed_components'],s['original_conformal_whole_peer']),(exkeys[1],peers[1],peers[1]['exercise'],peers[1]['precise_component_groups'],s['original_viability_whole_peer'])]:
 e=next(x for x in d['exercises'] if x['inventory_key']==key);o=next(x for x in old['exercises'] if x['inventory_key']==key)
 assert o['status']=='partial' and e['status']=='complete_math' and prior[key]==o==e['prior_installed26_partial_exercise_body_and_all_old_claims_preserved27']
 assert e['entire_original_full_source_review_body_and_time_preserved27']==peer and e['entire_original_whole_exercise_decision']==decision and decision['entire_inventory_record']==em[key]
 assert decision['whole_exercise_approved'] is True and decision['missing_clauses']==[] and len(e['claims'])==len(groups)
 for c,g in zip(e['claims'],groups):
  assert c['entire_original_component_body_and_review_time']==g and g['missing_clauses']==[]
  assert c['lean_declarations']==g['lean_declarations'] and c['hypotheses']==g['hypotheses'] and c['correspondence']==g['per_component_reason']
  assert c['status']=='proved' and c['remaining_gaps']==[] and c['independent_source_review']==reviewref and c['original_full_review_time']==peer['reviewed_at_utc']
for u in units:
 k=u['source_unit_key'];cid=k+'::claim-review';c=next(x for x in d['material_claims'] if x['id']==cid);o=next(x for x in old['material_claims'] if x['id']==cid);peer=peers[0] if k.startswith('verification') else peers[1]
 assert u['whole_unit_approved'] is True and u['missing_clauses']==[] and u['entire_inventory_record']==um[k]
 assert o['status']=='pending' and c['status']=='proved' and c['remaining_gaps']==[] and c['statement_in_prose']==um[k]['source_text']
 assert c['prior_installed26_pending_claim_body_preserved27']==prior[cid]==o and c['entire_original_literal_decision_and_review_time']==u
 assert c['lean_declarations']==u['lean_declarations'] and c['hypotheses']==u['hypotheses'] and c['correspondence']==u['per_unit_reason'] and c['original_full_review_time']==peer['reviewed_at_utc']
assert len(d['exercises'])==len(old['exercises'])==217 and len(d['material_claims'])==len(old['material_claims'])==5200
for a,b in zip(old['exercises'],d['exercises']):
 if a['inventory_key'] not in exkeys:assert a==b
for a,b in zip(old['material_claims'],d['material_claims']):
 if a['id'] not in {k+'::claim-review' for k in keys}:assert a==b
plans=s['planned_four_new_sources'];assert plans==p['source_plans'] and len(plans)==4 and sum(x['public_theorem_count'] for x in plans)==87
assert len(d['proof_files'])==len(old['proof_files'])+4
for n,x in old['proof_files'].items():assert d['proof_files'][n]==x
assert d['declarations'][:len(old['declarations'])]==old['declarations'] and len(d['declarations'])==len(old['declarations'])+87
newnames=[]
for plan,cmd in zip(plans,p['command_plans']):
 n=plan['canonical_source'];src=path(plan['exact_original_tmp_source']['file']);assert sha(src)==plan['source_sha256']==plan['exact_original_tmp_source']['sha256'] and not (R/n).exists()
 names=plan['all_public_declarations'];text=src.read_text();short=re.findall(r'^theorem\s+(\w+)',text,re.M)
 assert len(names)==len(short)==plan['public_theorem_count'] and [x.rsplit('.',1)[-1] for x in names]==short
 newnames+=names;r=d['proof_files'][n]
 assert r['declarations']==names and r['sha256']==plan['source_sha256'] and r['standalone_compile_status']=='canonical_and_named_execution_pending' and r['actual_paired_records']==[] and r['canonical_pair_execution_claimed'] is False
 tmp=plan['original_true_tmp_standalone'];tr=checked(tmp['record']);assert tr==tmp.get('entire_original_body_and_time',tmp.get('entire_actual_record'));zero(tr)
 assert tr['source_sha256_before']==tr['source_sha256_after']==tr['source_snapshot_sha256']==plan['source_sha256'] and tr['source_unchanged'] is True and sha(path(tr['source_snapshot']))==plan['source_sha256'] and sha(path(tr['raw_log']))==tr['raw_log_sha256']
 assert tr['actual_command']==['lake','env','lean',str(src)] and tr['actual_workdir']==str(R/'verification/lean')
 assert cmd['source']==n and cmd['source_sha256']==plan['source_sha256'] and cmd['execution_status']=='not_executed'
 assert cmd['standalone_command']==['python3','book/coverage/check_core_standalone.py',Path(n).stem] and cmd['named_command']==['python3','book/coverage/check_core_named_build.py',Path(n).stem]
 for name in names:
  x=next(x for x in d['declarations'] if x['name']==name);m=re.search(r'^theorem\s+'+name.rsplit('.',1)[-1]+r'\b',text,re.M)
  assert x=={'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip(),'canonical_source_execution_pending':True}
assert len(set(newnames))==87 and all(x not in {y['name'] for y in old['declarations']} for x in newnames)
assert all(name in {x['name'] for x in d['declarations']} for e in d['exercises'] if e['inventory_key'] in exkeys for c in e['claims'] for name in c['lean_declarations'])
for u in units:assert all(name in {x['name'] for x in d['declarations']} for name in u['lean_declarations'])
assert s['new_source_count']==4 and s['new_public_export_count']==87 and s['canonical_pairs_required']==8 and s['canonical_pairs_executed']==0 and s['production_installation_ready'] is False and s['installed_owner_mutation'] is False and p['canonical_or_named_execution_count']==0 and p['integration_ready'] is False
counts={'exercises':len(d['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in d['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in d['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in d['material_claims'])),'new_declarations':len(d['declarations'])};assert d['counts']==counts
inv=copy.deepcopy(d);inv.pop('reviewed_current55_two_whole_mapping_draft27')
for idx,e in enumerate(inv['exercises']):
 if e['inventory_key'] in exkeys:inv['exercises'][idx]=prior[e['inventory_key']]
for idx,c in enumerate(inv['material_claims']):
 if c['id'] in prior:inv['material_claims'][idx]=prior[c['id']]
for plan in plans:inv['proof_files'].pop(plan['canonical_source'])
inv['declarations']=inv['declarations'][:len(old['declarations'])]
for k,v in i['preserved_original_top_level_fields'].items():
 if k in old:inv[k]=v
 else:inv.pop(k,None)
assert inv==old
sel=read('reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
assets={n:h for n,h in read('reports/full-coverage/checkpoint-26-manifest.json')['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for row in app['applications']:assets[row['source_after']['file']]=row['source_after']['sha256']
protected={n:r['sha256'] for n,r in sel['proof_files'].items()}|assets
owners={'core':'1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38','foundations':'60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a','applied':'a0e087260288c8e8abc45eb0806eb3b09d17da463f5e918966c3a0686f3976a6','modules':'c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231','applied-promotions':'fa58595aacac0b82f9cd9d3bfe41718365113a2ebf76879001edcf3ab4b68fcb'}
protected.update({'book/coverage/'+n+'.json':h for n,h in owners.items()});protected['book/coverage/inventory.json']=i['current_source55_inventory']['sha256'];protected['book/coverage/material-corrections.json']='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
for n,h in protected.items():assert sha(R/n)==h,n
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Modules authored mapping draft and pair plan','candidate':ref(D),'source55_identity':ref(I),'pair_plan':ref(P),'author_preparer':ref('/tmp/prepare-modules27-current55-two-whole-mapping-draft-v1.py'),'original_author_execution_scope':'Author reports genuine exec tool0 only; no measured producer wrapper is claimed or invented.','entire_original_conformal_review_body_and_time':peers[0],'entire_original_viability_review_body_and_time':peers[1],'original_full_reviews_sha256':{s['original_conformal_whole_peer']['file']:s['original_conformal_whole_peer']['sha256'],s['original_viability_whole_peer']['file']:s['original_viability_whole_peer']['sha256']},'mechanics':{'entire_candidate_inverse_restores_installed26':True,'unchanged_other_exercises':215,'unchanged_other_material_claim_rows':5192,'unchanged_old_proof_metadata':491,'unchanged_old_declaration_prefix':3172,'new_source_count':4,'new_public_export_count':87,'fresh_whole_exercise_keys':exkeys,'fresh_whole_material_unit_keys':keys,'all_review_hypotheses_reasons_full_bodies_and_times_exact':True,'owned_entire_inventory_records':{'exercises':217,'material_units':4977},'owned_literal_changes':changes,'protected_selected_sources':1167,'protected_current55_assets':31,'protected_installed26_owners':5},'canonical_pair_execution_count':0,'integration_or_selection_approved':False,'semantic_redecision_or_retiming':False,'scope':'Exact read-only reversible TMP mapping and unexecuted pair-plan confirmation only. Current55 conformal whole peer and unchanged Viability full peer retain all original scopes; no fresh math inference. Canonical files absent, all eight planned genuine commands and subsequent independent binding/final mechanics remain required.'}
O=Path('/tmp/modules27-current55-two-whole-draft-independent-foundations-check-result-v2.json');assert not O.exists();O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','candidate_inverse_exact':True,'sources':4,'exports':87,'whole_exercises':2,'whole_units':8,'canonical_pairs_executed':0}))
