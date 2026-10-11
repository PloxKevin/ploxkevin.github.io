from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,collections,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
H=lambda n:hashlib.sha256((Path(n)if Path(n).is_absolute()else ROOT/n).read_bytes()).hexdigest()
J=lambda n:json.loads((Path(n)if Path(n).is_absolute()else ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def checkref(r):assert H(r['file'])==r['sha256'],r['file'];return J(r['file']) if r['file'].endswith('.json') else None
def zero(d):
 cs=[d[k]for k in ('actual_exit_code','exit_code')if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
O='book/coverage/checks/modules-future26/source53/modules-audit26-candidate-source53-additions-draft-v1.json';assert H(O)=='28d6ed6ca17028f20d69986d451f78c2734a737f4654a73536f9f2d5fb992119'
o=J(O);C=o['module_ledger'];assert H(C)==o['module_ledger_sha256']=='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231';c=J(C)
old=checkref(o['baseline25_module_ledger']);assert J('book/coverage/modules.json')==old
rebase=c['inventory_identity_rebase53'];c52=checkref(rebase['original_source52_candidate']);r=copy.deepcopy(c);r.pop('inventory_identity_rebase53');r.update(rebase['original_active_inventory_fields']);assert r==c52
identity=J(rebase['identity_binding']);assert identity['errors']==[] and identity['entire_owned_records_unchanged']
inv=J(o['current_inventory']);assert H(o['current_inventory'])==H('book/coverage/inventory.json')==o['current_inventory_sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
before=J('book/coverage/inventory-after-correction52.json');owned={}
for sec in ('exercises','material_source_units'):
 a={x['key']:x for x in before[sec]if x['source']in c['scope_pages']};b={x['key']:x for x in inv[sec]if x['source']in c['scope_pages']};assert a==b==identity['entire_owned_records_unchanged'][sec];owned[sec]=b
assert len(owned['exercises'])==217 and len(owned['material_source_units'])==4977
units=owned['material_source_units'];exs=owned['exercises'];li=c['reviewed_work_integration26_landscape_candidate'];ci=c['reviewed_work_integration26_combined_candidate']
lp=checkref(li['original_whole_review']);supp=checkref(li['physical_unit_supplement']);sp=checkref(ci['original_smoothing_whole_review']);assert lp['whole_exercise_approved'] is True and sp['whole_exercise_approved'] is True
assert li['entire_original_supplement_body_and_time']==supp and supp['entire_original_whole_peer_body_time_and_decisions_unchanged']==lp
assert ci['entire_original_smoothing_full_body_and_review_time']==sp
binding=checkref(o['canonical_original_full_smoothing44_review_body_binding_peer']);assert binding['errors']==[] and binding['entire_original_full_whole_source_review_body_and_time']==sp==o['entire_original_canonical_smoothing_binding_body_and_time']['entire_original_full_whole_source_review_body_and_time']
assert set(o['fresh_whole_exercise_keys'])=={'landscape.html::exercise-15','verification.html#practice-medium-3'}
# Exact mappings of every mathematical/nonformal clause, including per-key scopes.
for key,peer,groups,grouplabel,preservedlabel in [('landscape.html::exercise-15',lp,lp['eight_literal_clause_decisions'],'clause','entire_original_clause_body_and_review_time'),('verification.html#practice-medium-3',sp,sp['components'],'group','entire_original_component_body_and_review_time')]:
 e=next(e for e in c['exercises']if e['inventory_key']==key);old_e=next(e for e in old['exercises']if e['inventory_key']==key)
 assert e['prior_source52_pending_exercise_body_preserved26']==old_e and e['status']=='complete_math' and len(e['claims'])==len(groups)
 assert e['entire_original_whole_review_body_and_time_preserved26']==peer
 for claim,g in zip(e['claims'],groups):
  assert claim['lean_declarations']==g['lean_declarations'] and claim['hypotheses']==g['hypotheses'] and claim['correspondence']==g['reason'] and claim['statement_in_prose']==g[grouplabel]
  assert claim['remaining_gaps']==[] and claim['original_whole_review_time']==peer['reviewed_at_utc']
  assert any(v==g for v in claim.values())
 if key.startswith('verification'):assert sp['entire_exercise_record']==exs[key]
 else:assert lp['entire_inventory_record']==exs[key]
oldm={x['id']:x for x in old['material_claims']};newm={x['id']:x for x in c['material_claims']};assert len(newm)==len(c['material_claims'])
for unit in supp['material_units']:
 key=unit['source_unit_key'];assert unit['entire_inventory_record']==units[key] and unit['whole_literal_approved'] is True and unit['missing_clauses']==[]
 row=newm[key+('::claim-review'if key.endswith('1297')else'::source52-reviewed26-complete-literal')]
 assert row['entire_original_literal_decision_and_review_time']==unit and row['lean_declarations']==unit['lean_declarations'] and row['hypotheses']==unit['hypotheses'] and row['correspondence']==unit['reason'] and row['remaining_gaps']==[]
 assert row['entire_original_whole_review_body_and_time']==lp
 if key.endswith(('1285','1294')):assert newm[key+'::claim-review']==oldm[key+'::claim-review']
for unit in sp['material_units']:
 key=unit['source_unit_key'];assert unit['entire_inventory_record']==units[key] and unit['whole_unit_approved'] is True and unit['missing_clauses']==[]
 row=newm[key+'::claim-review'];assert row['prior_source52_pending_claim_body_preserved26']==oldm[row['id']]
 assert row['entire_original_literal_decision_and_review_time']==unit and row['lean_declarations']==unit['lean_declarations'] and row['hypotheses']==unit['hypotheses'] and row['correspondence']==unit['per_unit_reason'] and row['original_full_review_time']==sp['reviewed_at_utc']
 assert row['status']==unit['material_status'] and row['remaining_gaps']==[]
# Inverse restoration proves every unrelated body/proof/old declaration exact.
r=copy.deepcopy(c52)
for i,e in enumerate(r['exercises']):
 if e['inventory_key']in o['fresh_whole_exercise_keys']:r['exercises'][i]=copy.deepcopy(next(x for x in old['exercises']if x['inventory_key']==e['inventory_key']))
r['material_claims']=r['material_claims'][:len(old['material_claims'])]
changed=[]
for i,m in enumerate(r['material_claims']):
 if m!=old['material_claims'][i]:changed.append(m['id']);r['material_claims'][i]=copy.deepcopy(old['material_claims'][i])
assert len(changed)==7 and set(changed)=={'landscape.html::node-1297::claim-review'}|{u['source_unit_key']+'::claim-review'for u in sp['material_units']}
assert len(c['material_claims'])==len(old['material_claims'])+2==5200
for n,row in old['proof_files'].items():assert c['proof_files'][n]==row
r['proof_files']=copy.deepcopy(old['proof_files']);assert c['declarations'][:len(old['declarations'])]==old['declarations'];r['declarations']=copy.deepcopy(old['declarations'])
for k in ('generated_at_utc','counts','current_inventory','current_inventory_sha256'):r[k]=copy.deepcopy(old[k])
r.pop('reviewed_work_integration26_landscape_candidate');r.pop('reviewed_work_integration26_combined_candidate');assert r==old
assert len(old['proof_files'])==481 and len(old['declarations'])==3107
assert len(o['proof_files'])==2 and o['new_theorem_or_lemma_count']==48
public=[]
for n,row in o['proof_files'].items():
 assert H(n)==row['sha256']==c['proof_files'][n]['sha256']
 parsed=[d['name']for d in declarations((ROOT/n).read_text())if d['kind']in ('theorem','lemma')];assert parsed==row['declarations']==c['proof_files'][n]['declarations'];public+=parsed
 assert c['proof_files'][n]['actual_paired_records']==row['actual_paired_records'] and len(row['actual_paired_records'])==2
 for pair in row['actual_paired_records']:
  ar=checkref(pair['actual_record']);zero(ar);checkref(pair['raw_log']);checkref(pair['source_snapshot'])
  assert ar['source_sha256_before']==ar['source_sha256_after']==row['sha256'] and ar['source_unchanged'] is True
  command=ar.get('actual_command',ar.get('command'));expected=['lake','env','lean',n.removeprefix('verification/lean/')]if pair['kind']=='standalone'else['lake','build','SafeLearning.'+Path(n).stem];assert command==expected and ar['actual_workdir']==str(ROOT/'verification/lean')
  assert ar.get('log_sha256',ar.get('raw_log_sha256'))==pair['raw_log']['sha256']
 for p,h in row['evidence_sha256'].items():assert H(p)==h
assert len(public)==len(set(public))==48
for n,required in o['explicit_cross_owner_required_proofs'].items():
 offered=checkref(required['proof_offer']);assert offered['proof_files'][n]==required['proof_metadata'] and H(n)==required['sha256']
 assert c['proof_files'][n]['sha256']==required['sha256'] and n not in o['proof_files']
for n in set(c['proof_files'])-set(old['proof_files'])-set(o['proof_files'])-set(o['explicit_cross_owner_required_proofs']):assert n in o['reused_selected25_proof_sources_sha256'] and H(n)==o['reused_selected25_proof_sources_sha256'][n]
for d in c['declarations'][len(old['declarations']):]:assert d['name'] in {x['name']for x in declarations((ROOT/d['file']).read_text())}
for n,h in o['required_evidence_artifacts_sha256'].items():assert H(n)==h,n
assert len(o['required_evidence_artifacts_sha256'])==333
for r0 in [o['actual_builder'],o['actual_isolated_candidate_preparation']]:zero(checkref(r0))
checkref(o['actual_builder_raw_log']);assert H(o['module_builder'])==o['module_builder_sha256']
counts={'exercises':217,'exercise_status':dict(collections.Counter(e['status']for e in c['exercises'])),'exercise_claim_status':dict(collections.Counter(a['status']for e in c['exercises']for a in e['claims'])),'material_claim_status':dict(collections.Counter(m['status']for m in c['material_claims'])),'new_declarations':len(c['declarations'])};assert counts==c['counts']==o['counts']
manifest=J('reports/full-coverage/checkpoint-25-manifest.json');assert len(manifest['proof_files'])==1156
for n,row in manifest['proof_files'].items():assert H(n)==row['sha256']==H(manifest['snapshot']+'/'+n)
for n,h in manifest['frozen_inputs_sha256'].items():assert H(manifest['snapshot']+'/'+n)==h
for n,h in manifest['working_inputs_sha256'].items():
 if n.startswith('SafeLearning/') and n!='SafeLearning/lyapunov-mpc.html':assert H(n)==h
 if n in ['book/coverage/'+x+'.json'for x in ('core','foundations','applied','modules','applied-promotions')]:assert H(n)==h
out={'status':'passed_independent_isolated_module26_combined_source53_candidate_mechanics','errors':[],'reviewer':'independent_applied','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'offer':ref(O),'candidate':ref(C),'exact_source53_identity_inverse_restores_entire_source52_candidate':True,'exact_mathematical_inverse_restores_entire_installed25_module_ledger':True,'all217_and4977_entire_owned_records_unchanged52_to53':True,'original_Landscape_and_smoothing_full_bodies_times_hypotheses_reasons_preserved':True,'original_smoothing_canonical_binding':o['canonical_original_full_smoothing44_review_body_binding_peer'],'old_proof_metadata_rows':481,'old_declaration_prefix':3107,'other_exercises_exact':215,'old_material_bodies_exact_except_seven_pending_rows':5191,'two_prior_positive_material_atoms_exact':True,'Module_owned_new_sources':2,'Module_owned_public_exports':48,'explicit_Applied_cross_owned_CVaR_source':o['explicit_cross_owner_required_proofs'],'fresh_whole_exercise_keys':o['fresh_whole_exercise_keys'],'fresh_whole_material_unit_keys':o['fresh_whole_material_unit_keys'],'required_closed_artifact_count':333,'all1156_selected25_sources_and_all_frozen25_inputs_exact':True,'current30_unchanged_assets_exact_and_actual_authorized_Lyapunov53_scope_retained':True,'all_five_live25_owners_exact':True,'counts':counts,'scope':'Independent read-only mechanical correspondence and exact history/evidence/identity checks. No semantic redecision, compiler, live owner installation, aggregate26 or delivery claim.'}
p=Path('/tmp/module26-combined-source53-final-candidate-independent-applied-review-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed','peer':ref(str(p))}))
