from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
H=lambda p:hashlib.sha256((Path(p) if Path(p).is_absolute() else R/p).read_bytes()).hexdigest()
J=lambda p:json.loads((Path(p) if Path(p).is_absolute() else R/p).read_text())
O='book/coverage/checks/modules-future24/source51/modules-audit24-candidate-source51-additions-draft-v1.json';assert H(O)=='9be35fa54142f1a31fedb8f02af27dcfed18625fb6403bc39ca92d1867883979'
o=J(O)
def chkref(r):assert H(r['file'])==r['sha256'],r;return J(r['file']) if r['file'].endswith('.json') else (R/r['file']).read_text()
i=chkref(o['candidate_input_bindings']);g=chkref(o['candidate_binding_integrity']);assert g['errors']==[]
assert H(o['module_builder'])==o['module_builder_sha256']=='a0d3d35cdec6f0b2c5bb4afe6e558784f067c4a68a1095a757de7ef5b67b2a39'
a=chkref(o['actual_builder']);chkref(o['actual_builder_raw_log']);assert a['actual_exit_code']==0
assert a['actual_command']==['python3',o['module_builder']] and a['actual_workdir']==str(R)
assert a['actual_helper_sha256_before']==a['actual_helper_sha256_after']==o['module_builder_sha256']
assert H(a['raw_log'])==a['raw_log_sha256']==o['actual_builder_raw_log']['sha256']
assert H(o['module_ledger'])==o['module_ledger_sha256'];new=J(o['module_ledger']);old=chkref(i['baseline23_module_ledger'])
assert H('book/coverage/modules.json')==i['baseline23_module_ledger']['sha256']=='448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367'
assert J('book/coverage/modules.json')==old
for p,h in i['protected_owner_inventory_and31_asset_sha256'].items():assert H(p)==h,p
assert H(o['current_inventory'])==H('book/coverage/inventory.json')==o['current_inventory_sha256']
inv=J(o['current_inventory']);es={r['key']:r for r in inv['exercises']};us={r['key']:r for r in inv['material_source_units']}
selection=chkref(o['baseline23_selection']);assert selection['proof_file_count']==1131
for p,r in selection['proof_files'].items():assert H(p)==r['sha256'],p
for p,h in o['required_evidence_artifacts_sha256'].items():assert H(p)==h,p
aliases=chkref(o['canonical_path_aliases'])['aliases']
for p,r in aliases.items():
 assert H(r['file'])==r['sha256'],p
 if Path(p).exists():assert H(p)==r['sha256'],p
reviews=[]
for r,field in zip(i['original_source_reviews'],['entire_original_nine_body_review_and_time','entire_original_seven_bridge_review_and_time']):
 rv=chkref(r);assert rv==i[field] and rv['reviewed_at_utc']==r['original_review_time'] and rv['errors']==[]
 assert rv['exercise']['entire_inventory_record']==es[i['partial_exercise_key']] and not rv['exercise']['whole_exercise_approved']
 for u in rv['material_units']:assert u['entire_inventory_record']==us[u['source_unit_key']]
 reviews.append(rv)
binding=chkref(i['canonical_binding_peer']);assert binding['errors']==[] and binding['new_public_export_count']==16
assert binding['entire_original_nine_body_semantic_review_and_time']==reviews[0]
assert binding['entire_original_seven_bridge_semantic_review_and_time']==reviews[1]
na=i['explicit_old_to_new_three_declaration_names'];assert na==o['explicit_old_to_new_three_declaration_names'] and len(na)==3
mapped=lambda names:[na.get(n,n) for n in names]
key=i['partial_exercise_key'];olde={x['inventory_key']:x for x in old['exercises']};newe={x['inventory_key']:x for x in new['exercises']};assert set(olde)==set(newe) and len(olde)==217
for k,e in olde.items():
 if k!=key:assert e==newe[k],k
ex=newe[key];baseline=olde[key];assert baseline['status']=='pending' and ex['status']=='partial'
assert ex['claims'][:len(baseline['claims'])]==baseline['claims']
reverse=copy.deepcopy(ex);reverse['claims']=baseline['claims'];reverse['status']='pending';reverse.pop('independent_component_source_reviews24');reverse.pop('remaining_whole_source_gaps24');assert reverse==baseline
sourcegroups=[(0,c) for c in reviews[0]['exercise']['reviewed_components']]+[(1,c) for c in reviews[1]['approved_components']]
extra=ex['claims'][len(baseline['claims']):];assert len(extra)==len(sourcegroups)==12
for atom,(index,c) in zip(extra,sourcegroups):
 assert atom['entire_original_component_body']==c
 assert atom['status']=='proved' and atom['remaining_gaps']==[] and c['missing_clauses']==[] and c['remaining_gaps']==[]
 assert atom['lean_declarations']==mapped(c['lean_declarations']) and atom['hypotheses']==c['hypotheses']
 assert atom['statement_in_prose']==atom['correspondence']==c['per_component_reason']
 assert atom['independent_source_review']==i['original_source_reviews'][index]
 assert atom['explicit_declaration_namespace_aliases']==na and atom['canonical_source_binding_peer']==i['canonical_binding_peer']
assert ex['remaining_whole_source_gaps24']==reviews[1]['exercise']['remaining_gaps'] and ex['remaining_whole_source_gaps24']
oldm={x['id']:x for x in old['material_claims']};nm={x['id']:x for x in new['material_claims']}
changed={f'nn-in-the-loop.html::node-{n}::claim-review' for n in [1254,1258,1260,1262]}
assert len(oldm)==5183 and len(nm)==5195
for k,r in oldm.items():
 if k not in changed:assert nm[k]==r,k
 else:
  t=nm[k];assert t['prior_source51_claim_body_preserved']==r
  if 'node-1258::' in k:
   u=next(u for u in reviews[0]['material_units'] if u['source_unit_key']=='nn-in-the-loop.html::node-1258')
   assert u['whole_unit_approved'] and u['missing_clauses']==[]
   assert t['status']=='proved' and t['lean_declarations']==mapped(u['lean_declarations']) and t['hypotheses']==u['hypotheses']
   assert t['correspondence']==u['per_unit_reason'] and t['remaining_gaps']==[]
  else:
   index=1 if k.endswith(('1254::claim-review','1262::claim-review')) else 0
   u=next(u for u in reviews[index]['material_units'] if u['source_unit_key']+'::claim-review'==k)
   assert t['status']=='pending' and t['remaining_gaps']==u['missing_clauses'] and t['remaining_gaps']
   assert t['lean_declarations']==r['lean_declarations'] and t['hypotheses']==r['hypotheses']
newm=[x for x in new['material_claims'] if x['id'] not in oldm];assert len(newm)==12
for t,c in zip(newm,extra):
 z=copy.deepcopy(t);z['id']=c['id'];assert z==c
assert new['declarations'][:len(old['declarations'])]==old['declarations']
for p,row in old['proof_files'].items():assert new['proof_files'][p]==row,p
assert len(old['proof_files'])==475 and len(new['proof_files'])==478
allnames=[];newfiles=set(o['proof_files']);assert newfiles==set(new['proof_files'])-set(old['proof_files']) and len(newfiles)==3
for p,pr in o['proof_files'].items():
 assert H(p)==pr['sha256']==new['proof_files'][p]['sha256'];text=(R/p).read_text()
 names=[d['name'] for d in declarations(text) if d['kind'] in ('theorem','lemma')];assert names==pr['declarations']==new['proof_files'][p]['declarations'];allnames+=names
 for pair,cmd in zip(pr['actual_paired_records'],[['lake','env','lean','SafeLearning/'+Path(p).name],['lake','build','SafeLearning.'+Path(p).stem]]):
  ar=chkref(pair['actual_record']);chkref(pair['raw_log']);chkref(pair['source_snapshot'])
  assert ar==pair['entire_original_actual_record_body_and_time'] and ar['actual_exit_code']==0
  assert ar['actual_command']==cmd and ar['actual_workdir']==str(R/'verification/lean')
  assert ar['source']==p and ar['source_sha256_before']==ar['source_sha256_after']==H(p)==pair['source_snapshot']['sha256']
  assert ar['raw_log_sha256']==pair['raw_log']['sha256']
 for imported in re.findall(r'^import\s+(SafeLearning\.\S+)',text,re.M):
  q='verification/lean/'+imported.replace('.','/')+'.lean';assert H(q)==i['required_safelearning_import_sha256'][q]
  if q not in newfiles:assert q in selection['proof_files'] and selection['proof_files'][q]['sha256']==H(q)
assert len(allnames)==len(set(allnames))==16
for c in extra:assert set(c['lean_declarations'])<=set(allnames)
for p,h in i['protected_owner_inventory_and31_asset_sha256'].items():assert H(p)==h,p
assert H(O)=='9be35fa54142f1a31fedb8f02af27dcfed18625fb6403bc39ca92d1867883979'
out=Path('/tmp/module24-tanh-candidate-independent-applied-confirmation-v1.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_independent_exact_isolated_module24_tanh_candidate_mechanics','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'offer':{'file':O,'sha256':H(O)},'candidate':{'file':o['module_ledger'],'sha256':H(o['module_ledger'])},'input_bindings':o['candidate_input_bindings'],'original_semantic_reviews_and_times':i['original_source_reviews'],'canonical_original_body_binding_peer':i['canonical_binding_peer'],'all_original_component_bodies_hypotheses_reasons_scope_and_reviewtimes_exact':True,'counts':{'unchanged_exercises':216,'original_exercise_requirements_retained':len(baseline['claims']),'new_precise_exercise_components':12,'unchanged_material_bodies':5179,'new_whole_material_units':1,'partial_material_rows_retained_pending':3,'new_material_components':12,'old_proof_rows':475,'new_sources':3,'new_distinct_public_theorems':16,'actual_paired_records':6,'closed_required_artifacts':len(o['required_evidence_artifacts_sha256']),'original_byte_aliases':len(aliases),'protected_selected23_sources':1131},'explicit_three_namespace_aliases':na,'no_temporal_future25_selection':True,'scope':'Mechanical correspondence only against already independent full/precise original semantics. Only1258 whole; Exercise20 partial and1254/1260/1262 whole pending. No new mathematical decision/compiler run/live/global/aggregate/publication result.','checker':{'file':str(Path(__file__)),'sha256':H(Path(__file__))}},indent=2)+'\n');print(out,H(out))
