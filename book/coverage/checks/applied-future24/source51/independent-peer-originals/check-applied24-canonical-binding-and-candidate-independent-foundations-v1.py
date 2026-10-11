from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys,re
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/applied-future24/source51';TMP=Path('/tmp')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def bind(r):
 p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
OUT=TMP/'applied24-four-source29-canonical-binding-and-candidate-independent-foundations-review-v1.json';assert not OUT.exists()
op=BASE/'applied-audit24-candidate-source51-additions-v1.json';assert H(op)=='7c50224d67db64951bbd5c76fb4b482b986a4fe4a79d2a36cb2b506a1af9df26';o=read(op)
def ofile(f):
 p=path(o[f]);assert H(p)==o[f+'_sha256'];return p
ledgerp=ofile('mapped_ledger');promp=ofile('mapped_promotions');bp=ofile('original_review_bindings');alp=ofile('canonical_path_aliases');helper=ofile('candidate_builder')
ledger=read(ledgerp);prom=read(promp);b=read(bp);aliases=read(alp)['aliases']
assert b['canonical_original_path_aliases']==aliases and b['new_proof_files']==o['proof_files'] and b['actual_paired_records']==o['new_actual_paired_records']
for original,r in aliases.items():assert H(bind(r))==H(path(original)),original
for row in o['baseline23_owner_assets']:
 assert H(path(row['original']))==H(path(row['byte_exact_copy']))==row['sha256']
assert b['baseline23_history']==o['baseline23_owner_assets']
oldp=ROOT/'book/coverage/applied.json';oldpromp=ROOT/'book/coverage/applied-promotions.json';old=read(oldp);oldprom=read(oldpromp)
assert H(oldp)=='cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131'and H(oldpromp)=='64d40e98a0cb98cbb0e4355c38709a6a89b7d2822e982e34fc340dbc402fcdce'
invp=ofile('inventory');inv=read(invp);assert H(ROOT/'book/coverage/inventory.json')==H(invp)=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert bind(b['current_inventory'])==invp
assert b['exact_owned_exercise_records']==[e for e in inv['exercises']if e['source']in old['scope_pages']]
assert b['exact_owned_material_records']==[u for u in inv['material_source_units']if u['source']in old['scope_pages']]
assert len(b['exact_owned_exercise_records'])==128 and len(b['exact_owned_material_records'])==2059
reviews=[];semantic_rows={};expected=[('applied-total-variance-material24-three-literals-independent-foundations-review-v1.json','346051faf4e79616dfa0a0c44e33b9ab7403c8dd2c0e02b1ea1fea10f9bded1c'),('applied-mixture-material24-two-literals-independent-foundations-review-v1.json','7a56dbb31cc537a91f3fd26913c4b5521e9899590e5f7d2e789de9295d7db4ff'),('applied-mixture-covariance-material24-ensemble-independent-foundations-component-review-v2.json','a5574a575c2ca7ff0d422ff2369a6e070b66806afafd3c4b290aca0d242181b6')]
assert len(b['reviews'])==3
approved_source_bodies={}
for item,(name,h) in zip(b['reviews'],expected):
 p=TMP/name;assert H(p)==h;original=read(p);assert item['exact_original_body']==original and 'passed'in original['status']and original['errors']==[]
 assert bind(item['reference']).read_bytes()==p.read_bytes()and item['reference']['original_TMP_path']==str(p)and item['reference']['original_review_time']==original['reviewed_at_utc']and item['reference']['reviewer']==original['reviewer']
 reviews.append({'canonical_original_reference':item['reference'],'entire_original_semantic_body_and_time':original})
 for u in original['material_units']:assert u['source_unit_key']not in semantic_rows;semantic_rows[u['source_unit_key']]=(u,item['reference'])
 if 'entire_source_and_all_seven_bodies'in original:approved_source_bodies[hashlib.sha256(original['entire_source_and_all_seven_bodies'].encode()).hexdigest()]=original['entire_source_and_all_seven_bodies']
 if 'proof_packs'in original:
  for z in original['proof_packs']:approved_source_bodies[hashlib.sha256(z['entire_source_and_all_bodies'].encode()).hexdigest()]=z['entire_source_and_all_bodies']
 if 'entire_new_source_and_all_four_public_and_private_bodies'in original:approved_source_bodies[hashlib.sha256(original['entire_new_source_and_all_four_public_and_private_bodies'].encode()).hexdigest()]=original['entire_new_source_and_all_four_public_and_private_bodies']
assert len(approved_source_bodies)==4 and o['original_independent_review_references']==[i['reference']for i in b['reviews']]
units={u['key']:u for u in inv['material_source_units']};oldrows={k:c for c in old['material_claims']for k in c['source_unit_keys']};newrows={k:c for c in ledger['material_claims']for k in c['source_unit_keys']}
assert len(b['material_rows'])==6 and sorted(semantic_rows)==o['new_material_keys']
restored=copy.deepcopy(ledger);restoredprom=copy.deepcopy(prom)
for row in b['material_rows']:
 key=row['source_unit_key'];u,rr=semantic_rows[key];current=units[key];previous=oldrows[key];actual=newrows[key]
 assert row['entire_current51_inventory_record']==u['entire_inventory_record']==current
 assert row['original_complete_reviewed_row']==u and row['original_source_review']==rr and row['original_pending_claim']==previous and row['normalized_exact_ledger_claim']==actual
 assert previous['status']=='pending'and previous['source_unit_keys']==[key]and actual['preserved_entire_original_pending_claim']==previous
 assert H(path(current['source']))==current['source_sha256']and hashlib.sha256(current['source_text'].encode()).hexdigest()==current['text_sha256']
 for a,c in [('lean_declarations','lean_declarations'),('hypotheses','hypotheses'),('per_unit_reason','correspondence')]:assert u[a]==actual[c]
 assert actual['original_complete_literal_review_record']==u
 assert actual['source_review']=={**rr,'source_unit_key':key,'unit_text_sha256':current['text_sha256'],'inventory':o['inventory'],'inventory_sha256':o['inventory_sha256'],'classification_scope':u['per_unit_reason']}
 unchanged={k:v for k,v in previous.items()if k not in {'kind','status','remaining_gaps','lean_declarations','hypotheses','correspondence','approved_components'}}
 assert all(actual[k]==v for k,v in unchanged.items())
 if u['whole_unit_approved']:
  assert actual['kind']=='independently_reviewed_whole_mathematical_source_unit'and actual['status']=='proved'and actual['remaining_gaps']==u['missing_clauses']==[]
 else:
  assert key=='primer-probability.html::node-401'and actual['kind']=='independently_reviewed_mathematical_unit_partial_components'and actual['status']=='pending'and actual['remaining_gaps']==u['missing_clauses']and len(u['missing_clauses'])>0
  expected_components=[]
  for c in u['components']:
   assert c['missing_clauses']==c['remaining_gaps']==[]
   expected_components.append({'id':key+'::'+c['component_id'],'statement_in_prose':c['exact_component_literal'],'kind':'independently_reviewed_mathematical_component','status':'proved','lean_declarations':c['lean_declarations'],'hypotheses':c['hypotheses'],'correspondence':c['per_component_reason'],'remaining_gaps':[],'source_review':actual['source_review']})
  assert actual['approved_components']==expected_components and len(expected_components)==1
 normalized={k:v for k,v in actual.items()if k not in ['source','source_unit_keys','source_sha256','text_sha256']}
 assert prom['material'][key]=={'source_text_sha256':current['text_sha256'],'claim':normalized,'source_review':actual['source_review']}
 index=restored['material_claims'].index(actual);restored['material_claims'][index]=copy.deepcopy(previous)
 if key in oldprom['material']:restoredprom['material'][key]=copy.deepcopy(oldprom['material'][key])
 else:del restoredprom['material'][key]
assert sum(u['whole_unit_approved']for u,rr in semantic_rows.values())==5
assert old['exercises']==ledger['exercises']and len(ledger['exercises'])==128
assert len(old['proof_files'])==298 and len(ledger['proof_files'])==302
new=o['proof_files'];assert len(new)==4
for p,z in new.items():assert restored['proof_files'].pop(p)==z['sha256']
restored.pop('current24_material_candidate_integration');restored['generated_at_utc']=old['generated_at_utc'];assert restored==old
restoredprom.pop('current24_material_candidate_integration');assert restoredprom==oldprom
assert ledger['current24_material_candidate_integration']==prom['current24_material_candidate_integration']
ready_path=ROOT/'book/coverage/checks/applied-future24/four-material24-canonical-paired-build-readiness-v1.json';ready=read(ready_path)
assert ready['status']=='passed_genuine_four_canonical_standalone_and_named_pairs_unselected_future24'and ready['public_theorem_count']==29 and ready['actual_canonical_execution_count']==8 and len(ready['proof_sources'])==4
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
all_names=set();pairs=[];source_bindings=[]
for z in ready['proof_sources']:
 p=bind(z['source']);snapshot=bind(z['source_snapshot']);h=z['source']['sha256'];assert p.read_bytes()==snapshot.read_bytes()==path(z['original_TMP_source']).read_bytes()
 assert p.read_text()==approved_source_bodies[h]and not re.search(r'\b(sorry|admit|axiom)\b',p.read_text())
 names=[d['name']for d in declarations(p.read_text())if d['kind']in['theorem','lemma']];assert names==z['public_theorem_names']and len(names)==z['public_theorem_count'];all_names.update(names)
 row=new[z['source']['file']];assert row['sha256']==h and row['theorem_count']==len(names)and row['mapped_named_declarations']==names
 for n,d in row['evidence_sha256'].items():assert H(path(n))==d
 for index,pair in enumerate(z['actual_canonical_pair']):
  rp=bind(pair['record']);a=read(rp);assert a==pair['entire_original_actual_record']and a['exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==h and a['source']==z['source']['file']
  cmd=['lake','env','lean',z['source']['file'].removeprefix('verification/lean/')]if index==0 else['lake','build',z['source']['file'].removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')]
  assert a['command']==cmd and a['actual_workdir']==str(ROOT/'verification/lean')and H(path(a['log']))==a['log_sha256']
  assert bind(pair['raw_log'])==path(a['log'])and bind(pair['source_snapshot']).read_bytes()==p.read_bytes()
  assert row['evidence_sha256'][pair['record']['file']]==H(rp)and row['evidence_sha256'][a['log']]==a['log_sha256']
  prefix='standalone'if index==0 else'named';assert row[prefix+'_evidence']==pair['record']['file']and row[prefix+'_evidence_sha256']==H(rp)
  pairs.append({'record':pair['record'],'entire_original_body_and_time':a,'raw_log':pair['raw_log'],'source_snapshot':pair['source_snapshot']})
 source_bindings.append({'canonical_source':z['source'],'original_TMP_source':z['original_TMP_source'],'entire_original_source_and_all_bodies':p.read_text(),'public_names':names})
assert len(all_names)==29 and len(pairs)==8 and {a['file']:a['sha256']for a in o['new_actual_paired_records']}=={z['record']['file']:z['record']['sha256']for z in pairs}
for item in o['new_actual_paired_records']:assert read(bind(item))==item['entire_original_record']
manifestp=ofile('base_selection');manifest=read(manifestp);assert len(manifest['proof_files'])==1131
base_names=set()
for n,z in manifest['proof_files'].items():
 assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==z['sha256'];base_names.update(d['name']for d in declarations((ROOT/n).read_text()))
for u,rr in semantic_rows.values():assert set(u['lean_declarations'])<=all_names|base_names
assets={n:d for n,d in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,d in assets.items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==d
for name in ['core','foundations','applied','modules','applied-promotions']:
 n='book/coverage/'+name+'.json';assert H(ROOT/n)==manifest['working_inputs_sha256'][n]
for n,d in o['source_sha256'].items():assert H(ROOT/n)==d
actualp=ROOT/'book/coverage/checks/applied-future24/applied24-isolated-material-candidate-actual-v1.json';actual=read(actualp)
assert H(actualp)=='316d76de1d9fddaf76f99c842de42bf055c6bb72302c4201624544331bdc2938'and actual['actual_exit_code']==0 and actual['actual_command']==['python3',o['candidate_builder']]and actual['actual_workdir']==str(ROOT)
assert actual['helper_sha256_before']==actual['helper_sha256_after']==H(helper)and H(path(actual['log']))==actual['log_sha256']and H(path(actual['actual_runner']))==actual['actual_runner_sha256']
outer=ROOT/'book/coverage/checks/applied-future24/four-material24-outer-actual-runner-original-byte-aliases-v1.json';assert H(outer)=='d6906a3558b1325897b4667ef2aae0414fdc4589413470eeca6fe2d9cef7c3b0'
for n,r in read(outer)['aliases'].items():assert H(bind(r))==H(path(n))
assert read(outer)['aliases'][actual['actual_runner']]['sha256']==actual['actual_runner_sha256']
report={'status':'passed_independent_four_source29_export_canonical_original_body_binding_and_exact_five_whole_one_partial_applied24_candidate_mechanics','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':ref(Path(__file__)),'candidate_offer':ref(op),'candidate_ledger':ref(ledgerp),'candidate_promotions':ref(promp),'exact_row_bindings':ref(bp),'exact_original_path_aliases':ref(alp),'original_semantic_review_bodies_and_times':reviews,'canonical_sources_original_full_bodies_and_public_names':source_bindings,'eight_actual_canonical_records_with_original_times_and_raw_logs':pairs,'actual_original_candidate_builder_record_and_time':actual,'actual_original_candidate_builder':ref(helper),'actual_original_candidate_raw_log':ref(path(actual['log'])),'outer_runner_original_byte_aliases':ref(outer),'all128_whole_exercise_bodies_and468_prior_claims_exact':True,'all298_unpruned_baseline_proof_rows_including_three_unused_metadata_exact':True,'all_other1948_material_claim_bodies_exact':True,'exact_original_semantic_reasons_hypotheses_names_review_times_and_missing_clauses':True,'reversing_exact_six_changes_and_four_proof_rows_restores_entire_ledger_and_promotions':True,'whole_approved_material_units':5,'partial_component_only_unit':'primer-probability.html::node-401','whole401_remains_pending':True,'new_public_exports':29,'all1131_frozen23_sources31_assets_current51_and_five_live_owners_exact':True,'errors':[],'coverage_complete':False,'scope':'Narrow original semantic body/canonical-source/actual pair binding plus isolated candidate mechanics only. Original three full semantic reviews and decisions/time retained exact; no semantic redecision, compiler rerun, live mapping, checkpoint24 selection/aggregate/publication or whole401 Gaussian tail closure inferred.'}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'whole_units':5,'partial_units':1,'new_sources':4,'exports':29,'genuine_original_pairs':8}))
