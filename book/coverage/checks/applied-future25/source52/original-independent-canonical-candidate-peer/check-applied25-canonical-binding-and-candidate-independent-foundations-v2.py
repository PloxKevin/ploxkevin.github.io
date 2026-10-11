"""Narrow original semantic preservation, actual canonical evidence, and isolated mechanics."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys,re
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/applied-future25';TMP=Path('/tmp')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def bind(r):
 p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
OUT=TMP/'applied25-seven-source43-canonical-binding-and-candidate-independent-foundations-review-v2.json';assert not OUT.exists()
op=BASE/'source52/applied-audit25-candidate-source52-additions-v1.json';assert H(op)=='65e1ec899aa568ad7dae18d88bcda3d1914ac317258f9c9c844b4aee00dd34e3';o=read(op)
def ofile(f):
 p=path(o[f]);assert H(p)==o[f+'_sha256'];return p
ledgerp=ofile('mapped_ledger');promp=ofile('mapped_promotions');bp=ofile('original_review_bindings');alp=ofile('canonical_path_aliases');helper=ofile('candidate_builder')
ledger=read(ledgerp);prom=read(promp);b=read(bp);aliases=read(alp)['aliases']
assert b['canonical_original_path_aliases']==aliases and b['new_proof_files']==o['proof_files'] and b['actual_paired_records']==o['new_actual_paired_records']
for original,r in aliases.items():
 bind(r)
 if original.startswith('/tmp/'):assert H(path(original))==r['sha256'],original
for row in o['baseline24_owner_assets']:assert H(path(row['original']))==H(path(row['byte_exact_copy']))==row['sha256']
assert b['baseline24_history']==o['baseline24_owner_assets']
oldp=ROOT/'book/coverage/applied.json';oldpromp=ROOT/'book/coverage/applied-promotions.json';old=read(oldp);oldprom=read(oldpromp)
assert H(oldp)=='b869af52ff5db1e39b3971cdeb32e1afae4aa87f69c59af31f599e897066464d'and H(oldpromp)=='5d28d3d8bbcbfa0a7b96dce7b27c63ff4f55dd7f785568c8d44f6acf319815e3'
invp=ofile('inventory');inv=read(invp);assert H(ROOT/'book/coverage/inventory.json')==H(invp)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert bind(b['current_inventory'])==invp
assert b['exact_owned_exercise_records']==[e for e in inv['exercises']if e['source']in old['scope_pages']]
assert b['exact_owned_material_records']==[u for u in inv['material_source_units']if u['source']in old['scope_pages']]
assert len(b['exact_owned_exercise_records'])==128 and len(b['exact_owned_material_records'])==2059
reviews=[];semantic_rows={};expected=[('applied-gaussian-mixture401-independent-foundations-full-source-review-v2.json','7a06bc6b2c9d3f78411468c1da48e3c9aa58a51a729d07f3ac21013150ddb727'),('applied-conditioning-alarm25-independent-foundations-full-source-review-v2.json','9b7c9ef7ff7e4acfc2d8649a19119884025693a392307a0b3640bf26e9b26751'),('applied-truncated-conditioning25-independent-foundations-full-source-review-v2.json','a737f8f6d7abbb31e4e697f68839ad5a75fee44256bf7ceb7c7cc954ffcc6e13')]
assert len(b['reviews'])==3
for item,(name,h)in zip(b['reviews'],expected):
 p=TMP/name;assert H(p)==h;original=read(p);assert item['exact_original_body']==original and 'passed'in original['status']and original['errors']==[]
 assert bind(item['reference']).read_bytes()==p.read_bytes()and item['reference']['original_TMP_path']==str(p)and item['reference']['original_review_time']==original['reviewed_at_utc']and item['reference']['reviewer']==original['reviewer']
 reviews.append({'canonical_original_reference':item['reference'],'entire_original_semantic_body_and_time':original})
 for u in original['material_units']:
  key=u['entire_inventory_record']['key'];assert key not in semantic_rows;semantic_rows[key]=(u,item['reference'])
assert o['original_independent_review_references']==[i['reference']for i in b['reviews']]
units={u['key']:u for u in inv['material_source_units']};oldrows={k:c for c in old['material_claims']for k in c['source_unit_keys']};newrows={k:c for c in ledger['material_claims']for k in c['source_unit_keys']}
assert len(b['material_rows'])==11 and sorted(semantic_rows)==o['new_material_keys']
restored=copy.deepcopy(ledger);restoredprom=copy.deepcopy(prom);whole_count=0;component_count=0
component_literals={'conditional_event_ratio':r'$\mathbb P(A\mid B)=\mathbb P(A\cap B)/\mathbb P(B)$','conditional_event_product':r'$\mathbb P(A\cap B)=\mathbb P(A\mid B)\mathbb P(B)$','finite_partition_total_probability':r'$\mathbb P(A)=\sum_j\mathbb P(A\mid B_j)\mathbb P(B_j)$','finite_partition_Bayes':r'$\mathbb P(B_i\mid A)=\mathbb P(A\mid B_i)\mathbb P(B_i)/\sum_j\mathbb P(A\mid B_j)\mathbb P(B_j)$'}
for row in b['material_rows']:
 key=row['source_unit_key'];u,rr=semantic_rows[key];current=units[key];previous=oldrows[key];actual=newrows[key]
 assert row['entire_current52_inventory_record']==u['entire_inventory_record']==current
 assert row['original_complete_reviewed_row']==u and row['original_source_review']==rr and row['original_pending_claim']==previous and row['normalized_exact_ledger_claim']==actual
 assert previous['status']=='pending'and previous['source_unit_keys']==[key]and actual['preserved_entire_original_pending_claim']==previous
 assert H(path(current['source']))==current['source_sha256']and hashlib.sha256(current['source_text'].encode()).hexdigest()==current['text_sha256']
 whole=u['whole_source_unit_approved']if'whole_source_unit_approved'in u else u['whole_unit_approved']
 if whole:
  declarations=u['lean_declarations'];hyp=u['hypotheses'];reason=u.get('per_unit_reason',u.get('per_component_reason'));whole_count+=1
  assert actual['kind']=='independently_reviewed_whole_mathematical_source_unit'and actual['status']=='proved'and actual['remaining_gaps']==u['missing_clauses']==[]
 else:
  assert key=='primer-probability.html::node-371'and actual['kind']=='independently_reviewed_mathematical_unit_partial_components'and actual['status']=='pending'and actual['remaining_gaps']==u['remaining_gaps']and u['remaining_gaps']
  declarations=list(dict.fromkeys(d for c in u['components']for d in c['lean_declarations']));hyp=list(dict.fromkeys(h for c in u['components']for h in c['hypotheses']));reason='Four actual event conditioning/finite-partition formulas are independently approved; generic joint-density conditional and marginal clauses remain pending.'
  components=[]
  for c in u['components']:
   assert c['missing_clauses']==[]
   components.append({'id':key+'::'+c['component_id'],'statement_in_prose':component_literals[c['component_id']],'kind':'independently_reviewed_mathematical_component','status':'proved','lean_declarations':c['lean_declarations'],'hypotheses':c['hypotheses'],'correspondence':c['per_component_reason'],'remaining_gaps':[],'source_review':actual['source_review']})
  assert actual['approved_components']==components and len(components)==4;component_count+=len(components)
 assert declarations==actual['lean_declarations']and hyp==actual['hypotheses']and reason==actual['correspondence']
 assert actual['original_complete_literal_review_record']==u
 assert actual['source_review']=={**rr,'source_unit_key':key,'unit_text_sha256':current['text_sha256'],'inventory':o['inventory'],'inventory_sha256':o['inventory_sha256'],'classification_scope':reason}
 unchanged={k:v for k,v in previous.items()if k not in{'kind','status','remaining_gaps','lean_declarations','hypotheses','correspondence','approved_components','source_review','original_complete_literal_review_record','preserved_entire_original_pending_claim'}}
 assert all(actual[k]==v for k,v in unchanged.items())
 normalized={k:v for k,v in actual.items()if k not in['source','source_unit_keys','source_sha256','text_sha256']}
 assert prom['material'][key]=={'source_text_sha256':current['text_sha256'],'claim':normalized,'source_review':actual['source_review']}
 index=restored['material_claims'].index(actual);restored['material_claims'][index]=copy.deepcopy(previous)
 if key in oldprom['material']:restoredprom['material'][key]=copy.deepcopy(oldprom['material'][key])
 else:del restoredprom['material'][key]
assert whole_count==10 and component_count==4
assert old['exercises']==ledger['exercises']and len(ledger['exercises'])==128 and sum(len(e['claims'])for e in old['exercises'])==468
assert len(old['material_claims'])==len(ledger['material_claims'])==1954
assert len(old['proof_files'])==302 and len(ledger['proof_files'])==309
new=o['proof_files'];assert len(new)==7
for p,z in new.items():assert restored['proof_files'].pop(p)==z['sha256']
restored.pop('current25_material_candidate_integration');restored['generated_at_utc']=old['generated_at_utc'];assert restored==old
restoredprom.pop('current25_material_candidate_integration');assert restoredprom==oldprom
assert ledger['current25_material_candidate_integration']==prom['current25_material_candidate_integration']
ready_path=BASE/'seven-source43-canonical-paired-build-readiness-v1.json';ready=read(ready_path);assert H(ready_path)=='54c4c41ab3788442583a8d249fcd11681df34c549e8151c6c44759f0cd88f870'
assert ready['status']=='passed_genuine_seven_canonical_standalone_and_named_pairs_unselected_future25'and ready['public_theorem_count']==43 and ready['actual_canonical_execution_count']==14 and len(ready['proof_sources'])==7
prep_path=bind(ready['canonical_preparation']);prep=read(prep_path);assert H(prep_path)=='30965aa6358c42d5f54465239ef268b8b9ea81ca06609b13bb159b8ada596efc'
for row in prep['original_absolute_path_byte_aliases']:assert H(path(row['original_absolute_path']))==H(path(row['canonical_file']))==row['sha256']
assert len(prep['original_absolute_path_byte_aliases'])==129
for n,h in prep['protected_current_inputs_sha256'].items():assert H(path(n))==h
historical_manifest_alias=read(bind(ready['pre_aggregate_baseline_manifest_alias']));historical_manifest=read(bind(historical_manifest_alias['immutable_byte_copy']))
assert historical_manifest_alias['original_sha256']==prep['baseline_frozen24_manifest']['sha256']==H(bind(historical_manifest_alias['immutable_byte_copy']))
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
all_names=set();pairs=[];source_bindings=[]
def strings(x):
 if isinstance(x,str):yield x
 elif isinstance(x,list):
  for v in x:yield from strings(v)
 elif isinstance(x,dict):
  for v in x.values():yield from strings(v)
for z in ready['proof_sources']:
 p=bind(z['source']);snapshot=bind(z['source_snapshot']);h=z['source']['sha256'];originalp=bind(z['original_source']);assert p.read_bytes()==snapshot.read_bytes()==originalp.read_bytes()
 semantic=read(bind(z['original_semantic_peer']));assert semantic==z['entire_original_semantic_peer_body_and_time']and any(semantic==r['entire_original_semantic_body_and_time']for r in reviews)
 assert any(t==p.read_text()for t in strings(semantic)),'Approved entire source body absent'
 assert not re.search(r'\b(sorry|admit|axiom)\b',p.read_text())
 names=[d['name']for d in declarations(p.read_text())if d['kind']in['theorem','lemma']];assert names==z['public_theorem_names']and len(names)==z['public_theorem_count'];assert not set(names)&all_names;all_names.update(names)
 row=new[z['source']['file']];assert row['sha256']==h and row['theorem_count']==len(names)and row['mapped_named_declarations']==names
 for n,d in row['evidence_sha256'].items():assert H(path(n))==d
 for index,pair in enumerate(z['actual_canonical_pair']):
  rp=bind(pair['record']);a=read(rp);assert a==pair['entire_original_actual_record']and type(a['exit_code'])is int and a['exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==h and a['source']==z['source']['file']and a['source_unchanged']is True
  cmd=['lake','env','lean',z['source']['file'].removeprefix('verification/lean/')]if index==0 else['lake','build',z['source']['file'].removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')]
  assert a['command']==cmd and a['actual_workdir']==str(ROOT/'verification/lean')and H(path(a['log']))==a['log_sha256']and a['checked_at_utc']and a['elapsed_seconds']>=0
  assert bind(pair['raw_log'])==path(a['log'])and bind(pair['source_snapshot']).read_bytes()==p.read_bytes()
  assert row['evidence_sha256'][pair['record']['file']]==H(rp)and row['evidence_sha256'][a['log']]==a['log_sha256']
  prefix='standalone'if index==0 else'named';assert row[prefix+'_evidence']==pair['record']['file']and row[prefix+'_evidence_sha256']==H(rp)
  pairs.append({'record':pair['record'],'entire_original_body_and_time':a,'raw_log':pair['raw_log'],'source_snapshot':pair['source_snapshot']})
 source_bindings.append({'canonical_source':z['source'],'original_TMP_source':z['original_source'],'entire_original_source_and_all_bodies':p.read_text(),'public_names':names})
assert len(all_names)==43 and len(pairs)==14 and {a['file']:a['sha256']for a in o['new_actual_paired_records']}=={z['record']['file']:z['record']['sha256']for z in pairs}
for item in o['new_actual_paired_records']:assert read(bind(item))==item['entire_original_record']
selectionp=ofile('base_selection');selection=read(selectionp);current_manifest=read(ROOT/'reports/full-coverage/checkpoint-24-manifest.json');assert len(selection['proof_files'])==1144 and selection['proof_file_count']==1144
assert historical_manifest['proof_files']==current_manifest['proof_files']and historical_manifest['frozen_inputs_sha256']==current_manifest['frozen_inputs_sha256']
base_names=set();frozen=ROOT/current_manifest['snapshot']
for n,z in selection['proof_files'].items():assert H(ROOT/n)==H(frozen/n)==z['sha256'];base_names.update(d['name']for d in declarations((ROOT/n).read_text()))
for u,rr in semantic_rows.values():
 decls=u.get('lean_declarations',[d for c in u.get('components',[])for d in c['lean_declarations']]);assert set(decls)<=all_names|base_names
assets={n:d for n,d in current_manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,d in assets.items():assert H(ROOT/n)==H(frozen/n)==d
for name in['core','foundations','applied','modules','applied-promotions']:
 n='book/coverage/'+name+'.json';assert H(ROOT/n)==current_manifest['working_inputs_sha256'][n]
for n,d in o['source_sha256'].items():assert H(ROOT/n)==d
actualp=BASE/'applied25-isolated-material-candidate-actual-v2.json';actual=read(actualp)
assert actual['actual_exit_code']==0 and actual['actual_command']==['python3',o['candidate_builder']]and actual['actual_workdir']==str(ROOT)
assert actual['helper_sha256_before']==actual['helper_sha256_after']==H(helper)and H(path(actual['log']))==actual['log_sha256']and H(path(actual['actual_runner']))==actual['actual_runner_sha256']
pair_outerp=BASE/'seven-source43-canonical-pairs-actual-v1.json';pair_outer=read(pair_outerp)
assert pair_outer['actual_exit_code']==0 and pair_outer['actual_workdir']==str(ROOT)and pair_outer['actual_command']==['python3','book/coverage/checks/applied-future25/run_seven_source43_canonical_pairs_v1.py']
assert pair_outer['helper_sha256_before']==pair_outer['helper_sha256_after']==H(path(pair_outer['actual_command'][1]))and H(path(pair_outer['log']))==pair_outer['log_sha256']and H(path(pair_outer['actual_runner']))==pair_outer['actual_runner_sha256']
assert o['preserved_initial_builder_schema_failure']==b['preserved_initial_builder_schema_failure']and len(o['preserved_initial_builder_schema_failure'])==4
failed_refs=o['preserved_initial_builder_schema_failure']
for r in failed_refs:bind(r)
failed=read(bind(failed_refs[2]));assert type(failed['actual_exit_code'])is int and failed['actual_exit_code']==1 and H(path(failed['log']))==failed['log_sha256']==failed_refs[3]['sha256']
assert failed['helper_sha256_before']==failed['helper_sha256_after']==failed_refs[0]['sha256']and failed['actual_runner_sha256']==failed_refs[1]['sha256']
report={'status':'passed_independent_seven_source43_export_canonical_original_body_binding_and_exact_ten_whole_four_event_component_applied25_candidate_mechanics','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':ref(Path(__file__)),'candidate_offer':ref(op),'candidate_ledger':ref(ledgerp),'candidate_promotions':ref(promp),'exact_row_bindings':ref(bp),'exact_original_path_aliases':ref(alp),'original_semantic_review_bodies_and_times':reviews,'canonical_sources_original_full_bodies_and_public_names':source_bindings,'fourteen_actual_canonical_records_with_original_times_and_raw_logs':pairs,'actual_original_candidate_builder_record_and_time':actual,'actual_original_candidate_builder':ref(helper),'actual_original_candidate_raw_log':ref(path(actual['log'])),'actual_original_pair_outer_record_and_time':pair_outer,'preserved_initial_candidate_builder_failure':{'references':failed_refs,'entire_original_record_and_time':failed},'historical_preaggregate_manifest_byte_alias':ready['pre_aggregate_baseline_manifest_alias'],'readiness_original_stale_scope_sentence_retained_verbatim':ready['scope'],'readiness_scope_qualification':'Operational status, all seven immutable canonical sources and fourteen genuine records establish unselected future25 pairs only; the original last future24-aggregate sentence is preserved as history and creates no future25 aggregate claim.','all128_whole_exercise_bodies_and468_prior_claims_exact':True,'all302_unpruned_baseline_proof_rows_including_three_unused_metadata_exact':True,'all_other1943_material_claim_bodies_exact':True,'exact_original_semantic_reasons_hypotheses_names_review_times_and_missing_clauses':True,'reversing_exact_eleven_changes_and_seven_proof_rows_restores_entire_ledger_and_promotions':True,'whole_approved_material_units':10,'partial_component_only_unit':'primer-probability.html::node-371','whole371_remains_pending':True,'new_public_exports':43,'all1144_frozen24_sources31_assets_current52_and_five_live_owners_exact':True,'canonical_alias_count':len(aliases),'original_TMP_history_count':129,'errors':[],'coverage_complete':False,'scope':'Narrow original semantic body/canonical-source/actual pair binding plus isolated candidate mechanics only. Original three full semantic reviews and decisions/time retained exact; no semantic redecision, compiler rerun, live mapping, checkpoint25 selection/aggregate/publication or generic density371 closure inferred.'}
report['preserved_prior_independent_reader_failure']={'actual_record':ref(TMP/'applied25-canonical-binding-and-candidate-independent-foundations-actual-v1.json'),'entire_original_record_and_time':read(TMP/'applied25-canonical-binding-and-candidate-independent-foundations-actual-v1.json'),'raw_log':ref(TMP/'applied25-canonical-binding-and-candidate-independent-foundations-actual-v1.log'),'checker':ref(TMP/'check-applied25-canonical-binding-and-candidate-independent-foundations-v1.py'),'runner':ref(TMP/'run-applied25-canonical-binding-and-candidate-independent-foundations-v1.py'),'reason':'The first reader treated node401 prior partial semantic metadata as immutable top-level fields even when replacing it by the new whole-unit decision. The original partial row is preserved entire inside the new row, and the full candidate reversal restores the exact original metadata/body/time. NEW reader exempts only the explicitly replaced semantic metadata fields; no owner artifact changed.'}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'whole_units':10,'partial_units':1,'new_sources':7,'exports':43,'genuine_original_pairs':14}))
