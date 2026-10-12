from pathlib import Path
import copy,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/root31-Core-Applied-promotions-final2-independent-foundations31-semantic-v1.json')
assert not OUT.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
def read(p):return json.loads(path(p).read_bytes())
offerpath=path('book/coverage/checks/future31-core/Core24-Core15NF-Applied21proof1NF-final-candidates-v2/final-offer-v2.json')
assert sha(offerpath)=='2cab33d169990375bd73486e620412eefca4a6ca4ee45197dcd498bb7640a3b2'
offer=read(offerpath);draft=read(checked(offer['original_draft_offer']));inverse=read(checked(offer['AST_exact_inverse']))
semanticp=checked(draft['independent_AST_full_semantic_peer']);semantic=read(semanticp)
assert sha(semanticp)=='bb3c92b97798dd355c1d353bd264701e846804ab22dd1c93ccd379de68dcec49'
assert semantic['status'].startswith('passed') and semantic['errors']==[]
semantic_native=read(checked(semantic['actual_finalizer']))
assert semantic_native['actual_exit_code']==0 and semantic_native.get('protection_errors',[])==[]
assert semantic_native['helper_sha256_before']==semantic_native['helper_sha256_after']
inventoryp=checked(draft['inventory']);inventory=read(inventoryp);units={r['key']:r for r in inventory['material_source_units']}
assert inventory['counts']['exercises']==556 and inventory['counts']['material_source_units']==12774
binding=read('book/coverage/checks/future30-core/owner30-integration-binding-v1/actual-root30-reviewed-candidates-bindings-v1.json')
oldoffer=read(checked(binding['owners']['applied']['reviewed_offer']))
original_refs={o:oldoffer['candidate_refs'][o] for o in ['core','applied','applied-promotions']}
old={o:read(checked(r)) for o,r in original_refs.items()}
for owner in ['core','applied']:
 assert original_refs[owner]['sha256']==inverse['original_raw_owner30_files'][owner]['sha256']==sha(ROOT/f'book/coverage/{owner}.json')
assert original_refs['applied-promotions']['sha256']==inverse['original_raw_promotions']['sha256']==sha(ROOT/'book/coverage/applied-promotions.json')
candidates={o:read(checked(r)) for o,r in offer['candidates'].items()}
promotions=read(checked(offer['promotions']))
core_ast=read(checked(offer['Core24_metadata_inverse']['original_core_AST_candidate']))
core_back=copy.deepcopy(candidates['core']); source=offer['Core24_metadata_inverse']['remove_proof_source']
newproof=core_back['proof_files'].pop(source);core_back.pop('future31_actual_canonical_binding')
core_back['counts']['proof_files']=offer['Core24_metadata_inverse']['restore_proof_count']
assert core_back==core_ast
assert len(old['core']['proof_files'])==186 and len(candidates['core']['proof_files'])==187
assert all(candidates['core']['proof_files'][n]==m for n,m in old['core']['proof_files'].items())
assert candidates['applied']['proof_files']==old['applied']['proof_files'] and len(old['applied']['proof_files'])==314
assert candidates['core']['exercises']==old['core']['exercises'] and candidates['applied']['exercises']==old['applied']['exercises']
assert next(e for e in candidates['core']['exercises'] if e['inventory_key']=='barriers.html::exercise-16')==next(e for e in old['core']['exercises'] if e['inventory_key']=='barriers.html::exercise-16')
sys.path.insert(0,str(ROOT/'book'));from validate import Document
documents={}
def document(name):
 if name not in documents:documents[name]=Document(path(name).read_text())
 return documents[name]
decisions=[]
for owner in ['core','applied']:
 rows=candidates[owner]['material_claims'];changes=draft['individual_changes'][owner]
 assert len(changes)==(15 if owner=='core' else 22)
 indices={c['row_index'] for c in changes};assert len(indices)==len(changes)
 assert len(rows)==len(old[owner]['material_claims'])
 for i,(a,b) in enumerate(zip(rows,old[owner]['material_claims'])):
  if i not in indices:assert a==b,(owner,i)
 for c in changes:
  i=c['row_index'];r=rows[i];before=inverse['old_rows_by_owner_and_index'][owner][str(i)]
  assert before==old[owner]['material_claims'][i] and before['status']=='pending'
  key=c['inventory_key'];assert r['source_unit_keys']==[key] and r['status']==c['after_status']
  detail=r['independent_source_review'];pointer=detail['decision_JSON_pointer'];decision=semantic[pointer[0]][pointer[1]]
  assert decision['inventory_key']==key and decision['entire_current_material_literal']==units[key]
  assert checked(detail['peer']).read_bytes()==semanticp.read_bytes()
  assert checked(detail['exact_current81_inventory']).read_bytes()==inventoryp.read_bytes()
  assert detail['whole_individual_leaf_approved'] is True and detail['enclosing_math_or_handler_scope_promoted'] is False
  literal=units[key];doc=document(literal['source']);node=doc.nodes[int(literal['locator'].split('-')[-1])-1]
  assert node.tag==literal['tag'] and node.line==literal['line'] and node.text()==literal['source_text']
  assert r['remaining_gaps']==[]
  if r['status']=='proved':
   assert owner=='applied' and decision['whole_child_approved'] is True and decision['remaining_gaps']==[]
   assert r['lean_declarations']==c['declarations']==decision['exact_support']
   assert r['correspondence']==decision['full_clause_correspondence']
   parent=decision['entire_current_parent_exercise'];parentnode=doc.by_id[parent['locator'].lstrip('#')]
   assert parentnode is not node and any(n is node for n in parentnode.descendants())
   assert parentnode.text()==parent['source_text'] and parent['status']=='complete_math'
   assert decision['original_AST_scan_record']['strict_AST_descendant'] is True
  else:
   assert r['status']=='not_a_formal_claim' and decision['whole_selected_leaf_NF_approved'] is True
   assert r['lean_declarations']==[] and r['hypotheses']==[] and r['correspondence']==decision['reason']
   assert decision['underlying_handler_or_math_wrapper_approved'] is False
  decisions.append({'owner':owner,'key':key,'after_status':r['status'],'entire_literal':literal,'semantic_decision_pointer':pointer,'entire_row_and_context_read':True})
 assert candidates[owner]['source_sha256']==old[owner]['source_sha256']
 for name,digest in candidates[owner]['source_sha256'].items():
  if name.startswith('SafeLearning/'):assert sha(name)==digest
 back=copy.deepcopy(core_ast if owner=='core' else candidates[owner])
 for i,r in inverse['old_rows_by_owner_and_index'][owner].items():back['material_claims'][int(i)]=r
 back.pop('future31_source81_AST_reuse_draft_binding')
 back['current_inventory']=old[owner]['current_inventory'];back['current_inventory_sha256']=old[owner]['current_inventory_sha256']
 assert back==old[owner]
 assert candidates[owner]['current_inventory']=='book/coverage/inventory-after-correction81.json' and candidates[owner]['current_inventory_sha256']==sha(inventoryp)
promo_keys={c['inventory_key'] for c in draft['individual_changes']['applied']};assert len(promo_keys)==22
for key,row in promotions['material'].items():
 if key not in promo_keys:assert row==old['applied-promotions']['material'][key]
for c in draft['individual_changes']['applied']:
 key=c['inventory_key'];r=candidates['applied']['material_claims'][c['row_index']];mirror=promotions['material'][key]
 assert mirror=={'source_text_sha256':units[key]['text_sha256'],'claim':r,'current81_independent_exact_literal_reuse':r['independent_source_review']}
promo_back=copy.deepcopy(promotions)
for key,prior in inverse['old_promotion_entries'].items():
 if prior is None:promo_back['material'].pop(key)
 else:promo_back['material'][key]=prior
assert promo_back==old['applied-promotions']
for key in ['primer-rl-nn.html::node-1531','primer-rl-nn.html::node-359']:
 assert [r for r in candidates['applied']['material_claims'] if key in r['source_unit_keys']]==[r for r in old['applied']['material_claims'] if key in r['source_unit_keys']]
ready=read(checked(offer['real_canonical_readiness'])); assert ready['status'].startswith('passed_actual_reviewed31_') and ready['actual_compiler_command_count']==12
rootrow=next(r for r in ready['sources'] if r['canonical_source']==source)
assert newproof['sha256']==sha(source)==rootrow['original_tmp_source']['sha256']
assert newproof['theorem_count']==24 and newproof['public_theorem_names']==[d['name'] for d in rootrow['public_declarations'] if d['kind'] in ['theorem','lemma']]
assert newproof['public_names']==[d['name'] for d in rootrow['public_declarations']] and len(newproof['public_names'])==30
assert newproof['actual_pair']==[r for r in ready['actual_paired_records'] if r['source']['file']==source]
for pair in newproof['actual_pair']:
 n=read(checked(pair['actual_record']));raw=checked(pair['raw_log']);snap=checked(pair['source_snapshot'])
 assert type(n['exit_code']) is int and n['exit_code']==pair['actual_exit_code']==0
 assert n['source']==source and n['source_sha256_before']==n['source_sha256_after']==newproof['sha256']
 name=Path(source).stem;command=['lake','env','lean','SafeLearning/'+name+'.lean'] if pair['kind']=='standalone' else ['lake','build','SafeLearning.'+name]
 assert n['command']==command and n['actual_workdir']==str(ROOT/'verification/lean')
 assert snap.read_bytes()==path(source).read_bytes() and sha(raw)==n['log_sha256']
 for field in ['actual_record','raw_log','source_snapshot']:
  assert newproof['evidence_sha256'][pair[field]['file']]==pair[field]['sha256']
assert newproof['component_only_source_association']['whole_exercise_approved'] is False
assert any(p['sha256']=='6d618864e473e4a076ae2fecc78b91c4862e5edc6eeb1f5c32d30cb620cd8250' for p in newproof['original_math_peers'])
audit=read('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')['actual_audit'];actualaudit=read(checked(audit))
assert len(semantic['actual_reused_selected30_kernel_checks'])==13
for r in semantic['actual_reused_selected30_kernel_checks']:
 assert sha(r['source'])==r['source_sha256']==actualaudit['proof_sha256'][r['source']]
 assert r['exact_original_final_css_check']['exit_code']==0
 assert sha(r['raw_log'])==r['raw_log_sha256']
production_natives=[]
for stem,helper in [('Core15NF-Applied21proof1NF-draft-preparation-execution-v1',draft['helper']),('Core24-Core15NF-Applied21proof1NF-final-preparation-execution-v1',offer['helper'])]:
 p=path('reports/full-coverage/'+stem+'.json');n=read(p)
 assert type(n['actual_exit_code']) is int and n['actual_exit_code']==0 and n['status']=='passed'
 assert n['actual_command']==['python3',helper['file']] and n['actual_workdir']==str(ROOT)
 assert n['helper_sha256_before']==n['helper_sha256_after']=={helper['file']:helper['sha256']}
 assert sha(n['log'])==n['log_sha256'];production_natives.append({'native':ref(p),'raw_log':ref(n['log']),'original_elapsed_seconds':n['elapsed_seconds']})
result={'status':'passed_independent_Core24_Core15NF_Applied21proof1NF_promotions_final2_full_mapping_review','errors':[],
 'reviewed_offer':ref(offerpath),'candidate_refs':offer['candidates'],'promotions_candidate':offer['promotions'],
 'full_changed_Core15_NF_Applied21_proved_and_one_NF_rows_and_contexts_read':True,
 'all22_promotions_exact_mirrors_and_every_other_entry_unchanged':True,
 'both_full_owner_forward_inverse_and_full_original_raw_SHA_refs_verified':True,
 'Core24_to_AST_candidate_and_AST_candidates_to_whole_original_owner30_inverses_verified':True,
 'every_old_exercise_entire_body_status_claim_and_original_proof_metadata_unchanged':True,
 'CoreEx16_whole_false_and_integral_curve_existence_gap_unchanged':True,
 'two_specific_Applied_AST_children1531_359_still_pending_unchanged':True,
 'new_Core24_30_public_names_two_real_commands_match_Root12_readiness_and_source_snapshot':True,
 '13_old_Selected30_proof_source_kernel_native_chains_reused_without_new_kernel_claim':True,
 'NF_leaves_only_no_parent_math_or_handler_promotion':True,'individual_changed_rows':decisions,
 'original_decoded_owner30_refs':original_refs,'original_full_semantic_peer':draft['independent_AST_full_semantic_peer'],
 'original_actual_production_natives':production_natives,'canonical_root12_readiness':offer['real_canonical_readiness'],
 'actual_current_owner_or_new_aggregate_or_publication_installation_by_reviewer':False,'coverage_complete':False}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','errors':[],'changed_Core_NF':15,'changed_Applied_proved':21,'changed_Applied_NF':1,'promotion_mirrors':22,'Core_canonical_pairs':2}))
