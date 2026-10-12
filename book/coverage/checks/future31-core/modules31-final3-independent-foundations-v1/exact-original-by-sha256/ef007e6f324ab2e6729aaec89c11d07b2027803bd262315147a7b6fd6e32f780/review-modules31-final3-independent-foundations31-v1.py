from pathlib import Path
import copy,hashlib,json,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/modules31-final3-independent-foundations31-semantic-v1.json')
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256'],r['file']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
def read(p):return json.loads(path(p).read_bytes())
Q=path('book/coverage/checks/modules-future31/current81-integral39-ast19-realpair-v1/modules31-current81-integral39-realpair-ast19-final-mapping-request-root-relative-v3.json')
O=Q.with_name('modules31-current81-integral39-realpair-ast19-root-relative-author-final-offer-v3.json')
assert sha(Q)=='927ef428e2feb950d754dda07d06dd2e8314b038fe7f67f09806fe2a65ca0b5b' and sha(O)=='9bbcd5109d7c513c02e01c60b2447a62201adf83da75ef154d4c0cda083844ee'
q=read(Q);offer=read(O);old=read(checked(q['original_owner30']));candidate=read(checked(q['candidate']));f=read(checked(q['forward_patch']));r=read(checked(q['inverse_patch']))
for name,digest in q['required_evidence_artifacts_sha256'].items():assert sha(name)==digest,name
for name,digest in offer['required_evidence_artifacts_sha256'].items():assert sha(name)==digest,name
# Independently implement strict RFC6902 replay. Every replacement/removal must exist;
# every test checks the exact intermediate value. Values are deep-copied on assignment.
def apply(d,ops):
 d=copy.deepcopy(d)
 for i,x in enumerate(ops):
  ks=[k.replace('~1','/').replace('~0','~') for k in x['path'].split('/')[1:]];p=d
  for k in ks[:-1]:p=p[int(k)] if isinstance(p,list) else p[k]
  k=ks[-1];k=int(k) if isinstance(p,list) and k!='-' else k
  if x['op']=='test':assert p[k]==x['value'],(i,x['path'])
  elif x['op']=='replace':assert k in p if isinstance(p,dict) else 0<=k<len(p);p[k]=copy.deepcopy(x['value'])
  elif x['op']=='remove':
   if isinstance(p,list):p.pop(k)
   else:assert k in p;del p[k]
  elif x['op']=='add':
   if isinstance(p,list):p.append(copy.deepcopy(x['value'])) if k=='-' else p.insert(k,copy.deepcopy(x['value']))
   else:assert k not in p;p[k]=copy.deepcopy(x['value'])
  else:raise AssertionError(x['op'])
 return d
assert apply(old,f['operations'])==candidate
back=apply(candidate,r['operations']);assert back==old
serial=r['original_serialization'];body=(json.dumps(back,indent=serial['indent'],ensure_ascii=serial['ensure_ascii'])+('\n' if serial['trailing_newline'] else '')).encode()
assert body==checked(q['original_owner30']).read_bytes() and hashlib.sha256(body).hexdigest()==q['original_owner30']['sha256']==r['inverse_reconstruction_original_bytes_sha256']
assert (json.dumps(candidate,indent=2,ensure_ascii=False)+'\n').encode()==checked(q['candidate']).read_bytes()
identity=read(checked(q['identity']));ass=read(checked(q['explicit_associations']));inv79=read(checked(q['evidence']['inventory79']));inv81=read(checked(q['evidence']['inventory81']))
u79={x['key']:x for x in inv79['material_source_units']};u81={x['key']:x for x in inv81['material_source_units']};e79={x['key']:x for x in inv79['exercises']};e81={x['key']:x for x in inv81['exercises']}
assert inv81['counts']['exercises']==556 and inv81['counts']['material_source_units']==12774
assert len(identity['all_material_identities'])==4977 and len(identity['all_exercise_identities'])==217
for x in identity['all_material_identities']:
 a=u79[x['key']];b=u81[x['key']]
 assert x['original_text_sha256']==a['text_sha256'] and x['current_text_sha256']==b['text_sha256']
 assert x['original_source_sha256']==a['source_sha256'] and x['current_source_sha256']==b['source_sha256']
 assert x['literal_unchanged']==(a['source_text']==b['source_text'])
for x in identity['all_exercise_identities']:
 a=e79[x['key']];b=e81[x['key']]
 assert x['original_text_sha256']==a['text_sha256'] and x['current_text_sha256']==b['text_sha256']
 assert x['original_source_sha256']==a['source_sha256'] and x['current_source_sha256']==b['source_sha256']
 assert x['literal_unchanged']==(a['source_text']==b['source_text'])
assert set(identity['changed_materials_entire_original_and_current'])=={'nn-in-the-loop.html::node-1247'}
assert set(identity['changed_exercises_entire_original_and_current'])=={'nn-in-the-loop.html::exercise-19'}
for name,h in candidate['source_sha256'].items():assert sha(name)==h
assert candidate['chapter_fragment_sha256']==old['chapter_fragment_sha256']
for name,h in candidate['chapter_fragment_sha256'].items():assert sha(name)==h
source='verification/lean/SafeLearning/CompleteModulesIntegralTrackingWhole31.lean';proof=candidate['proof_files'][source]
assert len(old['proof_files'])==517 and len(candidate['proof_files'])==518 and all(candidate['proof_files'][n]==v for n,v in old['proof_files'].items())
assert len(old['declarations'])==3988 and candidate['declarations'][:3988]==old['declarations'] and len(candidate['declarations'])==4027
assert proof==ass['proof_metadata'] and proof['theorem_count']==39 and proof['public_name_count']==52
ready=read(checked(q['actual_current81_pair_binding31']['actual_complete12_readiness']));assert ready['actual_compiler_command_count']==12 and ready['errors']==[]
row=next(x for x in ready['sources'] if x['canonical_source']==source)
theorems=[x['name'] for x in row['public_declarations'] if x['kind'] in ['theorem','lemma']];public=[x['name'] for x in row['public_declarations']]
assert len(theorems)==39 and len(public)==52 and proof['public_theorem_names']==proof['declarations']==proof['mapped_named_declarations']==theorems and proof['public_names']==public
assert candidate['declarations'][3988:]==theorems
assert sha(source)==proof['sha256']=='1a388e0109e6e8ff8bd9ce8c102420a7202f064eb7e46a76ff2cd4bcfefc10aa'
assert proof['actual_pair']==[p for p in ready['actual_paired_records'] if p['source']['file']==source]
for pair in q['actual_current81_pair_binding31']['own_actual_pairs']:
 basepair=next(p for p in proof['actual_pair'] if p['kind']==pair['kind'])
 for k,v in basepair.items():
  if isinstance(v,dict):assert pair[k]['file']==v['file'] and pair[k]['sha256']==v['sha256'];checked(pair[k])
  else:assert pair[k]==v
 n=read(checked(pair['actual_record']));raw=checked(pair['raw_log']);snap=checked(pair['source_snapshot'])
 assert type(n['exit_code']) is int and n['exit_code']==0 and n['source_unchanged'] is True
 assert n['source']==source and n['source_sha256_before']==n['source_sha256_after']==proof['sha256']
 cmd=['lake','env','lean','SafeLearning/'+Path(source).name] if pair['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem]
 assert n['command']==cmd and n['actual_workdir']==str(ROOT/'verification/lean') and n['elapsed_seconds']>0
 assert n['log_sha256']==sha(raw) and snap.read_bytes()==path(source).read_bytes()
 for k in ['actual_record','raw_log','source_snapshot']:assert proof['evidence_sha256'][pair[k]['file']]==pair[k]['sha256']
peers={k:read(checked(q['evidence'][k])) for k in ['AST_peer','integral35_peer','integral39_supplement','integral39_increment']}
for p in peers.values():assert p['status'].startswith('passed') and p['errors']==[]
assert peers['integral39_supplement']['entire_combined39_source_including_all39_public_and_two_private_bodies_approved'] is True
assert peers['integral39_supplement']['entire_combined39_source']['sha256']==proof['sha256']
assert peers['integral39_supplement']['native_context_is_original_Source79_finalCSS_owner30_not_relabelled_Source81'] is True
ast={x['inventory_key']:x for x in peers['AST_peer']['per_structural_leaf_decisions']};decisions=[]
sys.path.insert(0,str(ROOT/'book'));from validate import Document
docs={}
def doc(n):
 if n not in docs:docs[n]=Document(path(n).read_text())
 return docs[n]
allchanged={x['id'] for x in ass['Integral_material_rows']+ass['AST19_material_rows']}
assert len(allchanged)==23 and len(candidate['material_claims'])==len(old['material_claims'])
for a,b in zip(old['material_claims'],candidate['material_claims']):
 if b['id'] not in allchanged:assert a==b
for x in ass['AST19_material_rows']:
 key=x['source_unit_keys'][0];unit=u81[key];s=ast[key]
 assert x in candidate['material_claims'] and x['status']=='not_a_formal_claim' and x['lean_declarations']==[] and x['hypotheses']==[]
 assert s['whole_selected_leaf_NF_approved'] is True and s['underlying_handler_or_math_wrapper_approved'] is False
 assert s['entire_current_material_literal']['source_text']==unit['source_text']==x['statement_in_prose']
 assert x['correspondence']==s['reason'] and x['remaining_gaps']==[]
 node=doc(unit['source']).nodes[int(unit['locator'].split('-')[-1])-1];assert node.tag==unit['tag'] and node.text()==unit['source_text']
 decisions.append({'key':key,'status':'not_a_formal_claim','entire_leaf_and_local_context_read':True,'no_handler_destination_or_enclosing_math_promotion':True})
for x in ass['Integral_material_rows']:
 key=x['source_unit_keys'][0];assert x in candidate['material_claims'] and x['status']=='proved' and x['whole_exact_current_source_unit_approved'] is True and x['statement_in_prose']==u81[key]['source_text']
 assert x['remaining_gaps']==[] and set(x['lean_declarations'])<=set(theorems) and x['canonical_pair_pending'] is False
 for predicate in x['formal_input_predicates']:assert predicate['declaration'] in theorems and predicate['source']['sha256']==proof['sha256'] and predicate['exact_reviewed_signature_and_all_input_predicates'] in path(source).read_text()
 decisions.append({'key':key,'status':'proved','entire_literal_and39_formal_input_domains_read':True,'original_independent_whole_scope_reused_with_Source81_identity':True})
exercise=ass['entire_Integral_exercise'];assert exercise in candidate['exercises'] and exercise['status']=='complete_math' and len(exercise['claims'])==5
assert exercise['whole_exact_current_exercise_approved'] is True and all(x['status']=='proved' and x['remaining_gaps']==[] and set(x['lean_declarations'])<=set(theorems) for x in exercise['claims'])
for a,b in zip(old['exercises'],candidate['exercises']):
 if b['inventory_key']==exercise['inventory_key']:
  assert [x['id'] for x in a['claims']]==[x['id'] for x in b['claims']] and [x['statement_in_prose'] for x in a['claims']]==[x['statement_in_prose'] for x in b['claims']]
 else:assert {k:v for k,v in a.items() if k!='source_sha256'}=={k:v for k,v in b.items() if k!='source_sha256'}
plan=read(checked(q['evidence']['plan2']));flags=plan['all_original_false_whole_flags_must_be_retained'];assert len(flags)==111
# Their unchanged historical bodies are independently preserved by the strict inverse
# and by equality of all pre-existing top-level history buckets.
for key in old:
 if key not in ['status','source_sha256','current_inventory','current_inventory_sha256','current_identity_binding_validation','proof_files','exercises','material_claims','declarations','counts']:assert candidate[key]==old[key],key
assert candidate['reviewed_work_integration31_current81_provisional_candidate']['whole_duality7_5_and_scenario15_5_approved'] is False
assert candidate['reviewed_work_integration31_current81_provisional_candidate']['whole_shifted_temporal_Exercise14_6_approved'] is False
natives=[]
for k in ['actual_author_preparation','actual_author_pair_binding']:
 z=q[k];n=read(checked(z['native']));assert n['actual_exit_code']==0 and n['actual_wrapper_exit_code']==0 and n['protection_errors']==[] and n['elapsed_seconds']>0
 assert n['actual_command']==['python3',n['helper']['file']] and n['actual_workdir']==str(ROOT)
 assert z['helper']['sha256']==n['helper']['sha256'] and z['wrapper']['sha256']==n['original_actual_wrapper']['sha256']
 checked(z['helper']);checked(z['wrapper']);assert z['raw_log']['sha256']==n['raw_log_sha256'];checked(z['raw_log'])
 natives.append({'native':z['native'],'original_elapsed_seconds':n['elapsed_seconds'],'raw_log':z['raw_log'],'helper':z['helper'],'wrapper':z['wrapper']})
result={'status':'passed_independent_modules31_current81_Integral39_AST19_real_pair_full_final3_mapping_review','errors':[],'reviewed_offer':ref(O),'reviewed_request':ref(Q),'candidate':q['candidate'],'original_whole_owner30':q['original_owner30'],'strict_full_forward_and_reverse_with_all_intermediate_test_assertions_verified':True,'whole_original_owner30_byte_inverse_verified':True,'all4977_material_and217_exercise_Source79_to81_identities_checked':True,'all_four_entire_Integral_literals_and_five_original_exercise_requirements_and39_complete_proof_bodies_read':True,'all19_individual_NF_leaves_full_local_contexts_and_prior_exact_peer_decisions_read':True,'all_old517_proof_metadata_and3988_declarations_prefix_exact':True,'all111_historical_wholeFalse_bodies_unchanged':True,'current_full_Exercise19_and_four_literals_only_approved_in_exact_prior_peer_domains':True,'two_true_canonical_commands_source_cwd_native_raw_snapshot_chains_verified':True,'new_public_theorems':39,'new_public_declarations':52,'actual_canonical_pairs':2,'original_independent_math_scope_peers':{k:q['evidence'][k] for k in peers},'individual_current_material_decisions':decisions,'original_actual_author_natives':natives,'canonical_readiness':q['actual_current81_pair_binding31']['actual_complete12_readiness'],'IQC_Duality_Scenario_whole_promoted':False,'current_owner_or_source_or_compiler_or_publication_write_by_reviewer':False,'coverage_complete':False}
assert not OUT.exists();OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','errors':[],'proved_material':4,'NF':19,'whole_exercise':1,'old_proofs':517,'new_theorems':39,'public_names':52,'canonical_pairs':2}))
