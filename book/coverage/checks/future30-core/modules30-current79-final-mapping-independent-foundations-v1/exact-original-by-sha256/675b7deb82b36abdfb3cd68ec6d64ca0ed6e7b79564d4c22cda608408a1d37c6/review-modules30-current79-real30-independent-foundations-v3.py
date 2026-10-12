from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import json,hashlib,copy,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');O=R/'book/coverage/checks/modules-future30/current79-real30-pair-bound-v1/modules30-current79-real30-pair-bound-offer-draft-v2.json';OUT=Path('/tmp/modules30-current79-real30-independent-foundations-findings-v3.json');assert not OUT.exists()
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
closed={str(O):sha(O),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q['file']);assert p.is_file() and sha(p)==q['sha256'],str(p)
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(R):assert not p.is_symlink() and p.resolve().is_relative_to(R)
 closed[str(p)]=q['sha256'];return json.loads(p.read_bytes()) if p.suffix=='.json' else p.read_bytes()
def read(q):return add(q)
def encoded(x,original):
 opts=[(json.dumps(x,indent=2,ensure_ascii=a)+'\n').encode() for a in [True,False]];assert original in opts;return True if opts[0]==original else False
def restore(x,patches):
 y=copy.deepcopy(x)
 for c in reversed(patches):
  cur=y
  for k in c['path'][:-1]:cur=cur[k]
  if c['existed']:cur[c['path'][-1]]=copy.deepcopy(c['before'])
  else:del cur[c['path'][-1]]
 return y
assert sha(O)=='ab47d92dbe12d65d6eb30cd817a0282170aabe8eaeada24d21979776e4977a0f';d=read(ref(O))
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():add(q)
c=read(d['candidate']);assert d['candidate']['sha256']=='182546163ee83684b3c693ab574eddd610fb73e4538fb156e3b68657ed4e6418';ci=read(d['exact_inverse_interface']);si=read(d['original_semantic_inverse_interface']);identity=read(d['identity_sidecar']);side=read(d['completion_component_associations']);old=read(d['original_owner'])
assert path(d['original_owner']['file']).read_bytes()==(R/'book/coverage/modules.json').read_bytes() and sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
provisional=read(ci['provisional_candidate']);reversed1=restore(c,ci['restore_patches_in_reverse_order']);assert reversed1==provisional;enc1=encoded(reversed1,path(ci['provisional_candidate']['file']).read_bytes())
reversed2=restore(reversed1,si['restore_patches_in_reverse_order']);assert reversed2==old;enc2=encoded(reversed2,path(d['original_owner']['file']).read_bytes())
assert ci['exact_whole_raw29_byte_inverse_verified'] is True and si['exact_inverse_restores_entire_original_raw29'] is True
assert len(old['proof_files'])==502 and list(c['proof_files'])[:502]==list(old['proof_files']) and all(c['proof_files'][n]==v for n,v in old['proof_files'].items()) and c['declarations'][:3484]==old['declarations'] and len(old['declarations'])==3484 and len(c['declarations'])==3988
assert len(c['proof_files'])==517 and len(d['proof_files'])==15
inv=read(d['inventory']);assert d['inventory_sha256']==sha(R/'book/coverage/inventory.json')=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de';units={u['key']:u for u in inv['material_source_units']};exs={u['key']:u for u in inv['exercises']}
assert identity['owned_exercise_count']==217 and identity['owned_material_source_unit_count']==4977 and identity['all_other_owned_records_entire_equal_except_whole_page_source_fingerprint'] is True
for e in c['exercises']:
 u=exs[e['inventory_key']];assert e['source']==u['source'] and e.get('source_text_sha256',e.get('text_sha256'))==u['text_sha256']
 if 'source_text' in e:assert e['source_text']==u['source_text']
for key in d['whole_material_keys']:
 rows=[r for r in c['material_claims'] if key in r['source_unit_keys']];assert rows and all(r['status']!='pending' for r in rows)
 for r in rows:
  u=units[key];lit=r['entire_original_literal_decision_and_review_time'];assert lit['source_unit_key']==key and lit['entire_actual79_record']==u and lit['whole_literal_approved'] is True and r['statement_in_prose']==u['source_text']
  assert c['source_sha256'][u['source']]==u['source_sha256'] and r['reviewed_owner30_transition']['whole_scope_approval'] is True
assert len(d['whole_exercises'])==8 and len(d['whole_material_keys'])==32 and len(set(d['whole_material_keys']))==32
for k in d['whole_exercises']:
 e=next(e for e in c['exercises'] if e['inventory_key']==k);assert e['status']=='complete_math' and all(r['status'] in ['proved','not_a_formal_claim'] for r in e['claims'])
for k in ['viability.html::exercise-19','verification.html::exercise-19']:assert next(e for e in c['exercises'] if e['inventory_key']==k)['status']!='complete_math'
assert side['whole_duality_7_5_remains_false'] is True and side['whole_scenario_15_5_remains_false'] is True
assert dict(Counter(e['status'] for e in c['exercises']))=={'complete_math':197,'partial':7,'pending':13}
assert dict(Counter(r['status'] for r in c['material_claims']))=={'proved':1124,'pending':3540,'not_a_formal_claim':536} and c['counts']==d['counts']
ready=read(d['actual_complete90_readiness']);outer=read(d['actual_complete90_execution']);assert ready['errors']==[] and ready['status']=='passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected' and (ready['source_count'],ready['public_theorem_count'],ready['actual_compiler_command_count'])==(45,966,90)
assert outer['status']=='passed' and type(outer['actual_exit_code']) is int and outer['actual_exit_code']==0 and outer['helper_sha256_before']==outer['helper_sha256_after'] and sha(outer['log'])==outer['log_sha256'];add(ref(outer['log']))
pairs={(r['source']['file'],r['kind']):r for r in ready['actual_paired_records']};assert len(pairs)==90
sys.path.insert(0,str(R/'book/coverage'));import lean_names;add(ref(R/'book/coverage/lean_names.py'));names=[];proof_pairs=[]
for dest,row in d['proof_files'].items():
 body=path(dest).read_text();add({'file':dest,'sha256':row['sha256']});decs=lean_names.declarations(body);tn=[x['name'] for x in decs if x['kind'] in ['theorem','lemma']]
 assert decs==row['public_declarations'] and tn==row['declarations'] and len(tn)==row['theorem_count'];names+=tn
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
 assert row['canonical_pair_pending'] is False and len(row['actual_pair'])==2
 read(row['independent_source_review'])
 for q in row['actual_pair']:
  rr=pairs[(dest,q['kind'])];assert rr==q;a=read(q['actual_record']);raw=add(q['raw_log']);snapshot=add(q['source_snapshot'])
  vals=[a[k] for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in a];assert vals and all(type(v) is int and v==0 for v in vals) and a['status']=='passed'
  command=['lake','env','lean','SafeLearning/'+Path(dest).name] if q['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(dest).stem]
  ks=[k for k in ['command','actual_command'] if k in a];assert ks and all(a[k]==command for k in ks)
  ks=[k for k in ['actual_workdir','cwd','workdir','working_directory'] if k in a];assert ks and all(a[k]==str(R/'verification/lean') for k in ks)
  assert a['source']==dest and a['source_unchanged'] is True and a['source_sha256_before']==a['source_sha256_after']==q['source']['sha256']==row['sha256'] and hashlib.sha256(snapshot).hexdigest()==row['sha256'] and hashlib.sha256(raw).hexdigest()==a['log_sha256']
  proof_pairs.append({'source':dest,'kind':q['kind'],'native':q['actual_record'],'original_checked_at_utc':a['checked_at_utc'],'original_elapsed_seconds':a['elapsed_seconds']})
assert len(names)==504 and len(set(names))==504 and len(proof_pairs)==30 and len([x for row in d['proof_files'].values() for x in row['public_declarations']])==707
# Every new association binds an actually present proof name to its exact prior independently read scope.
for a in si['new_exercise_claim_associations']:
 e=next(e for e in c['exercises'] if e['inventory_key']==a['exercise']);r=next(r for r in e['claims'] if r['id']==a['claim_id']);assert r['status']=='proved' and r['lean_declarations']==a['declarations'] and set(a['declarations']).issubset(set(names));p=read(a['peer']);assert p.get('errors',[])==[]
for a in si['new_material_claim_associations']:
 r=c['material_claims'][a['index']];assert r['id']==a['claim_id'] and r['source_unit_keys']==[a['key']] and r['status']=='proved' and r['lean_declarations']==a['declarations'] and set(a['declarations']).issubset(set(names));p=read(a['peer']);assert p.get('errors',[])==[]
assert len(si['new_exercise_claim_associations'])==37 and len(si['new_material_claim_associations'])==32
assert len(side['inherited_gap_list_only_changes'])==5
for a in side['inherited_gap_list_only_changes']:
 oe=next(e for e in old['exercises'] if e['inventory_key']==a['exercise']);ce=next(e for e in c['exercises'] if e['inventory_key']==a['exercise']);o=next(r for r in oe['claims'] if r['id']==a['claim_id']);n=next(r for r in ce['claims'] if r['id']==a['claim_id'])
 assert o['status']==n['status']=='proved' and o['remaining_gaps']==a['original_remaining_gaps'] and n['remaining_gaps']==[]
 assert {k:v for k,v in o.items() if k!='remaining_gaps'}=={k:v for k,v in n.items() if k!='remaining_gaps'}
 read(a['completion_full_scope_peer']);assert set(a['completion_support_declarations']).issubset(set(names))
 if a['source_assumed_probability_event_not_derived']:assert a['exercise']=='toolkit-gp.html#book-m3-b2' and 'assum' in a['reason'].lower()
# Exact previous scopes are retained; full duality/scenario exclusions and GP probability assumptions are explicit.
family_scopes=[]
for a in side['all15_compiled_family_full_semantic_associations']:
 read(a['source']);native=read(a['original_actual_native']);peer=read(a['full_semantic_peer']);assert native['actual_exit_code']==0 and native['protection_errors']==[] and peer.get('errors',[])==[]
 family_scopes.append({'family':a['family'],'original_exact_source':a['source'],'original_full_semantic_peer':a['full_semantic_peer'],'retained_exact_scope_pointer':a['scope_pointer'],'whole_scope_not_inferred_from_component':True})
actual=read(d['actual_finalizer']);assert actual['status']=='passed' and actual['actual_exit_code']==0 and actual['protection_errors']==[] and actual['helper_sha256_before']==actual['helper_sha256_after'] and actual['compiler_started'] is False
aliases=d['actual_finalizer_original_byte_aliases']
for n,h in actual['helper_sha256_before'].items():q=aliases[n];assert q['sha256']==h;read(q)
q=aliases[actual['raw_log']];assert q['sha256']==actual['raw_log_sha256'];read(q)
assert d['actual_canonical_pairs_pending'] is False and d['installation_ready'] is False and d['coverage_complete'] is False
reader1files=[Path('/tmp/review-modules30-current79-real30-independent-foundations-v1.py'),Path('/tmp/run-review-modules30-current79-real30-independent-foundations-v1.py'),Path('/tmp/modules30-current79-real30-independent-foundations-actual-v1.json'),Path('/tmp/modules30-current79-real30-independent-foundations-actual-v1.log')]
for p in reader1files:add(ref(p))
r1=json.loads(reader1files[2].read_bytes());assert r1['actual_exit_code']==1 and r1['protection_errors']==[]
reader1failure={'reason':'Own first reader treated the actual proof_files dictionary as a list while checking its old502 prefix. The genuine composed full dictionary/byte inverse already succeeded; NEW2 checks dictionary insertion-order keys and every exact502 old metadata value. No author packet or source changed.','original_refs':[ref(p) for p in reader1files],'original_elapsed_seconds':r1['elapsed_seconds'],'original_semantic_findings_output_existed':False}
reader2files=[Path('/tmp/review-modules30-current79-real30-independent-foundations-v2.py'),Path('/tmp/run-review-modules30-current79-real30-independent-foundations-v2.py'),Path('/tmp/modules30-current79-real30-independent-foundations-actual-v2.json'),Path('/tmp/modules30-current79-real30-independent-foundations-actual-v2.log')]
for p in reader2files:add(ref(p))
r2=json.loads(reader2files[2].read_bytes());assert r2['actual_exit_code']==1 and r2['protection_errors']==[]
reader2failure={'reason':'Own reader2 expected flattened source/source_text SHA slots on material claim rows. The actual Module schema keeps the complete actual79 unit in entire_original_literal_decision_and_review_time.entire_actual79_record and its statement_in_prose. NEW3 checks that exact full record and statement plus page fingerprint/whole transition. No author/candidate/math change.','original_refs':[ref(p) for p in reader2files],'original_elapsed_seconds':r2['elapsed_seconds'],'original_semantic_findings_output_existed':False}
find={'original_independent_reader2_true_schema_failure':reader2failure,'original_independent_reader1_true_schema_failure':reader1failure,'status':'passed_independent_modules30_current79_real15_source30_pair_full_mechanics_scope_mapping_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'offer':ref(O),'candidate':d['candidate'],'exact_inverse_interface':d['exact_inverse_interface'],'original_semantic_inverse_interface':d['original_semantic_inverse_interface'],'actual_complete90_readiness':d['actual_complete90_readiness'],'actual_complete90_execution':d['actual_complete90_execution'],'actual_author_binding_native':d['actual_finalizer'],'source_count':15,'public_theorem_count':504,'public_declaration_count':707,'actual_canonical_command_count':30,'all15_complete_public_declaration_sets_and_real30_native_source_command_cwd_log_snapshot_time_chains_verified':True,'full_forward_inverse_and_all_current79_owned_exercise_and32_whole_literal_bindings_read':True,'exact_composed_reverse_restores_entire_raw29_dictionary_and_bytes':True,'independently_selected_original_byte_serialization':{'provisional_ensure_ascii':enc1,'raw29_ensure_ascii':enc2},'all502_old_proof_metadata_rows_and3484_declaration_prefix_exact':True,'all37_new_exercise_claims_and32_new_material_claims_approved_in_existing_independent_scopes':True,'eight_whole_exercises_approved':d['whole_exercises'],'32_whole_material_keys_approved':d['whole_material_keys'],'three_component_only_requirement_associations':d['component_only_exercise_requirements'],'whole_duality_7_5_approved':False,'whole_scenario_15_5_approved':False,'five_old_proved_gap_array_changes_approved_with_exact_completion_sidecar':d['completion_component_associations'],'GP_B2_source_probability_event_remains_assumed_not_newly_derived':True,'provided_matrix_normal_law_not_GP_conditioning_posterior':True,'original_matrix53_sidecar_pending_flag_is_historical_and_actual_final_full11_peer_is_bound':d['proof_files']['verification/lean/SafeLearning/CompleteModulesMatrixScenarioOpenObstruction30.lean']['independent_source_review'],'counts':d['counts'],'original_family_semantic_scopes_and_body_times_retained_by_exact_refs':family_scopes,'actual_native_body_times':proof_pairs,'semantic_mapping_approval_reuses_full_mathematical_peers_not_integrity_as_a_proof':True,'compiler_or_parser_invoked_by_reviewer':False,'owner_source_canonical_selection_publication_mutation':False,'coverage_complete':False,'errors':[],'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases']}
OUT.write_text(json.dumps(find,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'sources_public_pairs':[15,504,30],'whole_exercises_units':[8,32],'partial_requirements':3,'exact_inverse':True,'counts':d['counts'],'errors':[]}))
