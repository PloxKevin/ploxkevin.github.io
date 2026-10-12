from pathlib import Path
from collections import Counter
import copy,hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');O=R/'book/coverage/checks/future31-foundations/current81-four-family-disjoint-inverse-v3/foundations31-current81-real8-pair-bound-final-offer-v4.json';OUT=Path('/tmp/foundations31-real8-final-mapping-independent-modules-findings-v4.json');C=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(x):
 p=Path(x['file']);return p if p.is_absolute()else R/p
def ref(p):
 p=Path(p);return{'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(O)=='e4d3f5faf77d6eb8e44ea12bd04d374456c52b1d53ccc0b1d1788542b74f9714';o=json.loads(O.read_bytes());meta=o['metadata'];candidate=path(o['candidate']);original=path(meta['original_whole_owner30']);inverse=path(o['exact_inverse'])
for x in [o['candidate'],o['exact_inverse'],meta['original_whole_owner30']]:assert sha(path(x))==x['sha256']
assert sha(candidate)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'and sha(original)=='4e84206199aa241e1e4ee95f59062bcbe78035bb6443281e398a02c1b3f3ae03'
for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h
for original_name,x in o['all_original_byte_aliases'].items():
 copies=[x[k]for k in ['original_byte_copy','already_durable_original_byte_alias']if k in x];assert len(copies)==1
 assert sha(path(x['original']))==x['original']['sha256']==sha(path(copies[0]))==copies[0]['sha256']
context=json.loads(C.read_bytes());assert sha(C)=='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
guards={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
common_path=path(meta['actual_common12_readiness']);assert sha(common_path)=='c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520';common=json.loads(common_path.read_bytes());assert common['errors']==[]and common['actual_compiler_command_count']==12 and common['source_count']==6
for s in common['sources']:guards[s['canonical_source']]=s['original_tmp_source']['sha256']
def guard():
 assert sha(O)=='e4d3f5faf77d6eb8e44ea12bd04d374456c52b1d53ccc0b1d1788542b74f9714'and sha(C)=='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
 for n,h in guards.items():
  p=R/n;assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R)and sha(p)==h,n
 for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h
guard();old=json.loads(original.read_bytes());new=json.loads(candidate.read_bytes());iv=json.loads(inverse.read_bytes())
def get(d,p):
 for k in p:d=d[k]
 return d
def put(d,p,v):
 for k in p[:-1]:d=d[k]
 d[p[-1]]=copy.deepcopy(v)
fwd=copy.deepcopy(old)
for row in iv['patches']:assert get(fwd,row['pointer'])==row['before'];put(fwd,row['pointer'],row['after'])
field=iv['appended_field'];assert field not in old and iv['appended_field_after']==new[field];fwd[field]=copy.deepcopy(new[field]);assert fwd==new
ptrs=[tuple(x['pointer'])for x in iv['patches']]
assert all(not (a==b[:len(a)]or b==a[:len(b)])for i,a in enumerate(ptrs)for b in ptrs[i+1:])
back=copy.deepcopy(new);del back[field]
for row in reversed(iv['patches']):assert get(back,row['pointer'])==row['after'];put(back,row['pointer'],row['before'])
assert back==old
encodings=[(json.dumps(back,indent=2,ensure_ascii=a)+'\n').encode()for a in [True,False]];assert original.read_bytes()in encodings
assert new['proof_files'][:len(old['proof_files'])]==old['proof_files']and len(old['proof_files'])==289 and len(new['proof_files'])==293
assert set(new['proof_sha256'])-set(old['proof_sha256'])==set(meta['proof_files'])
for n,h in old['proof_sha256'].items():assert new['proof_sha256'][n]==h
assert len(new['exercises'])==len(old['exercises'])==119
semantic_ex_changed=[]
for a,b in zip(old['exercises'],new['exercises']):
 aa=copy.deepcopy(a);bb=copy.deepcopy(b)
 for k in ['source_sha256']:
  aa.pop(k,None);bb.pop(k,None)
 assert aa==bb
assert meta['candidate_whole_keys']==['primer-linalg.html::node-421','primer-basics.html::node-1306','primer-basics.html::node-1271','primer-basics.html::node-1437','primer-basics.html::node-1452']
keys=set(meta['candidate_whole_keys']);changed=[];inv=json.loads(path(meta['actual_source81_inventory']).read_bytes());units={x['key']:x for x in inv['material_source_units']}
assert len(new['material_claims'])==len(old['material_claims'])
for index,(a,b)in enumerate(zip(old['material_claims'],new['material_claims'])):
 aa=copy.deepcopy(a);bb=copy.deepcopy(b)
 for k in ['source_sha256','source_text','source_text_sha256']:
  aa.pop(k,None);bb.pop(k,None)
 if aa!=bb:
  assert a['status']=='pending'and b['status']=='proved'and len(b['source_unit_keys'])==1 and b['source_unit_keys'][0]in keys
  assert b['remaining_gaps']==[]and b['lean_declarations'];changed.append({'index':index,'before':a,'after':b})
 for key in b['source_unit_keys']:
  if key in units and b.get('source')==units[key]['source']:
   assert b['source_sha256']==units[key]['source_sha256']
   if len(b['source_unit_keys'])==1:assert b['source_text']==units[key]['source_text']and b['source_text_sha256']==units[key]['text_sha256']
assert len(changed)==5 and {x['after']['source_unit_keys'][0]for x in changed}==keys
assert Counter(x['status']for x in new['material_claims'])=={'not_a_formal_claim':535,'proved':1213,'pending':375}
assert new['counts']['material_claim_statuses']==dict(Counter(x['status']for x in new['material_claims']))
assert meta==new[field]and meta['direct_new_source_count']==4 and meta['direct_new_public_theorems']==41 and meta['direct_new_definitions']==4 and meta['canonical_pairs_pending']is False
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
fullpeerrefs=[];pairrefs=[];alltheorems=[];allpublic=[];familyfindings=[]
for f in meta['families']:
 source=R/f['prospective_canonical_target'];assert sha(source)==f['final_actual_passed_TMP_source']['sha256'];text=source.read_text();ds=lean_names.declarations(text);thms=[x['name']for x in ds if x['kind']in ['theorem','lemma']];defs=[x['name']for x in ds if x['kind']not in ['theorem','lemma']]
 assert thms==f['public_theorem_names']and defs==f['public_definition_names']and len(thms)==f['direct_public_theorem_count']and len(defs)==f['direct_public_definition_count']
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(text))
 p=path(f['independent_full_math_scope_peer']);assert sha(p)==f['independent_full_math_scope_peer']['sha256'];peer=json.loads(p.read_bytes());assert peer['errors']==[]and peer['status'].startswith('passed_');fullpeerrefs.append(ref(p))
 if f['id']=='spectral_induction11':
  assert peer['current421_whole_literal_approved']is False and peer['prospective_corrected421_whole_mathematics_approved']is True
  assert units['primer-linalg.html::node-421']['source_text']==peer['entire_current_and_prospective_literal_records']['primer-linalg.html::node-421']['entire_prospective']['source_text']
 elif f['id']=='growth_examples_logdet10':
  assert peer['entire_node_decision']['entire_exact_literal_approved']is True and peer['entire_node_decision']['remaining_mathematical_gaps']==[]
  assert units['primer-basics.html::node-1271']['source_text']==peer['entire_exact_literal']['source_text']
 elif f['id']=='logcube_crossover13':
  assert peer['individual_decisions'][0]['current_whole_literal_approved']is True
 elif f['id']=='explorer_captions7':
  assert all(x['current_whole_literal_approved']is True and x['remaining_gaps']==[]for x in peer['individual_decisions'])
 pm=meta['proof_files'][f['prospective_canonical_target']];assert pm['sha256']==sha(source)and pm['theorem_count']==len(thms)and pm['public_theorem_names']==thms and pm['mapped_named_declarations']==[x['name']for x in ds]
 assert new['proof_sha256'][f['prospective_canonical_target']]==sha(source)
 for k,pair in pm['actual_pair'].items():
  assert k in ['standalone','named']and pair['kind']==k and pair['actual_exit_code']==0
  for rk in ['source','actual_record','raw_log','source_snapshot','actual_helper_invocation_log']:assert sha(path(pair[rk]))==pair[rk]['sha256'];pairrefs.append(pair[rk])
  native=json.loads(path(pair['actual_record']).read_bytes());assert native['exit_code']==0 and native['source_unchanged']and native['source_sha256_before']==native['source_sha256_after']==sha(source)
  assert native['actual_workdir']==str(R/'verification/lean')and native['log_sha256']==pair['raw_log']['sha256']
  expected=['lake','env','lean','SafeLearning/'+source.name]if k=='standalone'else['lake','build','SafeLearning.'+source.stem]
  assert native['command']==expected and pair['original_checked_at_utc']==native['checked_at_utc']and pair['original_elapsed_seconds']==native['elapsed_seconds']
  assert sha(path(pair['source_snapshot']))==sha(source)
  assert any(all(x['actual_record'][k]==pair['actual_record'][k]for k in ['file','sha256'])for x in common['actual_paired_records'])
  assert pm['evidence_sha256'][pair['actual_record']['file']]==pair['actual_record']['sha256']and pm['evidence_sha256'][pair['raw_log']['file']]==pair['raw_log']['sha256']
 for h in f['genuine_compiler_histories_preserved']:
  nn=json.loads(path(h['actual_native']).read_bytes());assert nn['actual_exit_code']==h['actual_exit_code']and nn['protection_errors']==[]
  for hk,nk in [('original_source','source_sha256_before'),('original_snapshot','source_snapshot_sha256'),('original_raw_log','raw_log_sha256')]:assert sha(path(h[hk]))==h[hk]['sha256']==nn[nk]
  for hk,nk in [('original_actual_command','actual_command'),('original_actual_workdir','actual_workdir'),('original_started_at_utc','started_at_utc'),('original_finished_at_utc','finished_at_utc'),('original_elapsed_seconds','elapsed_seconds')]:assert h[hk]==nn[nk]
  assert len(re.findall(rb'^.*?:\d+:\d+: warning:',path(h['original_raw_log']).read_bytes(),re.M))==h['emitted_diagnostic_warning_headers']
 alltheorems+=thms;allpublic+=[x['name']for x in ds];familyfindings.append({'family':f['id'],'canonical_source':ref(source),'all_public_declarations':ds,'full_scope_peer':ref(p),'exact_literal_scope_correspondence_approved':True})
assert len(alltheorems)==41 and len(allpublic)==45 and len(set(allpublic))==45
for row in changed:assert set(row['after']['lean_declarations'])<=set(alltheorems)
final=json.loads(path(o['actual_finalizer']).read_bytes());assert final['actual_exit_code']==0 and final['protection_errors']==[]and final['protected_inputs_sha256_before']==final['protected_inputs_sha256_after']
for p,h in final['helper_sha256_before'].items():assert sha(path(o['actual_finalizer_original_byte_aliases'][p]))==h==final['helper_sha256_after'][p]
assert sha(path(o['actual_finalizer_original_byte_aliases'][final['log']]))==final['log_sha256']
guard()
findings={'status':'passed_independent_foundations31_current81_real8_five_whole_keys_full_mapping_review','errors':[],'reviewer':'/root/modules_finish28','offer':ref(O),'candidate':o['candidate'],'exact_inverse':o['exact_inverse'],'original_whole_owner30':meta['original_whole_owner30'],'full_forward_and_reverse_JSONpatch_checked':True,'entire_original_owner30_UTF8_bytes_recovered':True,'all119_exercises_and289_old_proof_files_and_old_proved_semantics_histories_preserved':True,'exact_only_five_pending_rows_completed':changed,'five_current_whole_keys':meta['candidate_whole_keys'],'all_current81_scoped_literals_and_qualified421_match_full_semantic_peers':True,'four_families41_theorems45_public_names':familyfindings,'all_eight_literal_native_command_cwd_source_snapshot_log_time_chains_verified':True,'actual_pair_refs':pairrefs,'source81_context':ref(C),'actual_common12_readiness':meta['actual_common12_readiness'],'original_author_finalizer':o['actual_finalizer'],'original_author_finalizer_aliases':o['actual_finalizer_original_byte_aliases'],'original_all_physical_closure':o['required_evidence_artifacts_sha256'],'current_input_guard_sha256':guards,'counts_independently_derived':dict(Counter(x['status']for x in new['material_claims'])),'original_pending_provisional_and_all_prior_semantic_peer_body_time_preserved':True,'no_generic_neighbor_components_or_parent_exercise_promotion':True,'all_full_mapping_approved':True,'independent_final_mapping_approved':True,'current_owner_source_canonical_selection_publication_mutation':False,'coverage_complete':False,'scope':'Final candidate mapping and actual four-source/eight-command associations only. Full literal semantics come from the exact already-closed independent full mathematical peers;421 is bound to actualSource80-qualified text. Original pending provisional verdict, original35/other historical decisions and all native times remain unchanged. No new aggregate or owner installation is inferred.'}
with OUT.open('x')as f:json.dump(findings,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'all_full_mapping_approved':True,'errors':[]}))
