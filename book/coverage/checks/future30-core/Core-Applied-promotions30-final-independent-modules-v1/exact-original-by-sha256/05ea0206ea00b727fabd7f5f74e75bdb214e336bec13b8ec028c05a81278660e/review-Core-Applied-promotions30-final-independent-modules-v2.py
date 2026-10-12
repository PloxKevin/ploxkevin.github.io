from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/Core-Applied-promotions30-final-independent-modules-peer-v2.json');assert not O.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(v):p=path(v['file']);assert p.is_file() and sha(p)==v['sha256'];assert 'bytes' not in v or p.stat().st_size==v['bytes'];return p
def read(v):return json.loads(checked(v).read_bytes())
def encoded(d):return (json.dumps(d,indent=2,ensure_ascii=False)+'\n').encode()
P=R/'book/coverage/checks/future30-applied/owner30-source79-real-pairs-v3/Core1-Applied2-promotions30-source79-real90-pair-bound-forward-inverse-final-review-offer-v3.json';assert sha(P)=='5696d55ff9cb71bd32b49d8a68325b6be2cd3edc29de703d725fc74c7e152d23';offer=json.loads(P.read_bytes());I=read(offer['exact_raw29_forward_inverse_patch']);base={k:read(v) for k,v in offer['original_owner29_physical_refs'].items()};cand={k:read(v) for k,v in offer['candidate_refs'].items()}
for role,patches in I['patches'].items():
 f=copy.deepcopy(base[role]);r=copy.deepcopy(cand[role])
 for x in patches:
  d=f
  for k in x['path'][:-1]:d=d[k]
  k=x['path'][-1]
  if x['op']=='replace':assert d[k]==x['before'];d[k]=copy.deepcopy(x['after'])
  elif x['op']=='add':assert k not in d;d[k]=copy.deepcopy(x['after'])
  elif x['op']=='remove':assert d[k]==x['before'];del d[k]
  else:raise AssertionError(x['op'])
 assert f==cand[role] and encoded(f)==checked(offer['candidate_refs'][role]).read_bytes()
 for x in reversed(patches):
  d=r
  for k in x['path'][:-1]:d=d[k]
  k=x['path'][-1]
  if x['op']=='replace':assert d[k]==x['after'];d[k]=copy.deepcopy(x['before'])
  elif x['op']=='add':assert d[k]==x['after'];del d[k]
  else:d[k]=copy.deepcopy(x['before'])
 assert r==base[role] and encoded(r)==checked(offer['original_owner29_physical_refs'][role]).read_bytes()
for role in ['core','applied']:
 assert all(cand[role]['proof_files'][k]==v for k,v in base[role]['proof_files'].items());assert cand[role]['current_inventory_sha256']==offer['inventory_sha256']
assert len(base['core']['proof_files'])==185 and len(base['applied']['proof_files'])==312 and len(cand['core']['proof_files'])==186 and len(cand['applied']['proof_files'])==314
assert cand['applied']['exercises']==base['applied']['exercises'] and len(cand['applied']['exercises'])==128
assert cand['applied-promotions']['exercises']==base['applied-promotions']['exercises']
corebase={x['inventory_key']:x for x in base['core']['exercises']};corecand={x['inventory_key']:x for x in cand['core']['exercises']};assert corebase.keys()==corecand.keys() and len(corecand)==92
changedcore=[k for k in corebase if {f:v for f,v in corebase[k].items() if f!='source_sha256'}!={f:v for f,v in corecand[k].items() if f!='source_sha256'}];assert changedcore==['cmdp.html::exercise-21'];assert corecand['cmdp.html::exercise-21']['status']=='complete_math';assert corecand['barriers.html::exercise-16']==corebase['barriers.html::exercise-16'] and corecand['barriers.html::exercise-16']['status']=='partial'
INV=read(offer['inventory']);U={u['key']:u for u in INV['material_source_units']};E={e['key']:e for e in INV['exercises']};assert offer['inventory_sha256']=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
for role in ['core','applied']:
 for p,h in cand[role]['source_sha256'].items():assert sha(path(p))==h
scope=offer['original14_whole_material_decisions_and_full_Exercise21_scope'];assert len(scope)==14;individual=[]
for d in scope:
 role=d['owner'];key=d['inventory_key'];row=[r for r in cand[role]['material_claims'] if r['id']==d['id']];oldrow=[r for r in base[role]['material_claims'] if r['id']==d['id']];assert len(row)==len(oldrow)==1;row=row[0];oldrow=oldrow[0];assert oldrow['status']=='pending' and row['status']==d['candidate_status'] and row['remaining_gaps']==[]
 peer=read(d['full_independent_peer']);assert peer['status'].startswith('passed_') and peer.get('errors',[])==[];assert row.get('source_text',row.get('statement_in_prose'))==U[key]['source_text'] or row['statement_in_prose']==U[key]['source_text'];assert row['source_unit_keys']==[key]
 if d['candidate_status']=='not_a_formal_claim':assert row['lean_declarations']==[] and role=='applied' and key in {f'primer-probability.html::node-{n}' for n in [220,280,431,541,568,700,849,1037]}
 individual.append({'owner':role,'key':key,'status':d['candidate_status'],'actual79_text_sha256':U[key]['text_sha256'],'original_full_semantic_peer':d['full_independent_peer'],'whole_following_body_promoted_by_NF_heading':False})
assert sum(x['status']=='not_a_formal_claim' for x in individual)==8 and sum(x['owner']=='core' for x in individual)==2
for role in ['core','applied']:
 changed_ids={d['id'] for d in scope if d['owner']==role};b={r['id']:r for r in base[role]['material_claims']};c={r['id']:r for r in cand[role]['material_claims']};assert b.keys()==c.keys()
 for k,r in b.items():
  if k in changed_ids:continue
  allowed={'source_sha256'}
  if set(r.get('source_unit_keys',[])) & {'cmdp.html::node-750','cmdp.html::node-752'}:allowed|={'source_text','text_sha256'}
  assert {f:v for f,v in c[k].items() if f not in allowed}=={f:v for f,v in r.items() if f not in allowed}
  if c[k].get('source') in INV['source_sha256']:assert c[k]['source_sha256']==INV['source_sha256'][c[k]['source']]
# Core corrected CMDP full literal is actually Source79; Applied probability pages and all exercise data remain unchanged.
assert corecand['cmdp.html::exercise-21']['source_text']==E['cmdp.html::exercise-21']['source_text']
assert offer['canonical_owner_role_counts']=={'core':{'sources':1,'theorems':58},'applied':{'sources':2,'theorems':34}}
RD=read(offer['actual_root45_readiness']);RN=read(offer['actual_root90_primary_native']);assert RD['errors']==[] and RD['source_count']==45 and RD['actual_compiler_command_count']==90 and RN['status']=='passed' and type(RN['actual_exit_code']) is int and RN['actual_exit_code']==0
NAMES=R/'book/coverage/lean_names.py';spec=importlib.util.spec_from_file_location('CoreApplied30_independent_names',NAMES);names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);allnames=[];commands=0
for role,mapping in offer['new_proof_files_by_owner'].items():
 for source,p in mapping.items():
  assert cand[role]['proof_files'][source]==p and sha(R/source)==p['sha256'];index=names.declarations((R/source).read_text());ns=[v['name'] for v in index if v['kind'] in ['theorem','lemma']];assert ns==p['public_theorem_names']==p['mapped_named_declarations'] and len(ns)==p['theorem_count'];allnames+=ns
  pair=p['actual_pair'];assert pair==[r for r in RD['actual_paired_records'] if r['source']['file']==source] and [r['kind'] for r in pair]==['standalone','named']
  for r in pair:
   for k in ['source','actual_record','raw_log','source_snapshot']:checked(r[k])
   n=read(r['actual_record']);assert type(n['exit_code']) is int and n['exit_code']==r['actual_exit_code']==0 and n['source']==source and n['source_sha256_before']==n['source_sha256_after']==p['sha256'] and n['actual_workdir']==str(R/'verification/lean');expected=['lake','env','lean','SafeLearning/'+Path(source).name] if r['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem];assert n['command']==expected and n['log']==r['raw_log']['file'] and n['log_sha256']==r['raw_log']['sha256'];commands+=1
  for pth,h in p['evidence_sha256'].items():assert sha(path(pth))==h
assert len(allnames)==len(set(allnames))==92 and commands==6
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');ctx=json.loads(CTX.read_bytes());pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']};assert all(sha(path(n))==h for n,h in pins.items())
for n,h in offer['required_evidence_artifacts_sha256'].items():assert not Path(n).is_absolute() and path(n).resolve().is_relative_to(R) and sha(path(n))==h and n not in ctx['owners_sha256']
for original,v in offer['original_closed_byte_aliases'].items():checked(v)
D={'original_independent_reader1_true_schema_failure':ref('/tmp/Core-Applied-promotions30-final-independent-modules-actual-v1.json'),'reader1_failure_scope':'Own first genuine reader treated Source79 page SHA rebinding on sibling CMDP exercises as mathematical changes. NEW2 excludes only those explicit identity fields, verifies current hashes, and uses the real partial barriers exercise16 rather than complete cmdp exercise16. Sibling750/752 literal text slots are also explicit identity rebindings; every old semantic field/body/time is retained. No producer/candidate/math change or fabricated failure.','status':'passed_independent_Core_Applied_promotions30_current79_real90_three_source6_pair_full_forward_inverse_owned_scope_mapping_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_refs':offer['candidate_refs'],'offer':ref(P),'exact_inverse_interface':offer['exact_raw29_forward_inverse_patch'],'original_owner29_refs':offer['original_owner29_physical_refs'],'all_three_forward_and_inverse_dictionaries_and_entire_original_UTF8_bytes_verified':True,'old_Core185_and_Applied312_proof_metadata_exact':True,'all128_Applied_exercises_and_prior_promotions_exercises_exact':True,'all92_Core_exercises_retained_only_actual_full21_completed':True,'Core_barriers_exercise16_still_partial_exact':True,'all14_entire_physical_literal_scope_decisions':individual,'Core750752_actual79_whole_approved_and_Exercise21_complete':True,'Applied281383385386_whole_approved':True,'eight_physical_headings_NF_only_following_math_statuses_unchanged':True,'all_unchanged_old_material_rows_claim_bodies_times_exact':True,'shared_Monitoring58_owned_only_by_Core':True,'own_distinct_source_count':3,'own_public_theorems':92,'own_actual_compiler_commands':6,'all_names_source_snapshot_command_cwd_raw_native0_and_evidence_hashes_checked':True,'actual_complete90_readiness':offer['actual_root45_readiness'],'actual_complete90_execution':offer['actual_root90_primary_native'],'physical_closure_refs_checked':len(offer['required_evidence_artifacts_sha256']),'actual79_guard_context':ref(CTX),'producer_compiler_owner_Source_or_publication_changes':False,'coverage_complete':False,'live_integration_selection_aggregate_and_publication_remain_Root_actions':True}
O.write_text(json.dumps(D,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(O),'owners':3,'sources':3,'names':92,'actual_commands':6,'all14_scopes':True}))
