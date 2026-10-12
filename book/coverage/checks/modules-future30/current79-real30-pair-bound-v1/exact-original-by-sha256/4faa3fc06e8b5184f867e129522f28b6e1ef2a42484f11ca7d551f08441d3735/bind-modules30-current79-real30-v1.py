from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/current79-real30-pair-bound-v1';assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(v):p=path(v['file']);assert sha(p)==v['sha256'];return p
def read(p):return json.loads(Path(p).read_bytes())
def put(p,d):
 with Path(p).open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
OP=R/'book/coverage/checks/modules-future30/current79-provisional-owner30-v1/modules30-current79-provisional-root-relative-offer-v2.json';assert sha(OP)=='8e6e6631b416a82642014f3892fdb7fef98a5a01b7a00f8d2b7ff009c97c577b';offer=read(OP);C0=checked(offer['candidate']);old=read(C0);cand=copy.deepcopy(old);IF=checked(offer['exact_inverse_interface']);iface=read(IF)
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');assert sha(CTX)=='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737';ctx=read(CTX);held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']};assert all(sha(path(n))==h for n,h in held.items())
RD=R/'book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json';assert sha(RD)=='4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e';rd=read(RD);assert rd['errors']==[] and rd['source_count']==45 and rd['actual_compiler_command_count']==90 and all(type(r['actual_exit_code']) is int and r['actual_exit_code']==0 for r in rd['actual_paired_records'])
RN=R/'reports/full-coverage/current79-canonical-pairs45-application30-execution-v1.json';assert sha(RN)=='8e3e384891e52794a493d078350abe282c8d215ff7f883eae6a3861c4eda77ee';rn=read(RN);assert rn['status']=='passed' and type(rn['actual_exit_code']) is int and rn['actual_exit_code']==0;checked({'file':rn['log'],'sha256':rn['log_sha256']})
assert len(offer['proof_files'])==15 and sum(r['theorem_count'] for r in offer['proof_files'].values())==504
B.mkdir(parents=True);aliases=copy.deepcopy(offer['original_closed_byte_aliases']);req=copy.deepcopy(offer['required_evidence_artifacts_sha256']);changes=[]
def register(p):
 p=Path(p);h=sha(p)
 if p.is_relative_to(R) and p.resolve().is_relative_to(R) and not p.is_symlink():q=p
 else:
  q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():
   with q.open('xb') as f:f.write(p.read_bytes())
  assert sha(q)==h
 rr=ref(q);aliases[str(p)]=rr
 if p.is_relative_to(R):aliases[p.relative_to(R).as_posix()]=rr
 req[rr['file']]=h;return rr

def close(v):
 if isinstance(v,list):return [close(x) for x in v]
 if isinstance(v,dict):
  if isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str):
   p=path(v['file']);assert sha(p)==v['sha256'];rr=register(p);return {**{k:close(x) for k,x in v.items() if k not in ['file','sha256','bytes']},**rr}
  return {k:close(x) for k,x in v.items()}
 return v

def change(parts,v):
 d=cand
 for k in parts[:-1]:d=d[k]
 k=parts[-1];exists=k in d if isinstance(d,dict) else True;before=copy.deepcopy(d[k]) if exists else None
 if exists and before==v:return
 changes.append({'path':parts,'existed':exists,'before':before});d[k]=copy.deepcopy(v)
# Normalize only values introduced by the provisional forward interface. Every inherited proof row remains exact.
for patch in iface['restore_patches_in_reverse_order']:
 parts=patch['path'];v=cand
 for k in parts:v=v[k]
 change(parts,close(v))
newproof={}
for source,meta0 in offer['proof_files'].items():
 pair=[r for r in rd['actual_paired_records'] if r['source']['file']==source];assert len(pair)==2 and [r['kind'] for r in pair]==['standalone','named'];meta=copy.deepcopy(cand['proof_files'][source]);assert meta['sha256']==pair[0]['source']['sha256']==pair[1]['source']['sha256']==sha(R/source)
 for pr in pair:
  for key in ['source','actual_record','raw_log','source_snapshot']:checked(pr[key]);register(checked(pr[key]))
  native=read(checked(pr['actual_record']));assert native['exit_code']==0 and native['source']==source and native['source_sha256_before']==native['source_sha256_after']==meta['sha256'];assert native['actual_workdir']==str(R/'verification/lean')
  command=['lake','env','lean','SafeLearning/'+Path(source).name] if pr['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem];assert native['command']==command and native['log']==pr['raw_log']['file'] and native['log_sha256']==pr['raw_log']['sha256']
 row=next(x for x in rd['sources'] if x['canonical_source']==source);assert row['public_declarations']==meta['public_declarations'];ns=[x['name'] for x in row['public_declarations'] if x['kind'] in ['theorem','lemma']];assert ns==meta['public_theorem_names']==meta['mapped_named_declarations'] and len(ns)==meta['theorem_count']
 evidence={r[k]['file']:r[k]['sha256'] for r in pair for k in ['actual_record','raw_log','source_snapshot']};evidence[meta['independent_source_review']['file']]=meta['independent_source_review']['sha256'];evidence[meta['original_actual_tmp_trial']['file']]=meta['original_actual_tmp_trial']['sha256']
 meta.update({'actual_pair':pair,'canonical_pair_pending':False,'selection_scope':'direct_reviewed_reference_with_actual_canonical_standalone_and_named_pairs','standalone_compile_status':'passed_source_matched_actual_canonical_pair','evidence_sha256':evidence,'actual_Root_complete90_readiness':ref(RD),'actual_Root_complete90_execution':ref(RN)});change(['proof_files',source],meta);newproof[source]=meta
for i,e in enumerate(cand['exercises']):
 for j,z in enumerate(e['claims']):
  if 'reviewed_owner30_transition' in z:
   zz=copy.deepcopy(z['reviewed_owner30_transition']);zz['canonical_pair_pending']=False;zz['actual_Root_complete90_readiness']=ref(RD);change(['exercises',i,'claims',j,'reviewed_owner30_transition'],zz)
 if 'entire_literal_closure30' in e:
  zz=copy.deepcopy(e['entire_literal_closure30']);zz['actual_canonical_pairs_completed']=True;zz['owner_installation_pending']=True;zz['actual_Root_complete90_readiness']=ref(RD);change(['exercises',i,'entire_literal_closure30'],zz)
for i,z in enumerate(cand['material_claims']):
 if 'reviewed_owner30_transition' in z:
  zz=copy.deepcopy(z['reviewed_owner30_transition']);zz['canonical_pair_pending']=False;zz['actual_Root_complete90_readiness']=ref(RD);change(['material_claims',i,'reviewed_owner30_transition'],zz)
zz=copy.deepcopy(cand['reviewed_work_integration30_current79_candidate']);zz.update({'status':'prepared_isolated_actual79_pair_bound_eight_whole_exercises32_whole_units_and_bounded_components_pending_independent_final_mapping','canonical_pair_pending':False,'actual_Root_complete90_readiness':ref(RD),'actual_Root_complete90_execution':ref(RN)});change(['reviewed_work_integration30_current79_candidate'],zz)
change(['current_identity_binding_validation','status'],'actual79_owned_identity_and_real30_pairs_verified_independent_mapping_and_owner_installation_pending')
change(['actual_current79_pair_binding30'],{'status':'actual15_source30_canonical_commands_bound_completed90_root_pipeline_independent_final_mapping_pending','bound_at_utc':datetime.now(timezone.utc).isoformat(),'original_provisional_candidate':ref(C0),'original_provisional_root_offer':ref(OP),'actual_complete90_readiness':ref(RD),'actual_complete90_execution':ref(RN),'own_source_count':15,'own_theorem_count':504,'own_public_name_count':707,'own_actual_command_count':30,'owner_installation_and_aggregate_selection_pending':True,'coverage_complete':False})
CAND=B/'modules30-current79-real30-pair-bound-candidate-v1.json';put(CAND,cand)
reverse=copy.deepcopy(cand)
for item in reversed(changes):
 d=reverse
 for k in item['path'][:-1]:d=d[k]
 if item['existed']:d[item['path'][-1]]=copy.deepcopy(item['before'])
 else:del d[item['path'][-1]]
assert reverse==old and (json.dumps(reverse,indent=2,ensure_ascii=False)+'\n').encode()==C0.read_bytes()
for item in reversed(iface['restore_patches_in_reverse_order']):
 d=reverse
 for k in item['path'][:-1]:d=d[k]
 if item['existed']:d[item['path'][-1]]=copy.deepcopy(item['before'])
 else:del d[item['path'][-1]]
BASE=checked(iface['base']);assert (json.dumps(reverse,indent=2,ensure_ascii=False)+'\n').encode()==BASE.read_bytes();baseline=read(BASE);assert all(cand['proof_files'][n]==m for n,m in baseline['proof_files'].items()) and cand['declarations'][:3484]==baseline['declarations']
INV=B/'modules30-current79-real30-canonical-metadata-and-alias-inverse-v1.json';put(INV,{'status':'exact_real30_metadata_and_new_value_byte_alias_reverse_to_provisional_then_entire_raw29_verified','candidate':ref(CAND),'provisional_candidate':ref(C0),'restore_patches_in_reverse_order':changes,'original_semantic_forward_inverse_interface':ref(IF),'exact_whole_raw29_byte_inverse_verified':True,'all502_old_proof_metadata_and3484_decl_prefix_exact':True,'eight_whole_exercises32_whole_units_and_three_component_requirements_math_statuses_and_counts_unchanged':True,'no_prospective_original_peer_body_or_time_rewritten':True,'coverage_complete':False})
for p in [OP,C0,IF,INV,CAND,RD,RN,R/rn['log'],Path(__file__),CTX]:register(p)
O=B/'modules30-current79-real30-pair-bound-offer-draft-v1.json';put(O,{'status':'actual79_modules30_real15_source30_pair_bound_mapping_pending_independent_final_mapping','errors':[],'candidate':ref(CAND),'inventory':offer['inventory'],'inventory_sha256':offer['inventory_sha256'],'source_sha256':cand['source_sha256'],'proof_files':newproof,'exact_inverse_interface':ref(INV),'original_semantic_inverse_interface':ref(IF),'identity_sidecar':close(offer['identity_sidecar']),'completion_component_associations':close(offer['completion_component_associations']),'original_provisional_root_offer':ref(OP),'original_owner':offer['original_owner'],'actual_complete90_readiness':ref(RD),'actual_complete90_execution':ref(RN),'whole_exercises':offer['whole_exercises'],'whole_material_keys':offer['whole_material_keys'],'component_only_exercise_requirements':offer['component_only_exercise_requirements'],'counts':cand['counts'],'required_evidence_artifacts_sha256':req,'original_closed_byte_aliases':aliases,'actual_canonical_pairs_pending':False,'independent_final_mapping_pending':True,'installation_ready':False,'live_owner_source_selection_publication_changes':False,'coverage_complete':False})
assert all(sha(path(n))==h for n,h in held.items());print(json.dumps({'offer':ref(O),'candidate':ref(CAND),'inverse':ref(INV),'aliases':len(aliases),'required_refs':len(req),'old502_proof_metadata_exact':True,'source_count':15,'actual_pairs':30,'new_theorems':504,'counts':cand['counts']}))
