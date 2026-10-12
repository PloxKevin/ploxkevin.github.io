from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,re,subprocess
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future29/current65-pair-bound-v1';assert not B.exists()
PENDING=Path('/tmp/modules29-current65-two-whole-candidate-v1/modules29-current65-two-whole-candidate-v1.json')
PO=Path('/tmp/modules29-current65-two-whole-candidate-v1/modules29-current65-two-whole-offer-draft-v1.json')
OLD_OFFER=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1/modules28-current60-three-stale-gap-repair-final-offer-v2.json'
READY=R/'book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json'
OUTER=R/'reports/full-coverage/current65-canonical-pairs10-application29-execution-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):p=Path(p);return {'file':p.relative_to(R).as_posix(),'sha256':H(p),'bytes':p.stat().st_size}
def put(p,raw):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(raw)
def putj(p,d):put(p,(json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
assert H(PENDING)=='9dedf660822a6d3df2ee8b61724dc3c0f0c2cf6b7c667c8d3b413d3e3e1f387a'
assert H(PO)=='f58ef07a24743ac974dc58fb4119dae557b376f57bd4657c3adcd58c87bb2fad'
assert H(OLD_OFFER)=='f8a7626082ff01bd90fa09fa4d5d071a0cb6e196240107a4ac774849f4eecdd3'
assert H(READY)=='69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917'
ctx=J('/tmp/root_tmp_lean_current65_owner28_context_v1.json');pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256']}
def guard():
 for n,h in pins.items():assert H(P(n))==h,n
 guard_new={r['source']['file']:r['source']['sha256']for r in J(READY)['actual_paired_records']}
 for n,h in guard_new.items():assert H(P(n))==h,n
guard();pending=J(PENDING);po=J(PO);oldoffer=J(OLD_OFFER);old=J(R/'reports/full-coverage/checkpoint-28/book/coverage/modules.json');ready=J(READY);outer=J(OUTER)
assert ready['errors']==[]and ready['actual_compiler_command_count']==20 and ready['source_count']==10
assert outer['actual_exit_code']==0
inherited=dict(oldoffer['required_evidence_artifacts_sha256']);assert len(inherited)==1006
mutable={str(R/'book/coverage'/n)for n in ['core.json','foundations.json','applied.json','applied-promotions.json','modules.json']}
alias_sources={**oldoffer['original_closed_byte_aliases'],**ready['original_closed_byte_aliases']}
# Index exact existing byte archives to resolve historical typed references without changing native bodies.
archives={}
for n,h in inherited.items():archives.setdefault(h,[]).append(R/n)
for n in subprocess.check_output(['rg','--files','book/coverage/checks','reports/full-coverage'],cwd=R,text=True).splitlines():
 for m in re.finditer(r'(?:^|/)([0-9a-f]{64})(?:/|\.json$)',n):archives.setdefault(m.group(1),[]).append(R/n)
for n,h in inherited.items():assert not Path(n).is_absolute()and(R/n).resolve().is_relative_to(R.resolve())and H(R/n)==h,n
required=dict(inherited);aliases=copy.deepcopy(oldoffer['original_closed_byte_aliases']);refs={};queue=[];seen=set();resolutions=[]
def resolve(n,h):
 p=P(n)
 if str(p)not in mutable and p.is_file()and H(p)==h:return p
 for key in [n,str(p)]:
  if key in alias_sources:
   a=alias_sources[key];q=P(a['file'])
   if a['sha256']==h and q.is_file()and H(q)==h:return q
 for q in archives.get(h,[]):
  if q.is_file()and H(q)==h:return q
 raise AssertionError(('no exact original bytes',n,h))
def register(n,h,scan=True):
 p=resolve(n,h);key=str(p)
 refs.setdefault(key,h);assert refs[key]==h
 if p!=P(n):resolutions.append({'original_file':n,'sha256':h,'exact_original_archive':str(p)})
 if scan and p.suffix=='.json'and p.stat().st_size<10_000_000 and key not in seen and p not in [PENDING,PO]and p.name not in ['inventory.json','material-corrections.json']:
  seen.add(key);queue.append(p)
 # Both original spellings are fixed to the same durable byte alias later.
 refs.setdefault(n,h);refs.setdefault(str(P(n)),h)
 return p
def discover(v,field=''):
 if isinstance(v,dict):
  if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str)and re.fullmatch('[0-9a-f]{64}',v['sha256']):register(v['file'],v['sha256'])
  for k,x in v.items():
   if field in ['required_evidence_artifacts_sha256','closed_evidence_sha256','closed_evidence_artifacts_sha256']and isinstance(x,str)and re.fullmatch('[0-9a-f]{64}',x)and '/'in k:register(k,x,False)
   discover(x,k)
  for k,hk in [('helper','helper_sha256_before'),('runner','runner_sha256'),('log','log_sha256'),('raw_log','raw_log_sha256'),('source_snapshot','source_snapshot_sha256'),('source','source_sha256_before')]:
   if isinstance(v.get(k),str)and isinstance(v.get(hk),str):register(v[k],v[hk],False)
 elif isinstance(v,list):
  for x in v:discover(x,field)
seeds=[PO,PENDING,OLD_OFFER,READY,OUTER,Path(__file__),Path('/tmp/run-modules29-current65-durable-pair-binding-v1.py'),Path('/tmp/prepare-modules29-current65-two-whole-candidate-v1.py'),Path('/tmp/run-modules29-current65-two-whole-candidate-preparation-v1.py'),Path('/tmp/modules29-current65-two-whole-candidate-preparation-actual-v1.json'),R/'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/modules-scalar-lipsdp42-full-scope-independent-review-request29-current64-v3.json',R/'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/modules-source65-current64-narrow-independent-review-request29-v3.json',R/'book/coverage/checks/modules-future29/leaky-qc30-and-source63-v1/modules-leaky-qc30-full-scope-independent-review-request28-v1.json']
# Last seed basename may be recovered from the actual exact full semantic peer through its typed request.
if not seeds[-1].is_file():seeds.pop()
for p in seeds:register(str(p),H(p))
discover(po)
while queue:discover(J(queue.pop()))
B.mkdir(parents=True)
for n,h in list(refs.items()):
 p=resolve(n,h)
 if p.is_relative_to(R)and p.resolve().is_relative_to(R.resolve())and str(p)not in mutable:a=ref(p)
 else:
  t=B/'original-closed-bytes'/h/p.name
  if t.exists():assert H(t)==h
  else:put(t,p.read_bytes())
  a=ref(t)
 aliases[n]=a;aliases[str(P(n))]=a
 assert a['file']not in required or required[a['file']]==h
 required[a['file']]=h
# Existing historical aliases are retained by exact value except no external routes are allowed.
for n,a in aliases.items():assert not Path(a['file']).is_absolute()and P(a['file']).resolve().is_relative_to(R.resolve())and H(P(a['file']))==a['sha256'],n
def durable(v):
 if isinstance(v,dict):
  if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str)and re.fullmatch('[0-9a-f]{64}',v['sha256']):
   n=v['file'];a=aliases.get(n)or aliases.get(str(P(n)))
   assert a is not None,(n,v['sha256']);assert a['sha256']==v['sha256'];return {**v,'file':a['file']}
  return {k:durable(x)for k,x in v.items()}
 if isinstance(v,list):return[durable(x)for x in v]
 return v
out=copy.deepcopy(pending);binding_patches=[]
def setfield(parts,value):
 d=out
 for k in parts[:-1]:d=d[k]
 k=parts[-1];exists=k in d if isinstance(d,dict)else True;before=copy.deepcopy(d[k])if exists else None
 if exists and before==value:return
 binding_patches.append({'path':parts,'existed':exists,'before':before});d[k]=copy.deepcopy(value)
# Only newly added or newly replaced evidence fields are rebound; all old28 proof metadata/history remain exact.
def transform_changed(before,after,path):
 if isinstance(after,dict):
  for k,v in list(after.items()):
   if not isinstance(before,dict)or k not in before:setfield(path+[k],durable(v))
   elif before[k]!=v:transform_changed(before[k],v,path+[k])
 elif isinstance(after,list)and isinstance(before,list)and len(after)==len(before):
  for i,(a,b)in enumerate(zip(before,after)):
   if a!=b:transform_changed(a,b,path+[i])
transform_changed(old,out,[])
proofs={};by_source={r['canonical_source']:r for r in ready['sources']}
for n in po['proof_files']:
 row=by_source[n];meta=copy.deepcopy(out['proof_files'][n]);pairs=[p for p in ready['actual_paired_records']if p['source']['file']==n]
 assert [p['kind']for p in pairs]==['standalone','named']and len(pairs)==2
 source=R/n;assert H(source)==meta['sha256']==row['original_tmp_source']['sha256'];names=[d['name']for d in row['public_declarations']if d['kind']in ['theorem','lemma']]
 assert names==meta['declarations']==meta['mapped_named_declarations']and len(names)==row['public_theorem_count']
 for pair in pairs:
  assert pair['actual_exit_code']==0
  nr=J(P(pair['actual_record']['file']));assert H(P(pair['actual_record']['file']))==pair['actual_record']['sha256']and nr['exit_code']==0
  assert nr['source']==n and nr['source_sha256_before']==nr['source_sha256_after']==H(source)and nr['actual_workdir']==str(R/'verification/lean')
  expected=['lake','env','lean','SafeLearning/'+source.name]if pair['kind']=='standalone'else['lake','build','SafeLearning.'+source.stem]
  assert nr['command']==expected and H(P(pair['raw_log']['file']))==pair['raw_log']['sha256']==nr['log_sha256']and H(P(pair['source_snapshot']['file']))==H(source)
  for k in ['source','actual_record','raw_log','source_snapshot']:required[pair[k]['file']]=pair[k]['sha256']
 meta.update({'actual_pair':pairs,'canonical_pair_pending':False,'selection_scope':'direct_reviewed_reference_with_actual_canonical_standalone_and_named_pairs','standalone_compile_status':'passed_source_matched_actual_canonical_pair','evidence_sha256':pairs[0]['actual_record']['sha256'],'standalone_compile_evidence':pairs[0],'actual_canonical_readiness':ref(READY)})
 setfield(['proof_files',n],meta);proofs[n]=meta
for i,e in enumerate(out['exercises']):
 if 'entire_literal_closure29'in e:
  v=copy.deepcopy(e['entire_literal_closure29']);v['canonical_pair_and_owner_integration_pending']=False;v['actual_canonical_pairs_available_owner_integration_pending']=True;setfield(['exercises',i,'entire_literal_closure29'],v)
 for j,c in enumerate(e['claims']):
  if 'reviewed_owner29_transition'in c:setfield(['exercises',i,'claims',j,'reviewed_owner29_transition','canonical_pair_pending'],False)
for i,c in enumerate(out['material_claims']):
 if 'reviewed_owner29_transition'in c:setfield(['material_claims',i,'reviewed_owner29_transition','canonical_pair_pending'],False)
setfield(['reviewed_work_integration29_current65_candidate','status'],'reviewed_actual65_two_whole_exercises_eleven_units_with_actual_canonical_pairs_pending_independent_final_mapping_and_owner_integration')
setfield(['actual_current65_pair_binding29'],{'status':'actual_two_sources72_theorems91_public_names_four_zero_native_commands_bound_pending_independent_mapping','readiness':ref(READY),'original_actual_root_execution':ref(OUTER),'original_pending_candidate':aliases[str(PENDING)],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'old500_proof_metadata_and3412_declaration_prefix_exact':True,'original_semantic_peer_bodies_times_unmodified':True,'root_outer_baseline26_selection27_fields_retained_as_original_historical_fields_only':True,'actual_current65_context':aliases['/tmp/root_tmp_lean_current65_owner28_context_v1.json'],'owner_integrated':False,'coverage_complete':False})
assert all(out['proof_files'][n]==v for n,v in old['proof_files'].items())and out['declarations'][:len(old['declarations'])]==old['declarations']
rev=copy.deepcopy(out)
for patch in reversed(binding_patches):
 d=rev
 for k in patch['path'][:-1]:d=d[k]
 if patch['existed']:d[patch['path'][-1]]=patch['before']
 else:del d[patch['path'][-1]]
assert(json.dumps(rev,ensure_ascii=False,indent=2)+'\n').encode()==PENDING.read_bytes()
CAND=B/'modules29-current65-two-source-pair-bound-candidate-v1.json';putj(CAND,out);required[ref(CAND)['file']]=H(CAND)
INTER=B/'modules29-current65-pair-binding-exact-inverse-interface-v1.json';putj(INTER,{'status':'exact_forward_binding_and_full_byte_inverse_to_original_pending_candidate_verified','original_pending_candidate':aliases[str(PENDING)],'candidate':ref(CAND),'restore_patches_in_reverse_order':binding_patches,'old_candidate_inverse_interface':durable(po['exact_inverse_interface']),'original_closed_byte_aliases':aliases,'historical_exact_byte_resolutions':resolutions,'coverage_complete':False});required[ref(INTER)['file']]=H(INTER)
for p in [OLD_OFFER,READY,OUTER]:required[ref(p)['file']]=H(p)
offer={**durable(po),'status':'prepared_modules29_actual65_two_source_pair_bound_offer_pending_independent_final_mapping','candidate':ref(CAND),'candidate_builder':aliases[str(Path(__file__))],'proof_files':proofs,'base_selection':ref(R/'reports/full-coverage/checkpoint-28-selection.json'),'actual_canonical_pairs_pending':False,'actual_canonical_readiness':ref(READY),'actual_root_canonical_execution':ref(OUTER),'original_pending_candidate':aliases[str(PENDING)],'original_pending_offer':aliases[str(PO)],'original_reviewed_owner28_offer':ref(OLD_OFFER),'exact_pair_binding_inverse_interface':ref(INTER),'required_evidence_artifacts_sha256':required,'original_closed_byte_aliases':aliases,'actual_isolated_candidate_preparation':aliases['/tmp/modules29-current65-two-whole-candidate-preparation-actual-v1.json'],'final_mapping_peer':None,'actual_finalizer':None,'coverage_complete':False}
O=B/'modules29-current65-two-source-pair-bound-offer-draft-v1.json';putj(O,offer)
guard();print(json.dumps({'candidate':ref(CAND),'offer':ref(O),'inverse':ref(INTER),'required_ref_count':len(required),'exact_alias_count':len(aliases),'binding_patch_count':len(binding_patches),'counts':out['counts']}))
