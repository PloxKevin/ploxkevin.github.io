from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,importlib.util
R=Path('/home/oxrexkevin/SafetyBased');OUT=R/'book/coverage/checks/future29-core/current65-three-source-pair-bound-v1';C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');P=Path('/tmp/core29-current65-approved-candidate-v2/core29-current65-three-source-pending-pair-offer-v2.json')
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def checked(q):assert set(q) >= {'file','sha256'};p=path(q['file']);assert sha(p)==q['sha256'];return read(p)
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert sha(P)=='9347e56972b8e08578164756f280ac3156ccd4c67b13501fe05b684896eeca40';oldoffer=read(P)
assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';ctx=read(C);held={}
for m in [ctx['pins_sha256'],ctx['held_current_source_sha256'],ctx['owners_sha256']]:
 for f,h in m.items():assert f not in held or held[f]==h;held[f]=h
SELF=Path(__file__);selfsha=sha(SELF)
def guard():
 assert sha(SELF)==selfsha
 for f,h in held.items():assert sha(path(f))==h,f
 for n,h in evidence.items():assert sha(R/n)==h,n
pending=checked(oldoffer['candidate']);history=checked(oldoffer['original_changed_rows_and_inverse']);baseline=checked(history['original_entire_owner']);assert sha(R/'book/coverage/core.json')==history['original_entire_owner']['sha256']
reports=[]
for n,h in [('book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json','69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917'),('book/coverage/checks/future29-core/current65-monitoring29-canonical-pair-v1/actual-reviewed29-canonical-paired-readiness-v1.json','7c337991bad862e7a12ab28d2ef8e365a3aeebbec91026928ac5380bb6c02090')]:
 d=checked({'file':n,'sha256':h});assert d['status']=='passed_actual_reviewed29_canonical_standalone_and_named_pairs_unselected' and d['errors']==[]
 assert d['actual_compiler_command_count']==len(d['actual_paired_records'])==2*d['source_count'];reports.append((n,h,d))
sourcepairs={n:[] for n in oldoffer['planned_proof_files']};originals=dict(oldoffer['required_evidence_artifacts_sha256']);pool={}
def merge(f,h):assert f not in originals or originals[f]==h;originals[f]=h
def pool_alias(f,q):
 assert {'file','sha256'} <= set(q) <= {'file','sha256','bytes'};p=path(q['file']);assert sha(p)==q['sha256']
 if 'bytes' in q:assert type(q['bytes']) is int and q['bytes']==p.stat().st_size
 pool.setdefault((f,q['sha256']),[]).append(p)
for f,q in oldoffer['original_closed_byte_aliases'].items():pool_alias(f,q)
for n,h,d in reports:
 merge(n,h)
 for f,q in d['original_closed_byte_aliases'].items():pool_alias(f,q);merge(q['file'],q['sha256'])
 for pair in d['actual_paired_records']:
  n=pair['source']['file']
  if n not in sourcepairs:continue
  assert pair['source']['sha256']==oldoffer['planned_proof_files'][n]['sha256'] and type(pair['actual_exit_code']) is int and pair['actual_exit_code']==0
  sourcepairs[n].append(copy.deepcopy(pair))
  for k in ['source','actual_record','raw_log','source_snapshot']:q=pair[k];checked(q) if k=='actual_record' else None;assert sha(path(q['file']))==q['sha256'];merge(q['file'],q['sha256'])
  rec=checked(pair['actual_record']);assert rec['status']=='passed' and type(rec['exit_code']) is int and rec['exit_code']==0 and rec['source_unchanged'] is True
  assert rec['source']==n and rec['source_sha256_before']==rec['source_sha256_after']==pair['source']['sha256'] and rec['actual_workdir']==str(R/'verification/lean')
  expected=['lake','env','lean',str(Path(n).relative_to('verification/lean'))] if pair['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
  assert rec['command']==expected and rec['log']==pair['raw_log']['file'] and rec['log_sha256']==pair['raw_log']['sha256']
assert len(sourcepairs)==3 and all(len(ps)==2 and {p['kind'] for p in ps}=={'standalone','named'} for ps in sourcepairs.values())
# All exact provenance is collected before copying. Mutable owner names are
# archived by byte value rather than entering the immutable installation map.
for q in [oldoffer['candidate'],oldoffer['identity'],oldoffer['original_changed_rows_and_inverse'],history['original_entire_owner'],ref(P),ref(SELF)]:merge(q['file'],q['sha256'])
for f,q in oldoffer['original_closed_byte_aliases'].items():merge(q['file'],q['sha256'])
mutables=set(ctx['owners_sha256'])|{'book/coverage/inventory.json','book/coverage/material-corrections.json'}
existing_base=R/'book/coverage/checks/future28-core/current60-identity-v1/original-closed-bytes/5260f60e35a921106021e6c9d88197f4a96494fdd24c3b39ae143a06ea594036/core28-current60-identity-candidate-v1.json'
assert sha(existing_base)==history['original_entire_owner']['sha256']
for f in [history['original_entire_owner']['file'],'book/coverage/core.json']:pool.setdefault((f,sha(existing_base)),[]).append(existing_base)
evidence={};aliases={};targets={}
for f,h in originals.items():
 p=path(f);assert sha(p)==h,f
 possible=[p]+pool.get((f,h),[])
 valid=[q for q in possible if q.is_file() and q.resolve().is_relative_to(R) and not q.is_symlink() and str(q.relative_to(R)) not in mutables and sha(q)==h]
 if valid:target=valid[0]
 else:target=OUT/'original-closed-bytes'/h/p.name
 targets[(f,h)]=(p,target)
 for q in pool.get((f,h),[]):assert sha(q)==h
# Fresh destination makes copying and report creation collision-free.
guard();assert not OUT.exists();OUT.mkdir(parents=True)
for (f,h),(p,target) in targets.items():
 if not target.exists():
  target.parent.mkdir(parents=True,exist_ok=True)
  with target.open('xb') as out:out.write(p.read_bytes())
 assert sha(target)==h;rr=ref(target);assert rr['file'] not in evidence or evidence[rr['file']]==h;evidence[rr['file']]=h
 if rr['file']!=f:aliases[f]=rr
for f,q in oldoffer['original_closed_byte_aliases'].items():
 h=q['sha256'];target=targets[(q['file'],h)][1];rr=ref(target)
 assert f not in aliases or aliases[f]['sha256']==h;aliases.setdefault(f,rr)
for _,_,d in reports:
 for f,q in d['original_closed_byte_aliases'].items():
  target=targets[(q['file'],q['sha256'])][1];rr=ref(target);assert f not in aliases or aliases[f]['sha256']==rr['sha256'];aliases.setdefault(f,rr)
def resolved(q):
 rr=ref(targets[(q['file'],q['sha256'])][1]);assert evidence[rr['file']]==rr['sha256'];return rr
candidate=copy.deepcopy(pending)
history_ref=resolved(oldoffer['original_changed_rows_and_inverse']);identity_ref=resolved(oldoffer['identity']);base_ref=resolved(history['original_entire_owner'])
for e in candidate['exercises']:
 for x in e['claims']:
  if x.get('original_pending_row_archive')==oldoffer['original_changed_rows_and_inverse']:x['original_pending_row_archive']=history_ref
for x in candidate['material_claims']:
 if x.get('original_pending_row_archive')==oldoffer['original_changed_rows_and_inverse']:x['original_pending_row_archive']=history_ref
candidate['future29_current65_candidate_binding'].update(identity=identity_ref,original_changed_rows_and_exact_inverse=history_ref,original_entire_owner=base_ref,canonical_pair_binding_status='actual_three_standalone_named_pairs_all_zero',actual_canonical_readiness_reports=[{'file':n,'sha256':h} for n,h,_ in reports])
proofs={}
for n,x in oldoffer['planned_proof_files'].items():
 public=x['declarations'];th=[d['name'] for d in public if d['kind'] in ['theorem','lemma']];assert sha(R/n)==x['sha256']
 proof={'sha256':x['sha256'],'theorem_count':len(th),'public_theorem_names':th,'mapped_named_declarations':th,'public_declarations':public,'public_declaration_count':len(public),'actual_pair':sourcepairs[n],'evidence_sha256':{q[k]['file']:q[k]['sha256'] for q in sourcepairs[n] for k in ['actual_record','raw_log','source_snapshot']},'original_tmp_source':resolved(x['original_tmp_source']),'original_tmp_source_pointer_body_unchanged':copy.deepcopy(x['original_tmp_source']),'canonical_pair_binding_status':'actual_standalone_and_named_zero_aggregate_pending'}
 for f,h in proof['evidence_sha256'].items():assert evidence[f]==h
 proofs[n]=proof
assert sum(p['theorem_count'] for p in proofs.values())==93 and sum(p['public_declaration_count'] for p in proofs.values())==142
reverse=copy.deepcopy(candidate);oldes=history['original_exercises'];oldms=history['original_material_rows'];reverse['exercises']=[copy.deepcopy(oldes.get(e['inventory_key'],e)) for e in reverse['exercises']];reverse['material_claims']=[copy.deepcopy(oldms.get(c['id'],c)) for c in reverse['material_claims'] if c['id'] not in history['appended_material_claim_ids']]
for f in proofs:reverse['proof_files'].pop(f)
for k,v in history['original_top_level'].items():reverse[k]=copy.deepcopy(v)
reverse.pop('future29_current65_candidate_binding');assert reverse==baseline and json.dumps(reverse,indent=2,ensure_ascii=False)+'\n'==path(history['original_entire_owner']['file']).read_text()
CAND=OUT/'core29-current65-three-source-pair-bound-candidate-v1.json';put(CAND,candidate);evidence[ref(CAND)['file']]=sha(CAND)
INTEGRITY=OUT/'core29-current65-three-source-pair-bound-integrity-v1.json';put(INTEGRITY,{'status':'passed_actual_canonical_three_source_binding_and_exact_old_owner_inverse','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(CAND),'original_entire_owner':base_ref,'original_pending_pair_candidate':resolved(oldoffer['candidate']),'original_changed_rows_and_inverse':history_ref,'actual_readiness_reports':[{'file':n,'sha256':h} for n,h,_ in reports],'actual_canonical_command_count':6,'new_public_declaration_count':142,'new_theorem_lemma_count':93,'entire_old_proved_rows_and_original_review_times_preserved':True,'exercise_statuses':candidate['counts']['exercise_statuses'],'whole_exercise21_or_node1141_approved':False,'aggregate_audit_or_live_owner_installation_claimed':False});evidence[ref(INTEGRITY)['file']]=sha(INTEGRITY)
CAT=OUT/'original-closed-byte-aliases-v1.json';put(CAT,{'status':'exact_original_closed_bytes_normalized_to_physical_root_paths','original_closed_byte_aliases':aliases,'closed_evidence_sha256':evidence});evidence[ref(CAT)['file']]=sha(CAT)
OFFER=OUT/'core29-current65-three-source-pair-bound-offer-draft-v1.json';put(OFFER,{'status':'core29_current65_three_source_actual_pair_bound_offer_requires_independent_final_mapping','errors':[],'candidate':ref(CAND),'identity':identity_ref,'original_changed_rows_and_inverse':history_ref,'original_entire_owner':base_ref,'original_pending_pair_offer':resolved(ref(P)),'original_pending_pair_candidate':resolved(oldoffer['candidate']),'integrity':ref(INTEGRITY),'inventory_sha256':oldoffer['inventory_sha256'],'source_sha256':candidate['source_sha256'],'proof_files':proofs,'new_public_declaration_count':142,'new_theorem_lemma_count':93,'actual_canonical_compiler_command_count':6,'canonical_pair_ready':True,'source_correspondence_peers':oldoffer['source_correspondence_peers'],'whole_exercises':oldoffer['whole_exercises'],'whole_mathematical_units':oldoffer['whole_mathematical_units'],'editorial_not_formal_count':13,'dual_component_count':4,'fixed_selector_component_count':1,'whole_exercise21_or_generic_stochastic_CMDP_approved':False,'counts':candidate['counts'],'original_semantic_bodies_review_times_and_proved_rows_preserved':True,'required_evidence_artifacts_sha256':evidence,'original_closed_byte_aliases':aliases,'original_closed_byte_aliases_catalog':ref(CAT),'actual_finalizer':None,'final_independent_candidate_mapping_peer':None,'coverage_complete':False,'live_owner_written':False})
guard();print(json.dumps({'status':'passed_core29_three_source_actual_pair_binding','candidate':ref(CAND),'offer':ref(OFFER),'integrity':ref(INTEGRITY),'counts':candidate['counts'],'evidence_count':len(evidence),'aliases_count':len(aliases)}))
