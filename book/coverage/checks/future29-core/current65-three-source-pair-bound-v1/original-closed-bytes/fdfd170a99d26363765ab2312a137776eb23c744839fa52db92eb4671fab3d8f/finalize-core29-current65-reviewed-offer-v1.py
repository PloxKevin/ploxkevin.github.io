from pathlib import Path
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future29-core/current65-three-source-pair-bound-v1';O=B/'core29-current65-three-source-pair-bound-offer-draft-v2.json';P=R/'book/coverage/checks/future28-foundations/core29-current65-final-mapping-independent-v2/core29-current65-three-source-actual-pair-bound-independent-foundations-final-mapping-peer-v1.json';C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def path(n):p=Path(n);return p if p.is_absolute() else R/p
assert sha(O)=='a1fcc9eabe3db2f6307f839cf19451659632e0fe72297023266bd737256fba50' and sha(P)=='686388553f83b6425e2268cb054cc540ac12461ba48775059d5fb3bf7b797d25';d=json.loads(O.read_bytes());peer=json.loads(P.read_bytes());ctx=json.loads(C.read_bytes());held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
assert peer['status']=='passed_independent_full_core29_current65_actual_pair_bound_final_mapping_foundations' and peer['errors']==[] and peer['candidate']==d['candidate'] and peer['offer']==ref(O)
assert peer['whole_exercise21_or_nodes750_752_1141_approved'] is False and peer['native_exit_code']==0
for n,h in held.items():assert sha(path(n))==h
for n,h in peer['required_evidence_artifacts_sha256'].items():
 assert not Path(n).is_absolute() and (R/n).resolve().is_relative_to(R) and sha(R/n)==h
 assert n not in d['required_evidence_artifacts_sha256'] or d['required_evidence_artifacts_sha256'][n]==h;d['required_evidence_artifacts_sha256'][n]=h
for n,q in peer['original_closed_byte_aliases'].items():
 assert sha(R/q['file'])==q['sha256'];assert n not in d['original_closed_byte_aliases'] or d['original_closed_byte_aliases'][n]['sha256']==q['sha256'];d['original_closed_byte_aliases'].setdefault(n,{'file':q['file'],'sha256':q['sha256']})
d['required_evidence_artifacts_sha256'][ref(P)['file']]=sha(P);d['required_evidence_artifacts_sha256'][ref(O)['file']]=sha(O);d['original_author_pair_bound_offer']=ref(O);d['final_independent_candidate_mapping_peer']=ref(P);d['final_independent_mapping_actual']=peer['actual_finalizer'];d['final_independent_mapping_actual_original_byte_aliases']=peer['actual_finalizer_original_byte_aliases'];d['final_independent_mapping_actual_log_fields']=peer['actual_finalizer_log_fields'];d['status']='reviewed_core29_current65_three_source_actual_pair_bound_candidate_offer';d['actual_finalizer']=peer['actual_finalizer']
SELF=Path(__file__);t=B/'original-closed-bytes'/sha(SELF)/SELF.name;t.parent.mkdir(parents=True,exist_ok=True)
with t.open('xb') as f:f.write(SELF.read_bytes())
d['required_evidence_artifacts_sha256'][ref(t)['file']]=sha(t);d['original_closed_byte_aliases'][str(SELF)]=ref(t)
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h
F=B/'core29-current65-three-source-reviewed-offer-v1.json'
with F.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
for n,h in held.items():assert sha(path(n))==h
print(json.dumps({'status':'passed_exact_core29_final_independent_peer_offer_binding','offer':ref(F),'candidate':d['candidate'],'peer':ref(P),'actual_finalizer':d['actual_finalizer'],'closure':len(d['required_evidence_artifacts_sha256']),'new_sources':3,'new_public':142,'new_theorems':93,'live_owner_written':False}))
