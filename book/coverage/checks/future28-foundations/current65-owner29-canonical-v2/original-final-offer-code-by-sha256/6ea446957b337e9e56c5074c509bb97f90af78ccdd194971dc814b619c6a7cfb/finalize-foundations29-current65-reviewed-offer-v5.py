from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/current65-owner29-canonical-v2'
OLD=D/'foundations29-current65-canonical-offer-draft-v4.json';PEER=R/'book/coverage/checks/future29-foundations/current65-final-mapping-independent-modules-v3/foundations29-current65-final-mapping-independent-modules29-closed-peer-v2.json';NEW=D/'foundations29-current65-reviewed-final-offer-v5.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':sha(p)}
assert sha(OLD)=='9495f7e1378e2e0aeffe09972ce990cae857b626514ac0344931deba5c51efae' and sha(PEER)=='cf3953dfcf71c3ae57bcebe98e777eb35afd9db047f706a2bbe3b47eda087c10'
o=json.loads(OLD.read_bytes());peer=json.loads(PEER.read_bytes());assert peer['errors']==[] and peer['candidate']==o['candidate'] and peer['offer']==ref(OLD)
assert peer['source_count']==6 and peer['theorem_or_lemma_count']==53 and peer['actual_native_command_count']==12
ctx=json.loads(Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json').read_bytes());es=copy.deepcopy(o['required_evidence_artifacts_sha256'])
def add(q):assert not Path(q['file']).is_absolute() and sha(R/q['file'])==q['sha256'];assert q['file'] not in es or es[q['file']]==q['sha256'];es[q['file']]=q['sha256']
for n,h in peer['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for q in [ref(OLD),ref(PEER),peer['actual_finalizer'],peer['reader_original_catalog'],peer['original_full_independent_peer_body_and_observed_time']]:add(q)
CL=D/'foundations29-current65-physical-evidence-normalization-closure-v4.json';cl=json.loads(CL.read_bytes());add(ref(CL))
for q in cl['original_normalization_execution_aliases'].values():add(q)
for q in peer['actual_finalizer_original_byte_aliases'].values():add(q)
SELF=Path(__file__);h=sha(SELF);S=D/'original-final-offer-code-by-sha256'/h/SELF.name
def guard():
 for k in ('pins_sha256','held_current_source_sha256','owners_sha256'):
  for n,h in ctx[k].items():assert sha(R/n)==h,n
 for n,h in es.items():p=R/n;assert p.resolve().is_relative_to(R) and not p.is_symlink() and sha(p)==h,n
 assert sha(OLD)=='9495f7e1378e2e0aeffe09972ce990cae857b626514ac0344931deba5c51efae' and sha(PEER)=='cf3953dfcf71c3ae57bcebe98e777eb35afd9db047f706a2bbe3b47eda087c10'
guard();assert not NEW.exists() and not S.exists();S.parent.mkdir(parents=True,exist_ok=True);S.write_bytes(SELF.read_bytes());add(ref(S))
out=copy.deepcopy(o);out.update(status='reviewed_current65_foundations29_six_source_eight_math_eight_reference_final_offer_ready_for_root_isolated_preflight',independent_final_candidate_mapping_peer_pending=False,final_mapping_peer=ref(PEER),original_independently_reviewed_offer=ref(OLD),actual_finalizer=peer['actual_finalizer'],actual_finalizer_scope='Genuine independent Module reader3 native zero; original author preparation remains separate and unchanged.',actual_finalizer_original_byte_aliases=peer['actual_finalizer_original_byte_aliases'],actual_finalizer_log_fields=peer['actual_finalizer_log_fields'],independent_final_candidate_mapping_peer=ref(PEER),required_evidence_artifacts_sha256=es,additional_frozen_inputs=copy.deepcopy(es),physical_evidence_normalization_closure=ref(CL))
assert out['candidate']==o['candidate'] and out['exact_interface']==o['exact_interface'] and out['proof_files']==o['proof_files']
guard();NEW.write_text(json.dumps(out,indent=2)+'\n');guard()
print(json.dumps({'status':out['status'],'final_offer':ref(NEW),'candidate':out['candidate'],'exact_interface':out['exact_interface'],'final_mapping_peer':ref(PEER),'actual_finalizer':peer['actual_finalizer'],'closed_evidence_count':len(es),'counts':out['material_claim_counts'],'coverage_complete':False}))
