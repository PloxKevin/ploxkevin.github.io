from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/applied29-current65-identity-v2');CTX=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert sha(CTX)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
ctx=read(CTX);assert ctx['status']=='actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'
held={}
for m in [ctx['pins_sha256'],ctx['held_current_source_sha256'],ctx['owners_sha256']]:
 for n,h in m.items():assert n not in held or held[n]==h;held[n]=h
OLD_OFFER=Path('/tmp/applied29-current64-identity-v1/applied29-current64-identity-offer-draft-v2.json');assert sha(OLD_OFFER)=='dd6eefd0638aee7a188721a348fb530028ea458a6872ca4eeab4c99a915ac38b'
old=read(OLD_OFFER);assert old['errors']==[] and old['proof_files']=={}
OLD_PEER=R/'book/coverage/checks/future29-applied/applied64-identity-independent-modules-v1/applied29-current64-identity-independent-modules29-closed-peer-v2.json';assert sha(OLD_PEER)=='9d6d456662042ca629c4589fc7865c0c1e5cf0f0befbbac44038de7157d09f2b'
peer=read(OLD_PEER);assert peer['errors']==[]
C64=path(old['candidate']['file']);P64=path(old['candidate_promotions']['file']);assert sha(C64)==old['candidate']['sha256'] and sha(P64)==old['candidate_promotions']['sha256']
c64,p64=read(C64),read(P64);assert 'current64_owner_identity' in c64 and 'current64_owner_identity' in p64
base,pbase=copy.deepcopy(c64),copy.deepcopy(p64);base.pop('current64_owner_identity');pbase.pop('current64_owner_identity')
assert json.dumps(base,indent=2,ensure_ascii=False)+'\n'==(R/'book/coverage/applied.json').read_text()
assert json.dumps(pbase,indent=2,ensure_ascii=False)+'\n'==(R/'book/coverage/applied-promotions.json').read_text()
I64=R/'book/coverage/inventory-after-correction64.json';I65=R/'book/coverage/inventory-after-correction65.json';assert sha(I64)=='11136add476e6b5be58f4bc6ea038602d51016a7e8370eeb67e17e9358893f98' and sha(I65)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'==sha(R/'book/coverage/inventory.json')
i64,i65=read(I64),read(I65);scope=set(c64['scope_pages']);assert len(scope)==3
assert c64['source_sha256']=={n:i64['source_sha256'][n] for n in scope}=={n:i65['source_sha256'][n] for n in scope}
for section,count in [('exercises',128),('material_source_units',2059)]:
 a={x['key']:x for x in i64[section] if x['source'] in scope};b={x['key']:x for x in i65[section] if x['source'] in scope};assert a==b and len(a)==count
assert len(c64['exercises'])==128 and sum(len(x['claims']) for x in c64['exercises'])==468 and len(c64['material_claims'])==1954 and len(c64['proof_files'])==312
APP=path(ctx['actual_source65_application']['file']);ACT=path(ctx['actual_source65_application_native']['file']);assert sha(APP)==ctx['actual_source65_application']['sha256'] and sha(ACT)==ctx['actual_source65_application_native']['sha256']
a,n=read(APP),read(ACT);assert a['status']=='passed_actual_source65_correction_full29_inventory_owner_identity_rebase_pending' and a['selected28_proof_sources_unchanged']==1186 and a['five_owner28_ledgers_unchanged'] is True
assert type(n['actual_exit_code']) is int and n['actual_exit_code']==0 and n['status']=='passed' and n['actual_workdir']==str(R)
assert n['helper_sha256_before']==n['helper_sha256_after'] and sha(path(n['log']))==n['log_sha256']
assert n['actual_command'][0:2]==['python3','book/coverage/checks/root_apply_source65_v1.py'] and n['actual_command'][-1]=='--apply'
for f,h in n['helper_sha256_after'].items():assert sha(path(f))==h
closure=dict(old['required_evidence_artifacts_sha256'])
for m in [peer.get('required_evidence_artifacts_sha256',{}),peer.get('closed_evidence_sha256',{})]:
 for f,h in m.items():assert f not in closure or closure[f]==h;closure[f]=h
aliases=copy.deepcopy(old['original_closed_byte_aliases'])
for original,q in peer.get('original_closed_byte_aliases',{}).items():
 assert set(q) in ({'file','sha256'},{'file','sha256','bytes'})
 if 'bytes' in q:assert type(q['bytes']) is int and q['bytes']==path(q['file']).stat().st_size
 native={'file':q['file'],'sha256':q['sha256']}
 assert original not in aliases or aliases[original]==native;aliases[original]=native
for f,h in closure.items():assert sha(path(f))==h,f
for f,q in aliases.items():assert set(q)=={'file','sha256'} and sha(path(q['file']))==q['sha256']
for f in ['/tmp/prepare-applied29-current65-identity-overlay-v1.py','/tmp/run-applied29-current65-identity-preparation-v1.py','/tmp/applied29-current65-identity-candidate-preparation-actual-v1.json','/tmp/applied29-current65-identity-candidate-preparation-actual-v1.log']:
 closure[f]=sha(f)
SELF=Path(__file__);selfsha=sha(SELF)
def guard():
 assert sha(SELF)==selfsha and sha(CTX)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
 for f,h in held.items():assert sha(path(f))==h,f
 for f,h in closure.items():assert sha(path(f))==h,f
guard();OUT.mkdir(exist_ok=False)
SIDE=OUT/'applied29-current65-entire-owned-literal-identity-v1.json'
put(SIDE,{'status':'passed_actual_applied_source64_to65_entire_owned_literal_identity','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'historical_inventory':ref(I64),'current_inventory':ref(I65),'actual_source65_application':ref(APP),'actual_application_execution':ref(ACT),'original_current64_candidate':ref(C64),'original_current64_promotions':ref(P64),'original_current64_offer':ref(OLD_OFFER),'original_entire_current64_independent_peer_body_and_time':ref(OLD_PEER),'entire_equal_owned_inventory_records':{'exercises':128,'material_source_units':2059},'unchanged_math_counts':{'exercise_claims':468,'material_claims':1954,'proof_metadata_rows':312},'changed_owned_literals':[],'new_proof_sources':0,'new_mathematical_decisions':0,'inverse_recipe':'Delete only current65_owner_identity to restore both entire approved current64 candidate bytes. Then the retained current64 recipe deletes current64_owner_identity to restore both entire installed28 original bytes.','original_author1_prewrite_schema_failure':{'actual':ref('/tmp/applied29-current65-identity-candidate-preparation-actual-v1.json'),'reason':'Author1 wrongly rejected optional truthful bytes in immutable peer alias records; NEW2 verifies exact byte count then projects only its new map to file/sha256, leaving original peer unchanged.'},'semantic_review_redecided':False,'coverage_complete':False})
overlay={'inventory':str(I65.relative_to(R)),'inventory_sha256':sha(I65),'identity_sidecar':ref(SIDE),'original_current64_candidate':ref(C64),'original_current64_promotions':ref(P64),'original_current64_offer':ref(OLD_OFFER),'original_entire_current64_independent_peer_body_and_time':ref(OLD_PEER),'actual_source65_application':ref(APP),'changed_owned_literals':[],'new_proof_sources':0,'new_mathematical_decisions':0,'scope':'Source65 identity only; every original current64 mathematical field, semantic review body, status and time is unchanged.'}
c65,p65=copy.deepcopy(c64),copy.deepcopy(p64);assert 'current65_owner_identity' not in c65 and 'current65_owner_identity' not in p65;c65['current65_owner_identity']=copy.deepcopy(overlay);p65['current65_owner_identity']=copy.deepcopy(overlay)
x,y=copy.deepcopy(c65),copy.deepcopy(p65);x.pop('current65_owner_identity');y.pop('current65_owner_identity');assert x==c64 and y==p64
assert json.dumps(x,indent=2,ensure_ascii=False)+'\n'==C64.read_text() and json.dumps(y,indent=2,ensure_ascii=False)+'\n'==P64.read_text()
CAND=OUT/'applied29-current65-identity-candidate-v1.json';PROM=OUT/'applied-promotions29-current65-identity-candidate-v1.json';put(CAND,c65);put(PROM,p65)
INT=OUT/'applied29-current65-identity-candidate-integrity-v1.json';put(INT,{'status':'passed_actual_isolated_applied29_current65_identity_candidate_mechanics','errors':[],'candidate':ref(CAND),'candidate_promotions':ref(PROM),'identity_sidecar':ref(SIDE),'exact_inverse_recovers_both_entire_current64_original_bytes':True,'inverse64_recovers_both_entire_installed28_original_bytes':True,'new_proof_sources':0,'new_mathematical_decisions':0,'coverage_complete':False,'live_owner_written':False})
for p in [OLD_OFFER,OLD_PEER,C64,P64,I64,I65,APP,ACT,path(n['log']),CTX,SELF,SIDE,INT]:
 q=ref(p);assert q['file'] not in closure or closure[q['file']]==q['sha256'];closure[q['file']]=q['sha256']
for f,h in n['helper_sha256_after'].items():assert f not in closure or closure[f]==h;closure[f]=h
offer={'schema_version':1,'status':'isolated_applied29_current65_identity_candidate_awaiting_independent_mechanics','errors':[],'inventory':str(I65.relative_to(R)),'inventory_sha256':sha(I65),'base_selection':ctx['selection'],'candidate':ref(CAND),'candidate_promotions':ref(PROM),'mapped_ledger':str(CAND),'mapped_ledger_sha256':sha(CAND),'mapped_promotions':str(PROM),'mapped_promotions_sha256':sha(PROM),'source_sha256':copy.deepcopy(c65['source_sha256']),'candidate_builder':ref(SELF),'identity_sidecar':ref(SIDE),'identity_integrity':ref(INT),'original_current64_offer':ref(OLD_OFFER),'original_entire_current64_independent_peer_body_and_time':ref(OLD_PEER),'original_complete_independent_peer':copy.deepcopy(old['original_complete_independent_peer']),'proof_files':{},'new_actual_paired_records':[],'new_material_keys':[],'new_exercises':[],'counts':copy.deepcopy(c65['counts']),'required_evidence_artifacts_sha256':closure,'original_closed_byte_aliases':aliases,'actual_isolated_candidate_preparation':None,'final_independent_candidate_mapping_peer':None,'coverage_complete':False,'scope':'TMP-only exact invertible Applied65 identity overlay; no new proof/material/exercise decision or live write.'}
OFFER=OUT/'applied29-current65-identity-offer-draft-v1.json';put(OFFER,offer);guard();print(json.dumps({'candidate':ref(CAND),'candidate_promotions':ref(PROM),'offer':ref(OFFER),'identity_sidecar':ref(SIDE),'evidence_count':len(closure),'alias_count':len(aliases),'new_proofs':0,'new_decisions':0}))
