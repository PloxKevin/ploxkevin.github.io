from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased')
B='book/coverage/checks/future28-foundations/current60-owner28-v1'
D=B+'/foundations28-current60-offer-draft-v3.json'
P=B+'/independent-modules-final-mapping-v1/foundations21-current60-final-mapping-independent-modules28-closed-v1.json'
OUT=B+'/foundations28-current60-offer-draft-v4.json'
def safe(n):
 p=Path(n);assert type(n)is str and n and not p.is_absolute()and '..'not in p.parts and p.as_posix()==n
 p=R/p;assert p.resolve().is_relative_to(R)and not p.is_symlink();return p
def h(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def j(n):return json.loads(safe(n).read_bytes())
def ref(n):return {'file':n,'sha256':h(n)}
assert not safe(OUT).exists()
assert h(D)=='d2e2da5637cd39bbc033f09561144308e8c7b98adea87462a84eb096be69668f'
assert h(P)=='809eabeeb923f697657d68cd3eb2eb7e2c223c86e13930f43d68b56c532b25f5'
d=j(D);p=j(P)
assert p['status']=='passed_independent_foundations28_current60_final_candidate_mapping'and p['errors']==[]
assert p['candidate']==d['candidate']and p['offer']==ref(D)and p['exact_interface']==d['exact_interface']
assert p['new_whole_material_units']==21 and p['new_proof_sources']==6 and p['new_public_declarations']==99
a=j(p['actual_finalizer']['file'])
codes=[a[k]for k in ('actual_exit_code','exit_code','actual_runner_exit_code')if k in a]
assert codes and all(type(c)is int and c==0 for c in codes)
assert a['actual_command']==p['expected_actual_finalizer_command']and a['actual_workdir']==str(R)
assert a['helper_sha256_before']==a['helper_sha256_after']==p['expected_actual_finalizer_helpers_sha256']and a['protection_errors']==[]
out=copy.deepcopy(d);closed=out['required_evidence_artifacts_sha256']
mutable={'book/coverage/'+n+'.json'for n in ['core','foundations','applied','modules','applied-promotions']}
def add(n,s):
 assert n not in mutable and h(n)==s,n
 assert n not in closed or closed[n]==s;closed[n]=s
def walk(v):
 if isinstance(v,dict):
  if {'file','sha256'}<=set(v)and type(v['file'])is str and not Path(v['file']).is_absolute():add(v['file'],v['sha256'])
  for x in v.values():walk(x)
 elif isinstance(v,list):
  for x in v:walk(x)
add(D,h(D));add(P,h(P));walk(p)
cats=[B+'/normalization-original-closed-bytes/original-closed-byte-aliases-v1.json',p['original_closed_byte_catalog']['file']]
for n in cats:add(n,h(n));walk(j(n))
for n,s in closed.items():assert h(n)==s,n
pins=j('book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json')['protected_inputs_sha256']
def guard():
 for n,s in pins.items():assert h(n)==s,n
 assert h(D)=='d2e2da5637cd39bbc033f09561144308e8c7b98adea87462a84eb096be69668f'and h(P)=='809eabeeb923f697657d68cd3eb2eb7e2c223c86e13930f43d68b56c532b25f5'
guard()
out.update(status='foundations28_current60_exact_candidate_and_twenty_one_whole_material_mappings_independently_reviewed_ready_for_root_integration',finalized_at_utc=datetime.now(timezone.utc).isoformat(),reviewed_original_offer=ref(D),final_mapping_peer=ref(P),expected_final_mapping_peer_status=p['status'],actual_finalizer=p['actual_finalizer'],actual_finalizer_kind=p['actual_finalizer_kind'],actual_finalizer_original_byte_aliases=p['actual_finalizer_original_byte_aliases'],expected_actual_finalizer_command=p['expected_actual_finalizer_command'],expected_actual_finalizer_helpers_sha256=p['expected_actual_finalizer_helpers_sha256'],actual_finalizer_log_fields=p['actual_finalizer_log_fields'],independent_final_candidate_mapping_peer_pending=False,author_offer_finalization_actual_pending=True)
out['installer_schema_normalization']=dict(out['installer_schema_normalization'],actual_normalization_record_pending=False,actual_normalization_record=j(cats[0])['original_byte_aliases']['/tmp/foundations28-current60-offer-installer-normalization-actual-v1.json'])
assert out['candidate']==d['candidate']and out['proof_files']==d['proof_files']and out['material_claim_counts']==d['material_claim_counts']
with safe(OUT).open('x')as f:json.dump(out,f,indent=2);f.write('\n')
guard()
print(json.dumps({'offer':ref(OUT),'candidate':out['candidate'],'final_mapping_peer':out['final_mapping_peer'],'actual_finalizer':out['actual_finalizer'],'required_evidence_count':len(closed),'canonical_owner_source_selection_written':False}))
