from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');D=Path('/tmp/applied27-source55-identity-v1');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();real=lambda p:Path(p)if Path(p).is_absolute()else R/p
P=Path('/tmp/applied27-current55-identity-independent-modules-confirmation-v3.json');assert H(P)=='acf2bd0c04e30124109507023d7db14e0a0bfd54ce961fc61306296035f2e5f6';peer=json.loads(P.read_text());assert peer['errors']==[] and peer['status']=='passed_independent_exact_current55_identity_only_candidate_mechanics'
B=D/'applied-audit27-source55-identity-additions-draft-v1.json';assert H(B)=='10623286d794816ad3a78cc4a83c16cbc62cefc2ac62e440549a2ede99daf0d2';draft=json.loads(B.read_text());assert peer['entire_original_reviewed_draft_offer_body_and_time']==draft
for f,h in [(draft['candidate']['file'],draft['candidate']['sha256']),(draft['candidate_promotions']['file'],draft['candidate_promotions']['sha256'])]:assert H(f)==h
A=Path('/tmp/applied27-source55-identity-candidate-actual-v1.json');actual=json.loads(A.read_text());assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0;assert H(actual['raw_log'])==actual['raw_log_sha256']
closed={}
def union(m):
 for f,h in m.items():
  assert f not in closed or closed[f]==h,('digest conflict',f);assert H(real(f))==h,('byte drift',f);closed[f]=h
union(draft['entire_original_source53_final_offer_body_and_time']['required_evidence_artifacts_sha256']);union(draft['required_evidence_artifacts_sha256']);union(peer['closed_evidence_sha256'])
for p in [P,B,A,Path(actual['raw_log']),Path('/tmp/finalize-applied27-current55-identity-reviewed-offer-v1.py'),Path('/tmp/run-applied27-current55-reviewed-offer-finalization-v1.py')]:closed[str(p)]=H(p)
# Original bodies stay byte-exact; the canonical helper/offer move is a separate Root step.
aliases={};archive=D/'original-independent-current55-identity-peer';assert not archive.exists();archive.mkdir()
own=[str(P)]+[f for f in peer['closed_evidence_sha256']if f.startswith('/tmp/')and any(t in f for t in ['independent-modules','independent-modules-actual'])]
for i,f in enumerate(dict.fromkeys(own)):
 src=Path(f);dest=archive/(str(i).zfill(2)+'-'+src.name);dest.write_bytes(src.read_bytes());assert H(dest)==H(src);aliases[f]={'file':str(dest),'sha256':H(dest)};closed[str(dest)]=H(dest)
out=copy.deepcopy(draft);out['status']='independently_reviewed_isolated_applied27_current55_identity_only_offer';out['final_independent_candidate_mapping_peer']={'file':str(P),'sha256':H(P)};out['actual_isolated_candidate_preparation']={'file':str(A),'sha256':H(A)};out['required_evidence_artifacts_sha256']=closed;out['original_closed_byte_aliases']=aliases
out['preserved_original_draft_offer']={'file':str(B),'sha256':H(B)};out['entire_original_draft_offer_body_and_time']=draft;out['entire_original_independent_identity_peer_body_and_time']=peer
out['reviewed_offer_finalization']={'finalized_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/applied_next','helper':{'file':'/tmp/finalize-applied27-current55-identity-reviewed-offer-v1.py','sha256':H('/tmp/finalize-applied27-current55-identity-reviewed-offer-v1.py')},'scope':'TMP-only evidence closure and exact original identity offer preservation. Own then-open measured finalizer JSON/log are excluded until closed; no live owner, source, canonical proof, selection, PUB or Git change.'}
# Explicit inverse of the finalizer changes recovers the complete immutable draft.
inv=copy.deepcopy(out)
for k in ['original_closed_byte_aliases','preserved_original_draft_offer','entire_original_draft_offer_body_and_time','entire_original_independent_identity_peer_body_and_time','reviewed_offer_finalization']:inv.pop(k)
for k in ['status','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','required_evidence_artifacts_sha256']:inv[k]=draft[k]
assert inv==draft
O=D/'applied-audit27-source55-identity-additions-v1-reviewed.json';assert not O.exists();O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'offer':str(O),'sha256':H(O),'closed_evidence_count':len(closed),'original_peer_and_fail_history_aliases':len(aliases),'new_proof_sources':0,'new_decisions':0,'exact_inverse_to_original_draft':True}))
