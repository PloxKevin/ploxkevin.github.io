from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');DEST=ROOT/'book/coverage/checks/future31-foundations/current81-four-family-disjoint-inverse-v3'
TMP=Path('/tmp/foundations-source81-disjoint-inverse31-v3');NATIVE=Path('/tmp/foundations-source81-disjoint-inverse31-preparation-actual-v3.json')
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def alias(p):
 p=path(p);r=ref(p)
 if p.is_relative_to(ROOT):return r
 q=DEST/'exact-original-by-sha256'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 return ref(q)
assert not DEST.exists();n=json.loads(NATIVE.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]
o=json.loads((TMP/'foundations31-current81-real8-pair-bound-final-offer-v4-unclosed.json').read_bytes())
oldcandidate=o['candidate'];assert oldcandidate['sha256']=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
newinv=alias(o['exact_inverse']['file']);o['exact_inverse']=newinv
oldfinal=o['actual_finalizer'];o['original_actual_preparation2_native']=oldfinal
o['actual_finalizer']=alias(NATIVE)
artifacts=[NATIVE,path(n['log']),Path('/tmp/prepare-foundations-source81-disjoint-inverse31-v3.py'),Path('/tmp/run-prepare-foundations-source81-disjoint-inverse31-v3.py'),Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json'),TMP/'foundations31-current81-real8-pair-bound-final-offer-v4-unclosed.json',Path(__file__)]
observation=Path('/tmp/foundations31-inverse-overlap-actual-observation-v1.json')
if observation.exists():artifacts.append(observation)
newaliases={str(p):{'original':ref(p),'original_byte_copy':alias(p)} for p in artifacts}
o['actual_finalizer_original_byte_aliases']={str(p):alias(p) for p in artifacts[:5]}
o['original_actual_preparation2_native_and_all_original_aliases_retained']=True
o['inverse_repair3_original_byte_aliases']=newaliases
for x in newaliases.values():o['required_evidence_artifacts_sha256'][x['original_byte_copy']['file']]=x['original']['sha256']
o['required_evidence_artifacts_sha256'][newinv['file']]=newinv['sha256']
o['original_overlapping_inverse_protocol']=alias(o['original_overlapping_inverse_protocol']['file'])
o['inverse_protocol_repair']['candidate_bytes_unchanged']=oldcandidate
out=DEST/'foundations31-current81-real8-pair-bound-final-offer-v4.json';out.write_text(json.dumps(o,indent=2)+'\n')
print(json.dumps({'offer':ref(out),'candidate':oldcandidate,'exact_inverse':newinv,'actual_finalizer':o['actual_finalizer']}))
