from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1'
OLD=B/'modules28-current60-five-source-pair-bound-offer-draft-v3.json';NEW=B/'modules28-current60-five-source-pair-bound-offer-draft-v4.json'
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert h(OLD)=='9c615030cb2fbeea8430638b3353e03a27ecfbb240475731d4147cf261596286' and not NEW.exists()
o=json.loads(OLD.read_bytes());d=copy.deepcopy(o)
assert h(R/o['candidate']['file'])==o['candidate']['sha256']=='2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
originals={n:s for n,s in o['required_evidence_artifacts_sha256'].items() if n.startswith('verification/lean/.lake/packages/mathlib/')}
assert len(originals)==11
copies={}
for n,s in originals.items():
 p=R/n;assert h(p)==s and not p.resolve().is_relative_to(R)
 q=B/'canonical-primary-closed-bytes'/s/p.name
 assert q.resolve().is_relative_to(R) and not q.exists()
 copies[n]=(q,p.read_bytes(),{'file':str(q.relative_to(R)),'sha256':s})
for n,(q,b,a) in copies.items():
 q.parent.mkdir(parents=True,exist_ok=True)
 with q.open('xb') as f:f.write(b)
 assert q.read_bytes()==(R/n).read_bytes() and h(q)==a['sha256']
 d['required_evidence_artifacts_sha256'].pop(n);d['required_evidence_artifacts_sha256'][a['file']]=a['sha256']
 assert n not in d['original_closed_byte_aliases'];d['original_closed_byte_aliases'][n]=a
back=copy.deepcopy(d)
for n,(_,_,a) in copies.items():
 back['required_evidence_artifacts_sha256'].pop(a['file']);back['required_evidence_artifacts_sha256'][n]=a['sha256'];back['original_closed_byte_aliases'].pop(n)
assert back==o and len(d['required_evidence_artifacts_sha256'])==922
for n,s in d['required_evidence_artifacts_sha256'].items():
 p=R/n;assert p.resolve().is_relative_to(R) and h(p)==s,n
with NEW.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'offer':{'file':str(NEW.relative_to(R)),'sha256':h(NEW)},'candidate':d['candidate'],'original_primary_to_root_aliases':{n:a for n,(_,_,a) in copies.items()},'evidence_count':922}))
