from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1';OLD=B/'modules28-current60-five-source-pair-bound-offer-draft-v4.json';NEW=B/'modules28-current60-five-source-pair-bound-offer-draft-v5.json'
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert h(OLD)=='e48af9781070acd309855ac016895722f10bb4723e1b7a6e0e5cea48dce13e49' and not NEW.exists()
o=json.loads(OLD.read_bytes());d=copy.deepcopy(o);rels=[n for n in o['original_closed_byte_aliases'] if n.startswith('verification/lean/.lake/packages/mathlib/')];assert len(rels)==11
prior={}
for n in rels:
 absolute=str(R/n);a=o['original_closed_byte_aliases'][n];old=o['original_closed_byte_aliases'][absolute]
 assert old['file']==n and old['sha256']==a['sha256'] and h(R/a['file'])==a['sha256']
 prior[absolute]=old;d['original_closed_byte_aliases'][absolute]=copy.deepcopy(a)
back=copy.deepcopy(d)
for n,a in prior.items():back['original_closed_byte_aliases'][n]=a
assert back==o and d['candidate']==o['candidate'] and len(d['required_evidence_artifacts_sha256'])==922
for n,s in d['required_evidence_artifacts_sha256'].items():assert (R/n).resolve().is_relative_to(R) and h(R/n)==s,n
for a in d['original_closed_byte_aliases'].values():assert (R/a['file']).resolve().is_relative_to(R) and h(R/a['file'])==a['sha256'],a
assert h(R/d['candidate']['file'])==d['candidate']['sha256']=='2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
with NEW.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'offer':{'file':str(NEW.relative_to(R)),'sha256':h(NEW)},'candidate':d['candidate'],'absolute_original_alias_values_corrected':11,'evidence_count':922}))
