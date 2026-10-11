from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1'
OLD=B/'modules28-current60-five-source-pair-bound-offer-draft-v2.json';NEW=B/'modules28-current60-five-source-pair-bound-offer-draft-v3.json'
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert h(OLD)=='12642bfed0d44d9f613b5bc0e0eaea0cfc16a7c4e6585832a5d4531f443d36b0' and not NEW.exists()
o=json.loads(OLD.read_bytes());d=copy.deepcopy(o);assert h(R/o['candidate']['file'])==o['candidate']['sha256']=='2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
n='verification/lean/SafeLearning/CompleteModulesSensorCommissioning28.lean';row=o['proof_files'][n]
assert len(row['actual_pair'])==2 and [p['kind'] for p in row['actual_pair']]==['standalone','named']
added={}
for p in row['actual_pair']:
 for k in ['actual_record','raw_log','source_snapshot']:
  r=p[k];assert h(R/r['file'])==r['sha256']
  if r['file'] in added:assert added[r['file']]==r['sha256']
  added[r['file']]=r['sha256']
assert len(added)==5 and all(n not in o['required_evidence_artifacts_sha256'] for n in added)
d['required_evidence_artifacts_sha256'].update(added)
back=copy.deepcopy(d)
for n in added:back['required_evidence_artifacts_sha256'].pop(n)
assert back==o and len(d['required_evidence_artifacts_sha256'])==922
for n,s in d['required_evidence_artifacts_sha256'].items():assert h(R/n)==s,n
with NEW.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'offer':{'file':str(NEW.relative_to(R)),'sha256':h(NEW)},'candidate':d['candidate'],'only_new_direct_evidence_entries':added,'evidence_count':922}))
