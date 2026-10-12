from pathlib import Path
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/clock40-all-penalty-association-v2'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
P=B/'modules-clock40-actual-all-penalty-common-stationary-attainment-association-review-request30-v1.json';assert sha(P)=='b859163be4eb8c8c6663d912c29ed5ced2b324d4c0651cc100537e5c6af95b49'
d=json.loads(P.read_bytes());aliases=dict(d['original_closed_byte_aliases'])
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(q)==h
 z={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=z;return z
n=Path('/tmp/modules-clock40-all-penalty-association-request30-preparation-actual-v2.json');a=json.loads(n.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
for p,h in a['helper_sha256_before'].items():assert sha(p)==h==a['helper_sha256_after'][p];copy(p)
assert sha(a['raw_log'])==a['raw_log_sha256'];copy(a['raw_log']);copy('/tmp/run-modules-clock40-all-penalty-association-request30-preparation-v2.py');copy(__file__)
d['actual_author_preparation']=copy(n);d['original_association_request_v1']=copy(P)
d['actual_author_preparation_original_byte_aliases']={p:aliases[p]for p in [*a['helper_sha256_before'],a['raw_log']]}
d['original_closed_byte_aliases']=aliases;d['required_evidence_artifacts_sha256'].update({r['file']:r['sha256']for r in aliases.values()})
assert all(sha(R/p)==h for p,h in d['required_evidence_artifacts_sha256'].items())
O=B/'modules-clock40-actual-all-penalty-common-stationary-attainment-association-review-request30-v2.json';assert not O.exists();O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases)}))
