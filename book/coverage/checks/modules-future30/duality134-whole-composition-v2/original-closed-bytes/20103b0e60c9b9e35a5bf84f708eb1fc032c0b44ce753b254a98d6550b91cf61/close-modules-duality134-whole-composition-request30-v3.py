from pathlib import Path
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/duality134-whole-composition-v2'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
P=B/'modules-duality134-full-Exercise7_5-six-units-prospective-composition-review-request30-v2.json';assert sha(P)=='ea1115daac54cce9b2f76f4af3ef37f68b2866b4d18e386ec4601af2f5297053'
d=json.loads(P.read_bytes());aliases=dict(d['original_closed_byte_aliases'])
def copy(p):
 p=Path(p);h=sha(p);z=B/'original-closed-bytes'/h/p.name;z.parent.mkdir(parents=True,exist_ok=True)
 if not z.exists():
  with z.open('xb')as f:f.write(p.read_bytes())
 assert sha(z)==h;r={'file':str(z.relative_to(R)),'sha256':h,'bytes':z.stat().st_size};aliases[str(p)]=r;return r
N=Path('/tmp/modules-duality134-whole-composition-preparation-actual30-v2.json');n=json.loads(N.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]
for p,h in n['helper_sha256_before'].items():assert sha(p)==h==n['helper_sha256_after'][p];copy(p)
assert sha(n['raw_log'])==n['raw_log_sha256'];copy(n['raw_log']);copy('/tmp/run-modules-duality134-whole-composition-preparation30-v2.py')
F=Path('/tmp/modules-duality134-whole-composition-preparation-actual30-v1.json');f=json.loads(F.read_bytes());assert f['actual_exit_code']==1 and f['protection_errors']==[]
for p,h in f['helper_sha256_before'].items():assert sha(p)==h==f['helper_sha256_after'][p];copy(p)
assert sha(f['raw_log'])==f['raw_log_sha256'];copy('/tmp/run-modules-duality134-whole-composition-preparation30-v1.py')
d['genuine_first_author_preparation_failed_before_final_output']={'native':copy(F),'raw':copy(f['raw_log']),'reason':'The author assumed native instead of the original expected31 actual_native schema key. Original helper/raw/body/time retained; NEW2 adjusts only the exact retrieval field. No mathematical correction.'}
for p in [__file__,'/tmp/run-modules-duality134-whole-composition-durable-closure30-v3.py']:copy(p)
d['actual_author_preparation']=copy(N);d['original_composition_request_v2']=copy(P);d['actual_author_preparation_original_byte_aliases']={p:aliases[p]for p in [*n['helper_sha256_before'],n['raw_log']]};d['original_closed_byte_aliases']=aliases;d['required_evidence_artifacts_sha256'].update({r['file']:r['sha256']for r in aliases.values()})
assert all((R/p).resolve().is_relative_to(R.resolve())and sha(R/p)==h for p,h in d['required_evidence_artifacts_sha256'].items())
O=B/'modules-duality134-full-Exercise7_5-six-units-prospective-composition-review-request30-v3.json';assert not O.exists();O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':str(O.relative_to(R)),'sha256':sha(O),'bytes':O.stat().st_size,'refs':len(d['required_evidence_artifacts_sha256'])}))
