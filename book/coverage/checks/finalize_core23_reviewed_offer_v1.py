"""Append completed final mapping evidence without rewriting the original offer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[3];B=R/'book/coverage/checks/future23-core';A=B/'original-tmp'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ref=lambda p:{'file':str(p.relative_to(R)),'sha256':sha(p)}
files=[Path('/tmp/core23-source51-final-candidate-independent-applied-confirmation-v1.json'),Path('/tmp/core23-source51-final-candidate-independent-applied-actual-v1.json'),Path('/tmp/core23-source51-final-candidate-independent-applied-actual-v1.log')]
peer=json.loads(files[0].read_text());actual=json.loads(files[1].read_text());checker=peer['actual_checker']['file'];files.append(Path(checker))
assert 'passed' in peer['status'] and peer.get('errors',[])==[] and actual.get('actual_exit_code',actual.get('exit_code'))==0
ali={}
for p in files:
 t=A/p.name
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 ali[str(p)]=ref(t)
old=B/'core-audit23-candidate-source51-additions-v1.json';d=json.loads(old.read_text());out=copy.deepcopy(d)
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h,n
out['status']='independently_reviewed_isolated_core23_source51_candidate_ready_for_root_guarded_integration'
out['original_isolated_offer']=ref(old);out['final_independent_candidate_mapping_peer']=ref(A/files[0].name)
out['final_peer_original_path_aliases']=ali;out['finalized_at_utc']=datetime.now(timezone.utc).isoformat()
for v in ali.values():out['required_evidence_artifacts_sha256'][v['file']]=v['sha256']
for n in ['reports/full-coverage/core23-candidate-offer-preparation-execution-v1.json','reports/full-coverage/core23-candidate-offer-preparation-execution-v1.log','book/coverage/checks/prepare_core23_candidate_offer_v1.py']:
 p=R/n;out['required_evidence_artifacts_sha256'][n]=sha(p)
out['required_evidence_artifacts_sha256'][str(old.relative_to(R))]=sha(old)
p=B/'core-audit23-candidate-source51-additions-v2-reviewed.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','reviewed_offer':ref(p),'original_offer':ref(old),'original_peer':out['final_independent_candidate_mapping_peer']}))
