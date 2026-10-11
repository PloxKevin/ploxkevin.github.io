"""Close the six original Core26 candidate peer bytes without rewriting records."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
PEER=Path('/tmp/core26-composed-candidate-independent-foundations-confirmation-v1.json')
SHA='96e2bdebf1195b21b948e84f886b4e1708fb14ec9826ed249c37165015f8253f'
BASE=ROOT/'book/coverage/checks/future26-core/composed-source53-v3/original-independent-candidate-peer'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(PEER)==SHA
d=json.loads(PEER.read_text());assert 'passed' in d['status'] and d['errors']==[]
originals=dict(d['closed_evidence_sha256']);originals[str(PEER)]=SHA
assert len(originals)==6
for n,h in originals.items():assert Path(n).is_absolute() and Path(n).is_file() and sha(Path(n))==h
assert not BASE.exists();BASE.mkdir()
aliases={}
for n,h in sorted(originals.items()):
    p=Path(n);target=BASE/p.name
    with target.open('xb') as f:f.write(p.read_bytes())
    assert sha(target)==h;aliases[n]={'file':str(target.relative_to(ROOT)),'sha256':h}
out=BASE/'closed-original-byte-aliases-v1.json'
with out.open('x') as f:f.write(json.dumps({'status':'passed_exact_original_candidate_peer_byte_closure','closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_peer':{'file':str(PEER),'sha256':SHA},'entire_original_peer_body_and_time':d,'aliases':aliases,'scope':'Exact copies only; no new mathematical decision or compiler execution.'},indent=2)+'\n')
print(json.dumps({'status':'passed','peer':aliases[str(PEER)],'catalogue':{'file':str(out.relative_to(ROOT)),'sha256':sha(out)}}))
