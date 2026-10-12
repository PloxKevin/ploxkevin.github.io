from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=ROOT/'book/coverage/checks/future30-applied/physical-gp34-independent-applied-v1';PEER=OUT/'modules-physical-gp34-full-independent-applied30-closed-peer-v1.json';DEST=OUT/'modules-physical-gp34-full-independent-applied30-closed-peer-v2.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(PEER)=='47990e9878772c2984ea84d7b683424440ab0fbd1948cc388b39137e80753f3d' and not DEST.exists()
N=Path('/tmp/applied-independent-physical-gp34-full-review30-actual-v1.json');assert sha(N)=='5b0b3ff730d33e31a54cbb1298cf5c921377b4be0294b016450c730e6e9bc145';a=json.loads(N.read_bytes());assert a['actual_exit_code']==0
aliases={}
for p in [N,N.with_suffix('.log'),Path(a['review_helper']['file']),Path(a['wrapper']['file']),Path(__file__)]:
 h=sha(p);q=OUT/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==h;aliases[str(p)]=ref(q)
r=json.loads(PEER.read_bytes());r['review_helper']=aliases[a['review_helper']['file']];r['actual_independent_reader']=aliases[str(N)];r['actual_reader_wrapper']=aliases[a['wrapper']['file']];r['actual_reader_raw_log']=aliases[a['raw_log']['file']];r['reader_original_byte_aliases']=aliases;r['original_closed_semantic_peer']=ref(PEER)
context=json.loads(Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json').read_bytes())
for n,h in {**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}.items():assert sha(ROOT/n)==h,n
DEST.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'record':str(DEST.relative_to(ROOT)),'sha256':sha(DEST),'actual_independent_reader_exit_code':a['actual_exit_code'],'actual_reader_elapsed_seconds':a['elapsed_seconds'],'errors':r['errors'],'protection_errors':r['protection_errors']}))
