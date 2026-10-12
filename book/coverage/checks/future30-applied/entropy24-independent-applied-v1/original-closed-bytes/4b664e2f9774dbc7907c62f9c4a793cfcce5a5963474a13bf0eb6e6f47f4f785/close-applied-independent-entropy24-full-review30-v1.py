from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=ROOT/'book/coverage/checks/future30-applied/entropy24-independent-applied-v1';PEER=OUT/'modules-entropy24-full-independent-applied30-closed-peer-v1.json';DEST=OUT/'modules-entropy24-full-independent-applied30-closed-peer-v2.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(PEER)=='dd2565dbc6e1fd77a6b3b65b1c06ac970ad572fd607b380cae1272449ec810c2' and not DEST.exists()
N=Path('/tmp/applied-independent-entropy24-full-review30-actual-v1.json');assert sha(N)=='720ac70583e4896f9d6d9fe26d8da5d312f5ce5ebe3cd843dee28ad472811b88';a=json.loads(N.read_bytes());assert a['actual_exit_code']==0
aliases={}
for p in [N,N.with_suffix('.log'),Path(a['review_helper']['file']),Path(a['wrapper']['file']),Path(__file__)]:
 h=sha(p);q=OUT/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==h;aliases[str(p)]=ref(q)
r=json.loads(PEER.read_bytes());r['review_helper']=aliases[a['review_helper']['file']];r['actual_independent_reader']=aliases[str(N)];r['actual_reader_wrapper']=aliases[a['wrapper']['file']];r['actual_reader_raw_log']=aliases[a['raw_log']['file']];r['reader_original_byte_aliases']=aliases;r['original_closed_semantic_peer']=ref(PEER)
context=json.loads(Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json').read_bytes())
for n,h in {**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}.items():assert sha(ROOT/n)==h,n
DEST.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'record':str(DEST.relative_to(ROOT)),'sha256':sha(DEST),'actual_independent_reader_exit_code':a['actual_exit_code'],'actual_reader_elapsed_seconds':a['elapsed_seconds'],'errors':r['errors'],'protection_errors':r['protection_errors']}))
