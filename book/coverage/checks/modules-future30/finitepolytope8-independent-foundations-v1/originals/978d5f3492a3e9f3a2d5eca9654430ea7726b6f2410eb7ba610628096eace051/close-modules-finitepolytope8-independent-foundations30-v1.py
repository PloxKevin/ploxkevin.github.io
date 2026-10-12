from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future30/finitepolytope8-independent-foundations-v1'
FIND=Path('/tmp/modules-finitepolytope8-independent-foundations30-findings-v1.json')
ACTUAL=Path('/tmp/modules-finitepolytope8-independent-foundations30-actual-v1.json')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(CONTEXT.read_bytes());protected={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in protected.items())
d=json.loads(FIND.read_bytes());a=json.loads(ACTUAL.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert sha(a['log'])==a['log_sha256'] and d['errors']==[]
paths=dict(d['required_evidence_artifacts_sha256'])
for p in [FIND,ACTUAL,Path(a['log']),Path('/tmp/run-modules-finitepolytope8-independent-foundations30-v1.py'),CONTEXT,Path(__file__)]:paths[str(p)]=sha(p)
aliases={};closed={}
for n,h in paths.items():
 p=Path(n);assert sha(p)==h
 if p.is_relative_to(ROOT/'book/coverage/checks') and p.resolve().is_relative_to(ROOT) and p.stat().st_size<100_000_000:
  q=p
 else:
  q=BASE/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 aliases[n]=ref(q);closed[str(q.relative_to(ROOT))]=h
for original,q in d['original_closed_byte_aliases'].items():
 p=Path(q['file']);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==q['sha256'];aliases[original]=aliases[str(p)]
def normalized(v):
 if isinstance(v,dict):
  z={k:normalized(w) for k,w in v.items()}
  if isinstance(v.get('file'),str):
   n=v['file'];p=Path(n);absolute=str(p if p.is_absolute() else ROOT/p)
   if absolute in aliases:
    assert v['sha256']==aliases[absolute]['sha256'];z.update(aliases[absolute])
  return z
 if isinstance(v,list):return [normalized(w) for w in v]
 return v
peer={k:normalized(v) for k,v in d.items() if k not in ['original_closed_byte_aliases','required_evidence_artifacts_sha256']}
peer.update(closed_at_utc=datetime.now(timezone.utc).isoformat(),original_full_semantic_findings=aliases[str(FIND)],
 original_review_finished_at_utc=d['review_finished_at_utc'],actual_reader=aliases[str(ACTUAL)],actual_raw_log=aliases[str(Path(a['log']))],
 reader_helper=aliases['/tmp/check-modules-finitepolytope8-independent-foundations30-v1.py'],reader_wrapper=aliases['/tmp/run-modules-finitepolytope8-independent-foundations30-v1.py'],
 actual_protected_original_context=aliases[str(CONTEXT)],actual1197_31_five_before_after_unchanged=True,
 original_byte_aliases=aliases,required_evidence_artifacts_sha256=closed,
 prospective_postfreeze_evidence_not_part_of_frozen29=True)
out=BASE/'modules-finitepolytope8-actual-history-CMDP-attained-strongduality-independent-foundations30-closed-peer-v1.json'
assert not out.exists();out.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(sha(ROOT/n)==h for n,h in closed.items()) and all(sha(ROOT/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(out),'physical_references':len(closed),'original_aliases':len(aliases),'actual_reader_code':0,'protection_errors':[]}))
