from pathlib import Path
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future31-core/explorer7-independent-modules-v1'
assert not B.exists();B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p)
 if p.is_relative_to(R) and '.lake'not in p.parts and p.parts[:len(R.parts)+2]!=(*R.parts,'book','coverage'):
  pass
 q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':str(q.relative_to(R)),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;return r
P=Path('/tmp/foundations-explorer7-independent-modules31-v1/foundations-explorer7-full-two-current-captions-independent-modules31-peer-v1.json')
d=json.loads(P.read_bytes());assert d['errors']==[];d.pop('original_checked_closure',None)
def closed(v):
 if isinstance(v,list):return [closed(x)for x in v]
 if isinstance(v,dict):
  if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str):
   p=Path(v['file']);p=p if p.is_absolute()else R/p;assert sha(p)==v['sha256']
   return {**{k:closed(x)for k,x in v.items()if k not in ['file','sha256','bytes']},**copy(p)}
  return {k:closed(x)for k,x in v.items()}
 return v
d=closed(d)
Q=Path('/tmp/foundations-explorer7-two-captions-review31-v1/foundations-explorer7-full-source-current1437-1452-two-captions-independent-review-request31-v1.json');q=json.loads(Q.read_bytes())
for p,h in q['all_physical_original_inputs_sha256'].items():assert sha(p)==h;copy(p)
for old,r in q['all_original_byte_aliases'].items():aliases[old]=copy(r['file'])
for v in [1]:
 for p in [Path(f'/tmp/review-foundations-explorer7-independent-modules31-v{v}.py'),Path(f'/tmp/run-foundations-explorer7-independent-modules31-v{v}.py'),Path(f'/tmp/foundations-explorer7-independent-modules31-actual-v{v}.json'),Path(f'/tmp/foundations-explorer7-independent-modules31-actual-v{v}.log')]:copy(p)
n=Path('/tmp/foundations-explorer7-independent-modules31-actual-v1.json');a=json.loads(n.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
d['actual_finalizer']=copy(n);d['original_semantic_peer']=copy(P)
d['actual_finalizer_original_byte_aliases']={k:aliases[k]for k in [*a['helper_sha256_before'],a['raw_log']]}
d['own_reader_first_attempt_true_zero']=True
copy(Path(__file__));d['original_closed_byte_aliases']=aliases
d['required_evidence_artifacts_sha256']={r['file']:r['sha256']for r in aliases.values()}
d['fresh_after_checkpoint30_freeze_and_separate_future_material_scope']=True
O=B/'foundations-explorer7-full-source-current1437-1452-two-whole-captions-independent-modules31-closed-peer-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'peer':str(O.relative_to(R)),'sha256':sha(O),'bytes':O.stat().st_size,'physical_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),'actual_reader_sha256':sha(n)}))
