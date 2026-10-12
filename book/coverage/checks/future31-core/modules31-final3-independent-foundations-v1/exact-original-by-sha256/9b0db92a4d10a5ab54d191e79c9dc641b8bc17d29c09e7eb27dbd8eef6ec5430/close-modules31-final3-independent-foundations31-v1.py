from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=ROOT/'book/coverage/checks/future31-core/modules31-final3-independent-foundations-v1'
assert not DEST.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
semantic='/tmp/modules31-final3-independent-foundations31-semantic-v1.json';d=json.loads(Path(semantic).read_bytes())
native='/tmp/modules31-final3-independent-foundations31-actual-v1.json';n=json.loads(Path(native).read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]
refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys() and isinstance(x['file'],str):refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(d)
for name in [semantic,native,n['log'],'/tmp/review-modules31-final3-independent-foundations31-v1.py','/tmp/run-review-modules31-final3-independent-foundations31-v1.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json',str(Path(__file__))]:refs[name]=ref(name)
aliases={}
for name,r in refs.items():
 p=path(name);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 if p.is_relative_to(ROOT):aliases[name]={'original':r,'already_durable_exact_reference':ref(p)};continue
 q=DEST/'exact-original-by-sha256'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(q)}
def alias(n):return aliases[n].get('original_byte_copy',aliases[n].get('already_durable_exact_reference'))
d['actual_finalizer']=alias(native);d['actual_reader']=alias(native)
d['actual_finalizer_original_byte_aliases']={p:alias(p) for p in [native,n['log'],'/tmp/review-modules31-final3-independent-foundations31-v1.py','/tmp/run-review-modules31-final3-independent-foundations31-v1.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json']}
d['all_original_byte_aliases']=aliases
d['exact_original_mutable_owner_to_existing_immutable_whole_byte_aliases']={'book/coverage/modules.json':d['original_whole_owner30']}
d['required_evidence_artifacts_sha256']={alias(name)['file']:r['sha256'] for name,r in refs.items()}
d['no_recursive_peer_or_old_snapshot_or_lake_tree_copy']=True
d['genuine_original_reader_body_and_time_preserved']=True
p=DEST/'modules31-current81-Integral39-AST19-real2-pair-full-final3-mapping-independent-foundations31-closed-peer-v1.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'peer':ref(p),'actual_finalizer':d['actual_finalizer'],'elapsed_seconds':n['elapsed_seconds'],'bounded_direct_refs':len(refs)}))
