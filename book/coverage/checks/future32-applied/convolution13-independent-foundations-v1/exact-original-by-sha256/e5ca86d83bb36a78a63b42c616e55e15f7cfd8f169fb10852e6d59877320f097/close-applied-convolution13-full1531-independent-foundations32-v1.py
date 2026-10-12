from pathlib import Path
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future32-applied/convolution13-independent-foundations-v1';assert not D.exists();F=Path('/tmp/applied-convolution13-full-current1531-independent-foundations32-findings-v1.json');N=Path('/tmp/applied-convolution13-full1531-independent-foundations32-actual-v1.json');Q=R/'book/coverage/checks/future31-applied/convolution13-author-components-v2/convolution13-entire-source-all-bodies-current1531-entire-literal-independent-review-request31-v1.json'
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
d=json.loads(F.read_bytes());q=json.loads(Q.read_bytes());n=json.loads(N.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]and d['errors']==[]
refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys()and isinstance(x['file'],str):refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(d)
for a in q['all_original_byte_aliases'].values():
 r=a.get('original_byte_copy',a.get('already_durable_exact_reference'));refs[r['file']]=r
paths=[F,N,path(n['log']),Path('/tmp/review-applied-convolution13-full1531-independent-foundations32-v1.py'),Path('/tmp/run-review-applied-convolution13-full1531-independent-foundations32-v1.py'),Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),Path(__file__)]
for p in paths:refs[str(p)]=ref(p)
aliases={}
for name,r in refs.items():
 p=path(name);assert sha(p)==r['sha256']
 if p.is_relative_to(R):aliases[name]={'original':r,'already_durable_exact_reference':ref(p)};continue
 target=D/'exact-original-by-sha256'/r['sha256']/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:target.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(target)}
def a(name):return aliases[str(name)].get('original_byte_copy',aliases[str(name)].get('already_durable_exact_reference'))
d['actual_reader']=d['actual_finalizer']=a(N);d['actual_finalizer_original_byte_aliases']={str(p):a(p)for p in paths[1:]};d['bounded_original_ref_aliases']=aliases;d['required_evidence_artifacts_sha256']={a(name)['file']:r['sha256']for name,r in refs.items()};d['original_full_findings']=a(F);d['fresh_current1248_Source81assets31_installed_raw_owner31five_guards_before_after_unchanged']=True;d['no_old_snapshot_or_lake_tree_or_recursive_peer_copy']=True
out=D/'applied-convolution13-entire-source-entire-current1531-whole-independent-foundations32-closed-peer-v1.json';out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'peer':ref(out),'actual_reader_elapsed_seconds':n['elapsed_seconds'],'bounded_refs':len(refs)}))
