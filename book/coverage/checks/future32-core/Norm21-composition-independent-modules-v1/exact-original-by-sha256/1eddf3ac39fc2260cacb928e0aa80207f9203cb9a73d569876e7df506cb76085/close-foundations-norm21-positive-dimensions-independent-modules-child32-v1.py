from pathlib import Path
import hashlib,json,shutil
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future32-core/norm21-positive-dimensions-independent-modules-child-v1'
F=Path('/tmp/modules-child-norm21-positive-dimensions-independent32-findings-v3.json');N=Path('/tmp/modules-child-norm21-positive-dimensions-independent32-actual-v3.json');H=Path('/tmp/review-foundations-norm21-positive-dimensions-independent-modules-child32-v3.py');W=Path('/tmp/run-foundations-norm21-positive-dimensions-independent-modules-child32-v3.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
f=json.loads(F.read_bytes());n=json.loads(N.read_bytes());assert n['status']=='passed' and n['actual_exit_code']==0 and n['protection_errors']==[]
assert n['helper_sha256_before']==n['helper_sha256_after'];assert n['helper_sha256_before'][str(H)]==sha(H) and n['helper_sha256_before'][str(W)]==sha(W)
assert sha(path(n['log']))==n['log_sha256'];assert f['errors']==[] and f['protection_errors']==[]
assert not D.exists();D.mkdir(parents=True)
inputs=dict(f['input_and_original_artifacts_sha256']);inputs.update({str(p):sha(p) for p in [F,N,H,W,path(n['log']),Path(__file__)]});aliases={};required={}
for original,digest in sorted(inputs.items()):
 p=path(original);assert sha(p)==digest,original
 target=D/'exact-original-by-sha256'/digest/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,target)
 assert sha(target)==digest;aliases[original]=ref(target);required[target.relative_to(R).as_posix()]=digest

def normalize(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str) and isinstance(x.get('sha256'),str):
   original=str(path(x['file']));key=original if original in aliases else x['file']
   if key in aliases:return {**x,**aliases[key]}
  return {k:normalize(v) for k,v in x.items()}
 if isinstance(x,list):return [normalize(v) for v in x]
 return x
peer=normalize(f);peer.pop('input_and_original_artifacts_sha256');peer['actual_reader']=aliases[str(N)];peer['actual_reader_helper']=aliases[str(H)];peer['actual_reader_wrapper']=aliases[str(W)];peer['actual_reader_raw_log']=aliases[str(path(n['log']))]
peer['actual_reader_exit_code']=0;peer['actual_reader_started_at_utc']=n['started_at_utc'];peer['actual_reader_finished_at_utc']=n['finished_at_utc'];peer['actual_reader_elapsed_seconds']=n['elapsed_seconds'];peer['actual_reader_native_command_helper_log_time_preserved_exactly']=True
peer['exact_original_aliases']=aliases;peer['required_evidence_artifacts_sha256']=required;peer['durable_closure_no_original_artifact_mutations']=True
O=D/'foundations-common-norm21-positive-dimensions-one-phrase-full-literal-independent-parser-independent-modules-child32-closed-peer-v1.json'
with O.open('x') as out:json.dump(peer,out,indent=2,ensure_ascii=False);out.write('\n')
# Every operational typed reference is now immutable Root physical evidence; original JSON bytes remain separate exact aliases.
def verify(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str) and isinstance(x.get('sha256'),str):
   p=path(x['file']);assert p.is_relative_to(D) and sha(p)==x['sha256'],x
   if 'bytes' in x:assert p.stat().st_size==x['bytes']
  for v in x.values():verify(v)
 elif isinstance(x,list):
  for v in x:verify(v)
verify(peer)
for original,digest in inputs.items():assert sha(path(original))==digest
print(json.dumps({'peer':ref(O),'physical_refs':len(required),'aliases':len(aliases),'native_elapsed_seconds':n['elapsed_seconds'],'errors':[]}))
