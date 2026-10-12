from pathlib import Path
import hashlib,json,shutil
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future32-core/PositiveSubunitP5-independent-modules-v1';F=Path('/tmp/foundations-PositiveSubunitP5-independent-modules32-findings-v1.json');N=Path('/tmp/foundations-PositiveSubunitP5-independent-modules32-actual-v1.json');H=Path('/tmp/review-foundations-PositiveSubunitP5-full171-independent-modules32-v1.py');W=Path('/tmp/run-foundations-PositiveSubunitP5-full171-independent-modules32-v1.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
f=json.loads(F.read_bytes());n=json.loads(N.read_bytes());assert n['status']=='passed'and n['actual_exit_code']==0 and n['protection_errors']==[];assert not D.exists();D.mkdir(parents=True)
inputs=dict(f['input_and_original_artifacts_sha256'])
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=path(x['file']);assert sha(p)==x['sha256'];inputs[str(p)]=x['sha256']
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(f)
inputs.update({str(p):sha(p)for p in[F,N,H,W,path(n['log']),Path(__file__)]});aliases={};required={}
for original,digest in sorted(inputs.items()):
 p=path(original);assert sha(p)==digest
 target=D/'exact-original-by-sha256'/digest/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,target)
 assert sha(target)==digest and target.stat().st_size<100000000
 aliases[original]=ref(target);required[target.relative_to(R).as_posix()]=digest

def normalize(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str):
   original=str(path(x['file']));key=original if original in aliases else x['file']
   if key in aliases:return {**x,**aliases[key]}
  return {k:normalize(v)for k,v in x.items()}
 if isinstance(x,list):return [normalize(v)for v in x]
 return x
peer=normalize(f);peer.pop('input_and_original_artifacts_sha256');peer['actual_reader']=aliases[str(N)];peer['actual_reader_helper']=aliases[str(H)];peer['actual_reader_wrapper']=aliases[str(W)];peer['actual_reader_raw_log']=aliases[str(path(n['log']))];peer['actual_reader_exit_code']=0;peer['actual_reader_elapsed_seconds']=n['elapsed_seconds'];peer['actual_reader_native_command_helper_log_time_preserved_exactly']=True;peer['exact_original_aliases']=aliases;peer['required_evidence_artifacts_sha256']=required;peer['durable_closure_no_original_artifact_mutations']=True
O=D/'foundations-PositiveSubunitP5-current171-components-prospective171-whole-full-mathematical-independent-modules32-closed-peer-v1.json'
with O.open('x')as out:json.dump(peer,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'peer':ref(O),'physical_refs':len(required),'aliases':len(aliases),'native_elapsed_seconds':n['elapsed_seconds'],'errors':[]}))
