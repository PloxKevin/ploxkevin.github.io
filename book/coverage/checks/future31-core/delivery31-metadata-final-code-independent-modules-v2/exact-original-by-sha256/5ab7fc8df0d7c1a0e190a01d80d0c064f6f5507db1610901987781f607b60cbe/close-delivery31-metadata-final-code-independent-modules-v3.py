from pathlib import Path
import hashlib,json,shutil
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future31-core/delivery31-metadata-final-code-independent-modules-v2';F=Path('/tmp/root-delivery31-metadata-preparation4-independent-modules-findings-v2.json');N=Path('/tmp/root-delivery31-metadata-preparation4-independent-modules-actual-v2.json');H=Path('/tmp/review-root-delivery31-metadata-preparation4-independent-modules-v2.py');W=Path('/tmp/run-root-delivery31-metadata-preparation4-independent-modules-v2.py');CF=Path('/tmp/modules-delivery31-metadata-commit-push3-independent-code-review-v1/delivery31-metadata-commit-push3-historical-index-observation-interface-v1.json');CN=Path('/tmp/modules-delivery31-metadata-commit-push3-independent-code-review-actual-v1.json');CH=Path('/tmp/review-root-delivery31-metadata-commit-push3-independent-modules-v1.py');CW=Path('/tmp/run-review-root-delivery31-metadata-commit-push3-independent-modules-v1.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
f=json.loads(F.read_bytes());n=json.loads(N.read_bytes());c=json.loads(CF.read_bytes());cn=json.loads(CN.read_bytes());assert n['status']=='passed'and n['actual_exit_code']==0 and n['protection_errors']==[];assert cn['status'].startswith('passed')and cn['actual_exit_code']==0 and c['errors']==[]and c['code_approved_for_exact_future_protocol']is True;assert sha(CF)=='ae7fff764bb4d69e22231f89bb4dd04c607c3c56365dcf0228093c6cea62b261';assert not D.exists();D.mkdir(parents=True)
inputs=dict(f['input_and_original_artifacts_sha256'])
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=path(x['file']);assert sha(p)==x['sha256'];inputs[str(p)]=x['sha256']
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(f);walk(c);walk(cn)
for p in[F,N,H,W,CF,CN,CH,CW,path(n['log']),path(cn['raw_log']['file']),Path(__file__)]:inputs[str(p)]=sha(p)
aliases={};required={}
for original,digest in sorted(inputs.items()):
 p=path(original);assert sha(p)==digest
 target=D/'exact-original-by-sha256'/digest/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,target)
 assert sha(target)==digest and target.stat().st_size<100000000
 aliases[original]=ref(target);required[target.relative_to(R).as_posix()]=digest

def norm(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str):
   original=str(path(x['file']));key=original if original in aliases else x['file']
   if key in aliases:return {**x,**aliases[key]}
  return {k:norm(v)for k,v in x.items()}
 if isinstance(x,list):return [norm(v)for v in x]
 return x
peer=norm(f);peer.pop('input_and_original_artifacts_sha256');peer['status']='passed_independent_delivery31_final_preparation4_and_metadataCommitPush3_full_code_protocol_actual_inputs_pending';peer['reviewed_helpers_sha256']={'book/coverage/checks/root_prepare_delivery31_metadata_v4.py':'970bc5f04f403985afa9427acea6389f605dbd616def04e91e4defc87bba1753','book/coverage/checks/root_commit_push_delivery31_metadata_v3.py':'8938681c0f80f941ae8a128270db1c303e5716c9ccf379e9392e881df6a01a8f'};peer['actual_reader']=aliases[str(N)];peer['actual_reader_helper']=aliases[str(H)];peer['actual_reader_wrapper']=aliases[str(W)];peer['actual_reader_raw_log']=aliases[str(path(n['log']))];peer['actual_reader_elapsed_seconds']=n['elapsed_seconds'];peer['metadata_commit_push3_child_full_code_findings_original']=aliases[str(CF)];peer['metadata_commit_push3_child_genuine_actual_reader']=aliases[str(CN)];peer['metadata_commit_push3_child_actual_helper']=aliases[str(CH)];peer['metadata_commit_push3_child_actual_wrapper']=aliases[str(CW)];peer['metadata_commit_push3_child_actual_raw_log']=aliases[str(path(cn['raw_log']['file']))];peer['metadata_commit_push3_child_full_code_findings']=norm(c);peer['actual_reader_exit_code']=0;peer['exact_original_aliases']=aliases;peer['required_evidence_artifacts_sha256']=required
O=D/'delivery31-final-preparation4-metadataCommitPush3-full-code-independent-modules31-closed-peer-v1.json'
with O.open('x')as out:json.dump(peer,out,indent=2);out.write('\n')
print(json.dumps({'peer':ref(O),'physical_refs':len(required),'errors':[]}))
