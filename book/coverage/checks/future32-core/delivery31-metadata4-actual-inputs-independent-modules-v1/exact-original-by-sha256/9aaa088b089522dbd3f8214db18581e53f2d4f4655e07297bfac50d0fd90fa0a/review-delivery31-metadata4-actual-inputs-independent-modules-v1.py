from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,tempfile
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/delivery31-metadata4-actual-inputs-independent-modules-findings-v1.json');B=Path('/tmp/modules-delivery31-metadata4-actual-before-originals-v1');PREP='book/coverage/checks/root_prepare_delivery31_metadata_v4.py';PREPH='970bc5f04f403985afa9427acea6389f605dbd616def04e91e4defc87bba1753';CP='book/coverage/checks/future31-core/delivery31-metadata-final-code-independent-modules-v2/delivery31-final-preparation4-metadataCommitPush3-full-code-independent-modules31-closed-peer-v1.json';CPH='81fd110a112ae165ba1e14d1c879e3c38812e223d1467662a8c0f67a01562285'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def git(args):return subprocess.run(['git',*args],cwd=P,capture_output=True,check=True).stdout
refs={}
def read(n):
 p=path(n);refs[str(p)]=sha(p);return json.loads(p.read_bytes())
def checked_native(n,command,cwd,logkey='log',shakey='log_sha256'):
 d=read(n);assert d['status']=='passed'and type(d['actual_exit_code'])is int and d['actual_exit_code']==0 and d['actual_command']==command and d['actual_workdir']==cwd
 l=path(d[logkey]);assert sha(l)==d[shakey];refs[str(l)]=sha(l);return d
assert sha(C)==CH and not F.exists()and not B.exists();ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
 return []
guard();assert sha(R/PREP)==PREPH and sha(R/CP)==CPH;refs[str(R/PREP)]=PREPH;peer=read(CP);assert peer['full_code_read']is True and peer['errors']==[]and peer['reviewed_helpers_sha256'][PREP]==PREPH
assert peer['reviewed_helpers_sha256']['book/coverage/checks/root_commit_push_delivery31_metadata_v3.py']=='8938681c0f80f941ae8a128270db1c303e5716c9ccf379e9392e881df6a01a8f'
commit=checked_native('reports/full-coverage/publication31-content-commit-v1.json',['git','commit','--quiet','-m','Verify checkpoint 31 source corrections and six additional Lean proof files'],str(P),'raw_log','raw_log_sha256');content=commit['commit'];assert content=='06271d02a5bf0d99e59066b1ee5244bc465958de'and commit['baseline_publication_head']=='676db1f7d13ddbf65c2f0253d1fab79c44948a7e'
assert git(['rev-parse','HEAD']).decode().strip()==content and git(['symbolic-ref','--short','HEAD']).decode().strip()=='main'and git(['rev-parse','refs/heads/main']).decode().strip()==content and git(['rev-parse','HEAD^']).decode().strip()==commit['baseline_publication_head']
assert not git(['status','--porcelain','-z','--untracked-files=all'])
expected=commit['actual_committed_paths_sha256'];assert len(expected)==4786 and expected==commit['expected_committed_paths_sha256']
changed={n.decode()for n in git(['diff-tree','--no-commit-id','--name-only','-r','-z','--no-renames',commit['baseline_publication_head'],content]).split(b'\0')if n};assert changed==set(expected)
objects={}
for row in git(['ls-tree','-r','-z',content]).split(b'\0'):
 if not row:continue
 header,name=row.split(b'\t',1);name=name.decode()
 if name in changed:
  mode,kind,oid=header.split();assert mode==b'100644'and kind==b'blob';objects[name]=oid.decode();assert sha(P/name)==expected[name]
assert set(objects)==changed;unique=sorted(set(objects.values()));hashes={}
with tempfile.TemporaryFile()as req:
 req.write(('\n'.join(unique)+'\n').encode());req.seek(0);p=subprocess.Popen(['git','cat-file','--batch'],cwd=P,stdin=req,stdout=subprocess.PIPE)
 try:
  for oid in unique:
   actual,kind,size=p.stdout.readline().split();assert actual.decode()==oid and kind==b'blob';remaining=int(size);h=hashlib.sha256()
   while remaining:
    data=p.stdout.read(min(1048576,remaining));assert data;h.update(data);remaining-=len(data)
   assert p.stdout.read(1)==b'\n';hashes[oid]=h.hexdigest()
  assert p.stdout.read()==b''and p.wait()==0
 finally:
  if p.poll()is None:p.terminate();p.wait()
assert {name:hashes[oid]for name,oid in objects.items()}==expected
push=checked_native('reports/full-coverage/publication31-content-push-v1.json',['git','push','origin','main'],str(P),'raw_log','raw_log_sha256');assert push['commit']==push['remote_main_after']==content and push['remote_main_before']==commit['baseline_publication_head']
assert git(['ls-remote','origin','refs/heads/main']).decode().split()[0]==content
contenthelper='book/coverage/checks/root_commit_push_publication31_v3.py';hh=sha(R/contenthelper);refs[str(R/contenthelper)]=hh
for assoc in[commit,push]:
 original=read(assoc['actual_command_receipt']['file']);assert sha(path(assoc['actual_command_receipt']['file']))==assoc['actual_command_receipt']['sha256']and all(original[k]==assoc[k]for k in original)
 assert original['actual_exit_code']==0 and original['status']=='passed'and original['helper_sha256']==hh
for mode in ['commit','push']:
 n=checked_native('reports/full-coverage/'+mode+'-publication31-execution-v1.json',['python3',contenthelper,mode],str(R));assert n['helper_sha256_before']==n['helper_sha256_after']=={contenthelper:hh}
manifest=read('reports/full-coverage/checkpoint-31-manifest.json');assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
live=read('reports/full-coverage/live-checkpoint-31-attempt2.json');assert live['status']=='passed_all31_asset_sha256'and live['commit']==live['remote_main']==content and len(live['assets'])==31
assert {a['source']:a['expected_sha256']for a in live['assets']}==assets and all(a['matches']is True and a['http_status']==200 and a['actual_sha256']==a['expected_sha256']for a in live['assets'])
pages=read('reports/full-coverage/pages-checkpoint-31-attempt2.json');assert pages['status']=='passed'and pages['exit_code']==0 and pages['commit']==pages['expected_commit']==content and pages['build_status']=='built'and pages['actual_workdir']==str(P)and pages['command']==['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'];assert sha(path(pages['log']))==pages['log_sha256'];refs[str(path(pages['log']))]=pages['log_sha256'];page_raw=json.loads(path(pages['log']).read_bytes());assert page_raw['commit']==content and page_raw['status']=='built'
ln=checked_native('reports/full-coverage/live31-content-confirmation-execution-v2.json',['python3','book/coverage/verify_live19.py','31',content,'--attempt','2'],str(R));assert ln['helper_sha256_before']==ln['helper_sha256_after']=={'book/coverage/verify_live19.py':sha(R/'book/coverage/verify_live19.py')}
jobsnative=read('reports/full-coverage/pages31-content-jobs-observation-execution-v1.json');assert jobsnative['status']=='passed'and jobsnative['actual_exit_code']==0 and jobsnative['actual_command'][:2]==['gh','api']and jobsnative['actual_command'][2].startswith('repos/PloxKevin/ploxkevin.github.io/actions/runs/')and jobsnative['actual_command'][2].endswith('/jobs');assert sha(path(jobsnative['log']))==jobsnative['log_sha256'];refs[str(path(jobsnative['log']))]=jobsnative['log_sha256'];jobs=json.loads(path(jobsnative['log']).read_bytes());assert len(jobs['jobs'])==3 and all(j['head_sha']==content and j['conclusion']=='success'and j['status']=='completed'for j in jobs['jobs'])
failed=read('reports/full-coverage/live31-content-confirmation-execution-v1.json');assert failed['status']=='failed'and failed['actual_exit_code']==1 and failed['actual_command']==['python3','book/coverage/verify_live19.py','31',content,'--attempt','1'];assert sha(path(failed['log']))==failed['log_sha256'];refs[str(path(failed['log']))]=failed['log_sha256'];read('reports/full-coverage/live-checkpoint-31-attempt1.json');read('reports/full-coverage/pages-checkpoint-31-attempt1.json')
# Check exact metadata before-state and retain physical immutable aliases, avoiding an old-SHA key on mutable progress/README.
B.mkdir();before={}
for name in['book/coverage/progress.json','reports/full-coverage/README.md']:
 p=R/name;target=B/Path(name).name;target.write_bytes(p.read_bytes());assert sha(p)==sha(target);before[name]=ref(target);refs[str(target)]=sha(target)
progress=json.loads((B/'progress.json').read_bytes());assert progress['verified_checkpoint']['checkpoint']==31 and progress['verified_checkpoint']['status']=='passed'and progress['verified_checkpoint']['proof_files']==1248 and progress['verified_checkpoint']['theorems']==11184
assert (B/'README.md').read_text().count('Checkpoint 31 is verified locally; its GitHub delivery is pending.')==1
assert not(R/'reports/full-coverage/publication31-delivery-metadata-preparation-v1.json').exists()and not(R/'reports/full-coverage/source-history/checkpoint31-before-content-delivery-metadata-v1').exists()
assert git(['rev-parse','HEAD']).decode().strip()==content and not git(['status','--porcelain','-z','--untracked-files=all'])
guard()
f={'status':'passed_independent_delivery31_metadata_preparation4_full_actual_content_push_Pages_and_all31_live_input_review','errors':[],'full_code_read':True,'reviewed_helpers_sha256':peer['reviewed_helpers_sha256'],'original_static_full_code_peer':ref(R/CP),'actual_content_commit':ref(R/'reports/full-coverage/publication31-content-commit-v1.json'),'actual_content_push':ref(R/'reports/full-coverage/publication31-content-push-v1.json'),'content_commit':content,'actual_committed4786_path_delta_mode100644_blob_and_SHA_replayed_independently':True,'actual_commit_push_immutable_original_command_receipt_fields_log_helper_cwd_time_preserved':True,'actual_remote_main_and_clean_local_main_equal_content':True,'actual_adaptive_live_attempt':2,'actual_live_native':ref(R/'reports/full-coverage/live31-content-confirmation-execution-v2.json'),'actual_all31_manifest_asset_SHA_HTTP200_matches':True,'actual_successful_same_commit_Pages_build_and_three_jobs_checked':True,'original_true_live_attempt1_failure_preserved':ref(R/'reports/full-coverage/live31-content-confirmation-execution-v1.json'),'original_progress_and_README_before_bytes':before,'metadata_preparation4_actual_input_gates_approved':True,'metadata_commit_push3_protocol_approved_after_exact_future_actual_preparation_native_and_whitelist_exist':True,'metadata_preparation_invoked_or_metadata_commit_push_live_success_claimed':False,'actual_selected31_source_and_raw_owner_and_all_current_assets_protected':True,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2);out.write('\n')
print(json.dumps({'status':f['status'],'content_commit':content,'actual_committed_paths':len(expected),'all31live_attempt':2,'errors':[]}))
