"""Independent real Pages27 configuration-only output; no producer execution."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,subprocess,os
R=Path('/home/oxrexkevin/SafetyBased');PUB=R/'reports/book/publication-repo';CACHE={}
def safe(base,n):
 assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{\x00')
 p=base/n;assert p.resolve().is_relative_to(base.resolve()) and not p.is_symlink(),n;return p
def H(n):
 p=n if isinstance(n,Path) else safe(R,n)
 if p not in CACHE:CACHE[p]=hashlib.sha256(p.read_bytes()).hexdigest()
 return CACHE[p]
def J(n):return json.loads(safe(R,n).read_bytes())
def ref(n):return {'file':n,'sha256':H(n)}
def zero(d):
 values=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert values and all(type(v) is int and v==0 for v in values)
def actual(n,command):
 d=J(n);zero(d)
 commands=[d[k] for k in ['actual_command','command'] if k in d];assert commands and all(v==command for v in commands)
 work=[d[k] for k in ['actual_workdir','working_directory','cwd'] if k in d];assert work and all(v==str(R) for v in work)
 logs=[d[k] for k in ['log','raw_log'] if k in d];digests=[d[k] for k in ['log_sha256','raw_log_sha256'] if k in d];assert logs and digests and all(v==logs[0] for v in logs) and all(v==digests[0] for v in digests);assert H(logs[0])==digests[0]
 if 'helper_sha256_before' in d or 'helper_sha256_after' in d:
  assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']
  for n,h in d['helper_sha256_after'].items():assert H(n)==h
 return d
HELP='book/coverage/checks/root_prepare_pages27_config_v5.py';HS='d7e2a4764f4678d6e7dc7c6443a732fc60224b733633db3a1646628801ebd101';CP='book/coverage/checks/pages27-config-helper-independent-modules-review-v5.json';CS='6b733443e31eaf68bdbc25898ef1c75d1c67608494a0bb91d5765c8be2920e3a'
assert H(HELP)==HS and H(CP)==CS;code=J(CP);assert code['status']=='passed' and code['errors']==[] and code['helper']=={'file':HELP,'sha256':HS} and code['real_native_readonly_prepare_passed'] is True
for n,h in code['closed_evidence_sha256'].items():assert H(n)==h,n
NATIVE='reports/full-coverage/pages27-config-preparation-v1.json';EXEC='reports/full-coverage/pages27-config-execution-v2.json';BACK='reports/full-coverage/pages27-config-previous-original-v1.yml';BR='reports/full-coverage/pages27-config-previous-original-v1.json'
v=J(NATIVE);execution=actual(EXEC,['python3',HELP,'--apply']);assert execution['helper_sha256_before']==execution['helper_sha256_after']=={HELP:HS}
assert v['status']=='passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build' and v['helper']=={'file':HELP,'sha256':HS} and v['coverage_complete'] is False
BEFORE='1c14f454e5645b9eab1b68ccadf7ea4420cd66b739072c48f65316f6b2bd6bc6';assert H(BACK)==BEFORE and v['previous_configuration']=={'file':BACK,'sha256':BEFORE};assert J(BR)=={'status':'previous_exact_pages_configuration_preserved','original_publication_path':'_config.yml','original_sha256':BEFORE,'immutable_original_byte_copy':BACK}
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n';old=safe(R,BACK).read_bytes();oldexclude={s[4:] for s in old.decode().splitlines() if s.startswith('  - ')};assert len(oldexclude)==116 and old.decode()==header+''.join('  - '+n+'\n' for n in sorted(oldexclude))
retired26={'reports/full-coverage/checkpoint-26-manifest.json':'ef777b585d9654e5dd784160dd4e9502eaae230d1f4fefcd9bdb2458c347f896','reports/full-coverage/checkpoint-26-selection.json':'12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f'}
inv={'book/coverage/inventory-before-correction54.json':'4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be','book/coverage/inventory-after-correction54.json':'5b7540b2b62cc0a51d2604ce24c170cd6a228f42f4f13ba34f0b695836be8862','book/coverage/inventory-before-correction55.json':'5b7540b2b62cc0a51d2604ce24c170cd6a228f42f4f13ba34f0b695836be8862','book/coverage/inventory-after-correction55.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'}
delivery={'reports/full-coverage/publication-checkpoint20-prestage-integrity.json':'612448dcc767d133967f17658f63d628b06e0cccb646d00182eb2b46fd9c695f','reports/full-coverage/publication-checkpoint21-prestage-integrity.json':'89c8bd444f9a88743e93ad3553c624678cffadd1f8c5d0cfcb62581a17e26a33','reports/full-coverage/publication-checkpoint22-prestage-integrity.json':'00042b8dc886b876912bb0b8cbd579cf2cebaf6ec69860368ad2aa1d8c408f46','reports/full-coverage/publication-checkpoint23-prestage-integrity.json':'8fa429be35d7f33e8218fe6ffff91b3c37732d57337aeba5d7a5055baf8a4ee1'}
ADIR='reports/full-coverage/lean-checkpoint-25';added=set(retired26)|set(inv)|set(delivery)|{ADIR,'reports/full-coverage/checkpoint-27','reports/full-coverage/owner26-originals-before-owner27-integration-v1'};assert len(added)==13 and not added&oldexclude and set(v['new_literal_exclusions'])==added
exclusions=oldexclude|added;assert len(exclusions)==v['excluded_count']==129 and sorted(exclusions)==v['exclusions'];after=(header+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode();assert safe(PUB,'_config.yml').read_bytes()==after and H(PUB/'_config.yml')==v['config_sha256']
kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
S='reports/full-coverage/checkpoint-27-selection.json';M='reports/full-coverage/checkpoint-27-manifest.json';A='reports/full-coverage/lean-checkpoint-27/verification-original.json';selection=J(S);manifest=J(M);audit=J(A);assert H(S)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['selection_sha256']==H(S) and manifest['proof_files']==selection['proof_files'] and len(selection['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1175 and selection['new_file_count']==8
assert audit['status']=='passed' and audit['theorem_count']==9644 and audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()} and len(audit['declarations'])==len(audit['axiom_dependencies'])==9644
for row in audit['checks']:zero(row)
assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==8 and sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1167
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'} and all(set(values)<=set(audit['allowed_standard_axioms']) for values in audit['axiom_dependencies'].values())
success=manifest['successful_verification'];assert success['report']==A and success['report_sha256']==H(A) and success['proof_file_count']==1175 and success['theorem_count']==9644 and type(success['all_check_exit_codes']) is int and success['all_check_exit_codes']==0
prereq={}
for stem,cmd in [('verify-checkpoint27',['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(R/'reports/full-coverage/checkpoint-26')]),('export-checkpoint27',['python3','book/coverage/export_audit27_v3.py','--snapshot','reports/full-coverage/checkpoint-27','--output','reports/full-coverage/lean-checkpoint-27']),('prepare-publication27',['python3','book/coverage/prepare_publication.py','27'])]:
 n='reports/full-coverage/'+stem+'-execution-v1.json';actual(n,cmd);prereq[stem]=ref(n)
assert v['actual_prerequisite_executions']==prereq
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31 and assets['SafeLearning/lyapunov-mpc.html']=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f' and assets['SafeLearning/verification.html']=='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
required={};working={};published={}
def same(n,h):assert H(n)==H(safe(PUB,n))==h,n
for n,h in assets.items():same(n,h);required[n]=h
for n,h in {'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'}.items():
 same(n,h);assert manifest['frozen_inputs_sha256'][n]==H(manifest['snapshot']+'/'+n)==h;required[n]=h
prior=J('reports/full-coverage/checkpoint-26-manifest.json')
for owner in ['core','foundations','applied','modules']:
 n='book/coverage/'+owner+'.json';working[n]=manifest['working_inputs_sha256'][n];published[n]=manifest['frozen_inputs_sha256'][n];assert H(n)==working[n] and H(safe(PUB,n))==H(manifest['snapshot']+'/'+n)==published[n]
 row=copy.deepcopy(J(n));removed=manifest['excluded_unreferenced_ledger_metadata'][owner];assert removed==prior['excluded_unreferenced_ledger_metadata'][owner] and len(removed)==(3 if owner=='applied' else 0)
 for proof in removed:assert proof in row['proof_files'] and proof not in selection['proof_files'];row['proof_files'].pop(proof)
 assert row==json.loads(safe(PUB,n).read_bytes());required[n]=published[n]
n='book/coverage/applied-promotions.json';h=manifest['working_inputs_sha256'][n];assert h==manifest['frozen_inputs_sha256'][n];same(n,h);required[n]=h
for n in [M,S,A,'reports/full-coverage/integration-27.json','reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/browser-checkpoint-27.json','reports/full-coverage/browser-corrections-27-inputs.json']:same(n,H(n));required[n]=H(n)
adir='reports/full-coverage/lean-checkpoint-27';amap={p.relative_to(R).as_posix():H(p) for p in (R/adir).rglob('*') if p.is_file()};assert amap and {p.relative_to(PUB).as_posix():H(p) for p in (PUB/adir).rglob('*') if p.is_file()}==amap
for n,h in amap.items():same(n,h);required[n]=h
browser=J('reports/full-coverage/browser-checkpoint-27.json');bi=J('reports/full-coverage/browser-corrections-27-inputs.json');assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['page_count']==29 and browser['requested_viewport_count']==browser['verified_viewport_count']==145 and browser['fresh_verified_viewport_count']==10 and browser['retained_verified_viewport_count']==135 and browser['screenshot_count']==48 and browser['skipped_capture_target_count']==10 and browser['source_sha256']==assets
freshname=browser['actual_execution'];assert H(freshname)==browser['actual_execution_sha256'] and bi['actual_execution']==ref(freshname);fresh=actual(freshname,['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source55-27-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source55-27-v1','lyapunov-mpc.html','verification.html']);assert fresh['source_sha256_before']==fresh['source_sha256_after']==assets and fresh['qa_source_sha256']==browser['qa_source_sha256'] and len(browser['qa_source_sha256'])==2
for n,h in browser['qa_source_sha256'].items():same(n,h);required[n]=h
assert H(fresh['report'])==fresh['report_sha256'];same(freshname,H(freshname));required[freshname]=H(freshname);same(fresh['report'],fresh['report_sha256']);required[fresh['report']]=fresh['report_sha256'];assert len(bi['screenshot_aliases'])==len({x['file'] for x in bi['screenshot_aliases']})==48
for row in bi['screenshot_aliases']:
 n,h=row['file'],row['sha256'];assert n.startswith('reports/full-coverage/browser-artifacts-27/');same(n,h);required[n]=h
 if row['evidence_mode']=='fresh_actual_source55_browser_execution':assert row['original'].startswith('reports/full-coverage/browser-artifacts-source55-27-v1/');same(row['original'],h);required[row['original']]=h
assert len(required)==1284 and required==v['required_publication_files_sha256'] and working==v['working_ledger_sha256'] and published==v['published_frozen_ledger_sha256'] and v['exact_original_metadata_removals']==manifest['excluded_unreferenced_ledger_metadata'] and all(kept(n) for n in required)
assert v['retired_completed26_direct_manifest_selection_sha256']==retired26 and v['older_delivery_file_archives_sha256']==delivery and v['duplicate_source54_55_inventory_sha256']==inv
for n,h in inv.items():same(n,h);assert manifest['frozen_inputs_sha256'][n]==H(manifest['snapshot']+'/'+n)==h and not kept(n)
oldmap={p.relative_to(R).as_posix():H(p) for p in (R/ADIR).rglob('*') if p.is_file()};assert len(oldmap)==1165 and v['older25_audit_archives_sha256']==oldmap and {p.relative_to(PUB).as_posix():H(p) for p in (PUB/ADIR).rglob('*') if p.is_file()}==oldmap
head=subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()
for name,group in [(ADIR,oldmap)]+[(n,{n:h}) for n,h in {**retired26,**delivery}.items()]:
 tracked=subprocess.run(['git','ls-files','-z','--',name],cwd=PUB,check=True,capture_output=True).stdout.decode().split('\0');assert {x for x in tracked if x}==set(group)
 tree=subprocess.run(['git','ls-tree','-rz','HEAD','--',name],cwd=PUB,check=True,capture_output=True).stdout;heads={}
 for raw in tree.split(b'\0'):
  if not raw:continue
  info,path=raw.split(b'\t',1);mode,kind,oid=info.split();assert mode in [b'100644',b'100755'] and kind==b'blob';heads[path.decode()]=oid.decode()
 assert set(heads)==set(group)
 for n,h in group.items():
  same(n,h);assert not kept(n);b=safe(PUB,n).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==heads[n]
 subprocess.run(['git','diff','--quiet','HEAD','--',name],cwd=PUB,check=True)
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==head
assert v['older_retired_archives_all_root_publication_tracked_HEAD_exact'] is True and v['retired_completed26_direct_archives_root_pub_tracked_HEAD_exact'] is True and v['duplicate_inventory_bytes_exact_in_root_publication_and_frozen27'] is True
count=0
for top,dirs,files in os.walk(PUB,followlinks=False):
 root=Path(top)
 for dn in list(dirs):
  q=root/dn;n=q.relative_to(PUB).as_posix()
  if '.git' in q.relative_to(PUB).parts or not kept(n):dirs.remove(dn);continue
  assert not q.is_symlink(),n
 for fn in files:
  q=root/fn;n=q.relative_to(PUB).as_posix()
  if not kept(n):continue
  assert not q.is_symlink(),n;count+=q.stat().st_size
assert count==v['prospective_included_website_bytes_before_new_native_records']
assert all(not (PUB/n).exists() for n in [NATIVE,BACK,BR]);nativebytes=sum(safe(R,n).stat().st_size for n in [NATIVE,BACK,BR]);assert count+nativebytes==v['prospective_included_website_bytes_including_native_records']<v['website_budget_bytes']==850000000
failed='reports/full-coverage/pages27-config-execution-v1.json';f=J(failed);assert type(f['actual_exit_code']) is int and f['actual_exit_code']==1 and f['actual_command']==['python3','book/coverage/checks/root_prepare_pages27_config_v3.py','--apply'] and H(f['log'])==f['log_sha256']
closed={n:H(n) for n in [HELP,CP,NATIVE,EXEC,execution['log'],BACK,BR,M,S,A,failed,f['log'],'book/coverage/checks/pages27-config-helper-independent-modules-review-v4.json','reports/full-coverage/approved-inventory55-exact-byte-restoration28-v1.json']};closed.update(required)
for row in prereq.values():closed[row['file']]=row['sha256']
out={'status':'passed_independent_actual_checkpoint27_pages_configuration','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':HELP,'sha256':HS},'helper_sha256':HS,'config_sha256':v['config_sha256'],'excluded_count':129,'selected_sources':1175,'public_theorems':9644,'new_kernel_replays':8,'reused_identical_sources':1167,'native_configuration_report':ref(NATIVE),'native_preparation_report':ref(NATIVE),'actual_configuration_execution':ref(EXEC),'actual_execution':ref(EXEC),'actual_configuration_raw_log':ref(execution['log']),'independent_configuration_code_peer':ref(CP),'original_configuration_byte_copy':ref(BACK),'required_publication_files_sha256':required,'required_download_count':1284,'working_ledger_sha256':working,'published_frozen_ledger_sha256':published,'actual_current_included_website_bytes':count,'projected_bytes_including_closed_native_outputs':count+nativebytes,'website_budget_bytes':850000000,'exact_retired25_files':oldmap,'exact_retired20_23_delivery_files':delivery,'retired_Git_HEAD':head,'entire_native_configuration_report_body_and_time':v,'original_failed_configuration_execution':ref(failed),'entire_original_failed_configuration_body_and_time':f,'closed_evidence_sha256':closed,'coverage_complete':False,'all48_current27_screenshots_exact_and_public':True,'scope':'Independent genuine configuration-only output. Complete current27 and baseline26 Lean downloads, current55 assets31, current5owners/frozen3metadata pruning and browser145/48 remain exact. Old25 audit/four delivery records retained in Root/PUB/Git HEAD, website-only retired. No Pages build, deployment, live check or whole mathematical coverage inferred.'}
p=Path('/tmp/pages27-config5-actual-output-independent-modules-confirmation-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'config_sha256':v['config_sha256'],'included_website_bytes':count,'projected_native_bytes':count+nativebytes}))
