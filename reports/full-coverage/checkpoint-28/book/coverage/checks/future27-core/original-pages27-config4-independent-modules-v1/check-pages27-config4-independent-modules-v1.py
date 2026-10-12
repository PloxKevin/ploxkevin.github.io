from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util,tempfile,os,copy
R=Path('/home/oxrexkevin/SafetyBased');N='book/coverage/checks/root_prepare_pages27_config_v4.py';P=R/N;OLD='book/coverage/checks/root_prepare_pages27_config_v3.py';PR='book/coverage/checks/pages27-config-helper-independent-modules-review-v3.json';OUT=Path('/tmp/pages27-config4-independent-modules-check-result-v1.json');assert not OUT.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P)=='9f9f683d3400d071b089876f834711d07c9ecc172b6bd39d6277e0a6cfc85f44'
assert sha(R/OLD)=='bd6e79efaeaec954549be2e8d0158ee494244c955874aa1a7441eca601caf2cb'
assert sha(R/PR)=='e175a6e1cfd765c20b739f6695d028d18e6612fb540a5b4c7ac2e682c02eab6f'
s=P.read_text();restored=s.replace("HELPER='book/coverage/checks/root_prepare_pages27_config_v4.py'","HELPER='book/coverage/checks/root_prepare_pages27_config_v3.py'").replace("  if '.git' in rel.parts or not kept(rel.as_posix(),exclusions):continue","  if '.git' in rel.parts:continue").replace("  if p.is_file():total+=p.stat().st_size","  if p.is_file() and kept(rel.as_posix(),exclusions):total+=p.stat().st_size")
assert restored==(R/OLD).read_text(),'entire old source restored by exact self-name/exclusion-before-symlink delta'
prior=json.loads((R/PR).read_bytes());assert prior['status']=='passed' and prior['errors']==[]
for n,h in prior['closed_evidence_sha256'].items():assert sha(R/n)==h,n
spec=importlib.util.spec_from_file_location('pages27_config4_independent',P);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
failn='reports/full-coverage/pages27-config-execution-v1.json';findn='reports/full-coverage/pages27-config-helper3-prewrite-failure-finding-v1.json';failure=json.loads((R/failn).read_bytes());assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1 and failure['actual_command']==['python3',OLD,'--apply'] and failure['actual_workdir']==str(R);assert sha(R/failure['log'])==failure['log_sha256'];finding=json.loads((R/findn).read_bytes())
protected={n:sha(R/n) for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json',N,OLD,PR,failn,findn]}
config_before=sha(m.PUB/'_config.yml')
assert config_before==m.BEFORE
base=Path(tempfile.mkdtemp(prefix='pages27-config4-symlink-fixtures-'));fixtures=[]
def good(name):fixtures.append({'name':name,'result':'passed','scope':'isolated code fixture, no producer execution'})
def reject(name,fn):
 try:fn()
 except AssertionError:good(name);return
 raise AssertionError('accepted rejecting fixture '+name)
def tree(name):p=base/name;p.mkdir();return p
p=tree('excluded_directory_external_symlink');(p/'keep').write_bytes(b'123');external=base/'external';external.mkdir();(external/'data').write_bytes(b'external');(p/'excluded').symlink_to(external,target_is_directory=True);assert m.included_tree_bytes(p,{'excluded'})==3;good('excluded_directory_external_symlink_is_not_included_or_followed')
p=tree('excluded_file_symlink');(p/'keep').write_bytes(b'12');(p/'excluded').symlink_to(external/'data');assert m.included_tree_bytes(p,{'excluded'})==2;good('exact_excluded_file_symlink_not_included')
p=tree('excluded_dangling_symlink');(p/'excluded').symlink_to(base/'absent');assert m.included_tree_bytes(p,{'excluded'})==0;good('excluded_dangling_symlink_not_included')
p=tree('excluded_ancestor');(p/'excluded').mkdir();(p/'excluded'/'package').symlink_to(external,target_is_directory=True);assert m.included_tree_bytes(p,{'excluded'})==0;good('literal_excluded_ancestor_skips_nested_package_symlink')
for name,target in [('included_file_link',external/'data'),('included_directory_link',external),('included_dangling_link',base/'absent')]:
 p=tree(name);(p/'included').symlink_to(target,target_is_directory=target.is_dir());reject(name,lambda p=p:m.included_tree_bytes(p,{'excluded'}))
p=tree('literal_prefix_boundary');(p/'excluded-other').symlink_to(external,target_is_directory=True);reject('excluded_name_does_not_allow_similar_included_prefix',lambda:m.included_tree_bytes(p,{'excluded'}))
p=tree('ordinary_included_and_excluded_files');(p/'keep').write_bytes(b'12345');(p/'excluded').mkdir();(p/'excluded'/'nested').write_bytes(b'123456789');assert m.included_tree_bytes(p,{'excluded'})==5;good('ordinary_included_byte_count_excludes_literal_subtree')
p=tree('git_dir_unchanged');(p/'.git').mkdir();(p/'.git'/'cache').symlink_to(external);(p/'keep').write_bytes(b'1');assert m.included_tree_bytes(p,set())==1;good('existing_git_internal_exclusion_unchanged')
# Complete REAL native prepare is read-only: actual27 audit/export/PUB/browser
# records and all current owner/source bytes are checked by original gates.
old,after,report,outputs=m.prepare()
assert old==(m.PUB/'_config.yml').read_bytes() and report['excluded_count']==124 and report['selected_sources']==1175 and report['theorem_exports']==9644 and report['new_kernel_replays']==8 and report['reused_identical_sources']==1167
assert report['helper']=={'file':N,'sha256':sha(P)} and len(report['new_literal_exclusions'])==8 and report['screenshot_downloads']==48
assert set(outputs)=={m.REPORT,m.BACKUP,m.BACKUP_RECORD};assert outputs[m.BACKUP]==old
assert report['prospective_included_website_bytes_including_native_records']==report['prospective_included_website_bytes_before_new_native_records']+sum(map(len,outputs.values()))<m.BUDGET
for d in [R,m.PUB]:
 for n in outputs:assert not (d/n).exists()
assert sha(m.PUB/'_config.yml')==config_before
# Independently count INCLUDED ordinary bytes using pruned os.walk. Excluded
# symlinks are ignored before inspection; all included symlinks remain rejected.
count=0;ignored=[]
for root,dirs,files in os.walk(m.PUB,followlinks=False):
 here=Path(root)
 for dn in list(dirs):
  q=here/dn;n=q.relative_to(m.PUB).as_posix()
  if '.git' in q.relative_to(m.PUB).parts or not m.kept(n,set(report['exclusions'])):
   if q.is_symlink():ignored.append(n)
   dirs.remove(dn);continue
  assert not q.is_symlink(),n
 for fn in files:
  q=here/fn;n=q.relative_to(m.PUB).as_posix()
  if not m.kept(n,set(report['exclusions'])):
   if q.is_symlink():ignored.append(n)
   continue
  assert not q.is_symlink(),n;count+=q.stat().st_size
assert count==m.included_tree_bytes(m.PUB,set(report['exclusions']))
assert count-len(old)+len(after)==report['prospective_included_website_bytes_before_new_native_records']
assert (m.PUB/'verification/lean/.lake/packages').is_symlink() and not m.kept('verification/lean/.lake/packages',set(report['exclusions']))
for n,h in protected.items():assert sha(R/n)==h,n
closed={n:sha(R/n) for n in protected};closed[failure['log']]=sha(R/failure['log'])
for n in ['reports/full-coverage/checkpoint-27-manifest.json','reports/full-coverage/checkpoint-27-selection.json','reports/full-coverage/lean-checkpoint-27/verification-original.json','reports/full-coverage/verify-checkpoint27-execution-v1.json','reports/full-coverage/export-checkpoint27-execution-v1.json','reports/full-coverage/prepare-publication27-execution-v1.json']:closed[n]=sha(R/n)
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':N,'sha256':sha(P)},'helper_sha256':sha(P),'original_code_review':{'file':PR,'sha256':sha(R/PR)},'entire_original_code_review_body_and_time':prior,'entire_helper3_restored_by_exact_reviewed_delta':True,'actual_original_helper3_failure':{'file':failn,'sha256':sha(R/failn)},'entire_original_failure_body_and_time':failure,'original_failure_finding':{'file':findn,'sha256':sha(R/findn)},'entire_original_finding_body_and_time':finding,'reused_prior_full_code_fixture_count':prior['fixture_count'],'fresh_fixtures':fixtures,'fresh_fixture_count':len(fixtures),'real_native_readonly_prepare_passed':True,'real_native_projected_website_bytes_including_native_records':report['prospective_included_website_bytes_including_native_records'],'real_native_report_preview':report,'independent_existing_included_bytes':count,'original_publication_configuration_unchanged_sha256':config_before,'required_literal_exclusions':124,'selected_sources':1175,'public_theorems':9644,'website_budget_bytes':m.BUDGET,'closed_evidence_sha256':closed,'fixture_directory':str(base),'actual_producer_execution_claimed':False,'scope':'Independent full helper4 source read and exact helper3 delta; prior full-code39 fixtures preserved unchanged,10 fresh included/excluded symlink/count guards tested, complete REAL native prepare and independent included-byte count passed without writes to Root/PUB/config/native outputs. Original actual producer failure retained unchanged. Real --apply remains Root controlled.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'result':str(OUT),'sha256':sha(OUT),'fresh_fixtures':len(fixtures),'website_bytes':result['real_native_projected_website_bytes_including_native_records']}))
