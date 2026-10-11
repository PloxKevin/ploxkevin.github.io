"""Independent read-only actual Pages26 config output reader; no producer execution."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo';CACHE={}
def H(n):
 p=Path(n) if isinstance(n,Path) else R/n
 if p not in CACHE:CACHE[p]=hashlib.sha256(p.read_bytes()).hexdigest()
 return CACHE[p]
def J(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':H(n)}
def checked(v):
 assert isinstance(v,dict)and set(v)=={'file','sha256'}and H(v['file'])==v['sha256'];return J(v['file'])
def zero(d):
 v=[d[k]for k in ('actual_exit_code','exit_code')if k in d];assert v and all(type(c)is int and c==0 for c in v)
def actual(n):
 d=J(n);zero(d);assert H(d['log'])==d['log_sha256'];assert d['helper_sha256_before']==d['helper_sha256_after']
 for file,digest in d['helper_sha256_after'].items():assert H(file)==digest
 return d
HELP='book/coverage/checks/root_prepare_pages26_config_v3.py';HS='30d7f41eb587b915230eaa272efd44355b6a1965864ec71624ae295c2c03b50f';PEER='book/coverage/checks/pages26-config-helper-independent-modules-review-v3.json';PS='ba14cfd9e211a4a47011ac2fc80974d56e439c2b631de7151eeb003ae08eebb0'
assert H(HELP)==HS and H(PEER)==PS
code=J(PEER);assert 'passed' in code['status']and code['errors']==[]and code['helper_sha256']==HS
NATIVE='reports/full-coverage/pages26-config-preparation-v1.json';ACTUAL='reports/full-coverage/pages26-config-execution-v1.json';BACKUP='reports/full-coverage/pages26-config-previous-original-v1.yml';BREC='reports/full-coverage/pages26-config-previous-original-v1.json'
report=J(NATIVE);execution=actual(ACTUAL);assert execution['actual_command']==['python3',HELP] and execution['helper_sha256_after']=={HELP:HS}
assert report['status']=='passed_exact_pages26_archival_configuration_preparation_requires_actual_pages_build'
assert report['helper']==ref(HELP)and report['coverage_complete']is False
BEFORE='7cbf6c4a7aa5c2f349b83025018e6a27898e567e1822f3aeab4d064fbfecb0af'
assert H(BACKUP)==BEFORE and report['previous_configuration']=={'file':BACKUP,'sha256':BEFORE}
backup=J(BREC);assert backup=={'status':'previous_exact_pages_configuration_preserved','original_publication_path':'_config.yml','original_sha256':BEFORE,'immutable_original_byte_copy':BACKUP}
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
old=(R/BACKUP).read_text();oldexclude={l[4:]for l in old.splitlines()if l.startswith('  - ')};assert len(oldexclude)==101 and old==header+''.join('  - '+n+'\n'for n in sorted(oldexclude))
added={'reports/full-coverage/lean-checkpoint-24','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json','reports/full-coverage/checkpoint-25-manifest.json','reports/full-coverage/checkpoint-25-selection.json','book/coverage/inventory-after-correction53.json','book/coverage/inventory-before-correction53.json','reports/full-coverage/checkpoint-26','reports/full-coverage/owner25-originals-before-owner26-integration-v1'}
SCREEN_DIRS={'reports/full-coverage/browser-artifacts-'+str(i)for i in range(19,25)}
added|=SCREEN_DIRS
assert set(report['new_literal_exclusions'])==added and not added&oldexclude
exclusions=oldexclude|added;assert len(exclusions)==report['excluded_count']==116 and sorted(exclusions)==report['exclusions']
assert all(n and not Path(n).is_absolute()and '..'not in Path(n).parts and not any(c in n for c in '*?[{')for n in exclusions)
after=(header+''.join('  - '+n+'\n'for n in sorted(exclusions))).encode();assert (P/'_config.yml').read_bytes()==after and H(P/'_config.yml')==report['config_sha256']
kept=lambda n:not any(n==e or n.startswith(e+'/')for e in exclusions)
manifest=J('reports/full-coverage/checkpoint-26-manifest.json');selection=J('reports/full-coverage/checkpoint-26-selection.json');audit=J('reports/full-coverage/lean-checkpoint-26/verification-original.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'and manifest['selection_sha256']==H('reports/full-coverage/checkpoint-26-selection.json')
assert manifest['proof_files']==selection['proof_files']and len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1167
assert selection['new_file_count']==11 and audit['status']=='passed'and audit['theorem_count']==9503
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
assert all(type(c['exit_code'])is int and c['exit_code']==0 for c in audit['checks'])
assert sum(c.get('evidence_mode')=='fresh_kernel_replay'for c in audit['checks'])==11
assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports'for c in audit['checks'])==1156
for stem in ('verify-checkpoint26','export-checkpoint26','prepare-publication26'):actual('reports/full-coverage/'+stem+'-execution-v1.json')
for n,row in selection['proof_files'].items():assert H(n)==row['sha256']
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31 and assets['SafeLearning/lyapunov-mpc.html']=='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
required=dict(assets);working={};published={}
for n,h in assets.items():assert H(n)==H(P/n)==h
for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json'):
 h=manifest['frozen_inputs_sha256'][n];assert H(n)==H(P/n)==H(manifest['snapshot']+'/'+n)==h;required[n]=h
assert required['book/coverage/inventory.json']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
prior=J('reports/full-coverage/checkpoint-25-manifest.json')
for owner in ('core','foundations','applied','modules'):
 n='book/coverage/'+owner+'.json';working[n]=manifest['working_inputs_sha256'][n];published[n]=manifest['frozen_inputs_sha256'][n]
 assert H(n)==working[n]and H(P/n)==H(manifest['snapshot']+'/'+n)==published[n]
 normalized=copy.deepcopy(J(n));removed=manifest['excluded_unreferenced_ledger_metadata'][owner];assert removed==prior['excluded_unreferenced_ledger_metadata'][owner]and len(removed)==(3 if owner=='applied'else 0)
 for source in removed:assert source in normalized['proof_files']and source not in manifest['proof_files'];normalized['proof_files'].pop(source)
 assert normalized==json.loads((P/n).read_text());required[n]=published[n]
for n in ('reports/full-coverage/integration-26.json','reports/full-coverage/browser-checkpoint-26.json','reports/full-coverage/checkpoint-26-manifest.json','reports/full-coverage/checkpoint-26-selection.json','reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/lean-checkpoint-26/verification.json','reports/full-coverage/lean-checkpoint-26/ledger-audit.json','reports/full-coverage/lean-checkpoint-25/verification-original.json'):
 assert H(n)==H(P/n);required[n]=H(P/n)
inputs=J('reports/full-coverage/browser-corrections-26-inputs.json');assert len(inputs['screenshot_aliases'])==48
for row in inputs['screenshot_aliases']:
 n,h=row['file'],row['sha256'];assert n.startswith('reports/full-coverage/browser-artifacts-26/')and H(n)==H(P/n)==h and kept(n);required[n]=h
assert report['required_publication_files_sha256']==required and report['working_ledger_sha256']==working and report['published_frozen_ledger_sha256']==published
assert all(kept(n)for n in required)and report['exact_original_metadata_removals']==manifest['excluded_unreferenced_ledger_metadata']
retired_dir='reports/full-coverage/lean-checkpoint-24';retired={p.relative_to(R).as_posix():H(p)for p in (R/retired_dir).rglob('*')if p.is_file()}
assert retired and {p.relative_to(P).as_posix():H(p)for p in (P/retired_dir).rglob('*')if p.is_file()}==retired
files={'reports/full-coverage/checkpoint-24-manifest.json':'5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0','reports/full-coverage/checkpoint-24-selection.json':'9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314','reports/full-coverage/checkpoint-25-manifest.json':'0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363','reports/full-coverage/checkpoint-25-selection.json':'3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'}
for name,group in [(retired_dir,retired)]+[(n,{n:h})for n,h in files.items()]:
 output=subprocess.run(['git','ls-files','-z','--',name],cwd=P,check=True,capture_output=True);assert {n for n in output.stdout.decode().split('\0')if n}==set(group)
 subprocess.run(['git','diff','--quiet','HEAD','--',name],cwd=P,check=True)
 for n,h in group.items():assert H(n)==H(P/n)==h and not kept(n)
assert report['retired_older_audit_file_count']==len(retired) and report['retired_older_audit_sorted_exact_path_sha256_map_fingerprint']==hashlib.sha256(json.dumps(retired,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert report['retired_older_manifest_selection_exact_sha256']==files
assert report['retired_baseline25_direct_archives_exact_bytes']=={'reports/full-coverage/checkpoint-25-manifest.json':56004385,'reports/full-coverage/checkpoint-25-selection.json':41605130}
assert sum((R/n).stat().st_size for n in files if 'checkpoint-25-'in n)==97609515
ARC='book/coverage/checks/future26-core/pages26-six-older-screenshot-archives-readonly-observation-v1.json';BUD='book/coverage/checks/future26-core/pages26-real-prepared-budget-original-v1.json'
assert H(ARC)=='d06fcb35ef030e2ef97c530777ea0d6dce21f755ae12e6d77e775028841b8ed7'and H(BUD)=='84b9040cbbd42cc071aaffc2167d4e91a6d087a3d7bc5fc6f63cc224b2ef12b5'
archive=J(ARC);screens={};size=0
assert set(archive['archival_directories'])==SCREEN_DIRS
for d in sorted(SCREEN_DIRS):
 a=archive['archival_directories'][d];m=a['exact_files_sha256'];assert len(m)==a['file_count']==48
 for base in (R,P):
  paths=list((base/d).rglob('*'));assert not any(p.is_symlink()for p in paths)
  assert {p.relative_to(base).as_posix():H(p)for p in paths if p.is_file()}==m
 subprocess.run(['git','diff','--quiet','HEAD','--',d],cwd=P,check=True)
 tracked=subprocess.run(['git','ls-files','-z','--',d],cwd=P,check=True,capture_output=True);assert {n for n in tracked.stdout.decode().split('\0')if n}==set(m)
 assert all(not kept(n)for n in m)and hashlib.sha256(json.dumps(m,sort_keys=True,separators=(',',':')).encode()).hexdigest()==a['sorted_exact_path_sha256_map_fingerprint']
 b=sum((R/n).stat().st_size for n in m);assert b==a['byte_count']==sum((P/n).stat().st_size for n in m);size+=b;screens.update(m)
assert len(screens)==archive['total_files']==report['retired_older_screenshot_file_count']==288
assert size==archive['total_bytes']==report['retired_older_screenshot_archive_bytes']==169960594
assert report['retired_older_screenshot_directories']==sorted(SCREEN_DIRS)and report['retired_older_screenshot_sorted_exact_path_sha256_map_fingerprint']==hashlib.sha256(json.dumps(screens,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert report['current26_screenshot_aliases48_remain_public_exact']is True
assert report['exact_older_screenshot_archive_observation']==ref(ARC)and report['original_real_prepared_budget_observation']==ref(BUD)
assert report['original_unexecuted_config2_helper']==ref('book/coverage/checks/root_prepare_pages26_config_v2.py')and report['original_config2_independent_code_review']==ref('book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json')
for d in ('reports/full-coverage/browser-artifacts-25','reports/full-coverage/browser-artifacts-source53-26-v1'):assert kept(d+'/example.png')
included=sum(p.stat().st_size for p in P.rglob('*')if p.is_file()and '.git'not in p.relative_to(P).parts and kept(p.relative_to(P).as_posix()))
assert included==report['prospective_included_website_bytes_before_new_native_records']<report['website_budget_bytes']==850000000
out={'status':'passed_independent_actual_pages26_configuration_output_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'config_sha256':report['config_sha256'],'excluded_count':116,'selected_sources':1167,'public_theorems':9503,'native_configuration_report':ref(NATIVE),'actual_configuration_execution':ref(ACTUAL),'actual_configuration_raw_log':ref(execution['log']),'configuration_helper':ref(HELP),'independent_configuration_code_peer':ref(PEER),'original_configuration_byte_copy':ref(BACKUP),'required_publication_files_sha256':required,'working_ledger_sha256':working,'published_frozen_ledger_sha256':published,'actual_current_included_website_bytes':included,'website_budget_bytes':850000000,'four_retired_direct_archives_preserved_root_publication_tracked_HEAD':files,'entire_native_configuration_report_body_and_time':report,'exact_288_retired_original_screenshot_hashes':screens,'retired_screenshot_archive_bytes':size,'all48_current26_screenshots_exact_and_public':True,'original_real_prepared_budget_observation':ref(BUD),'exact_older_screenshot_archive_observation':ref(ARC),'unexecuted_prior_output_checker':{'file':'/tmp/check-pages26-config-independent-output-modules-v2.py','sha256':H(Path('/tmp/check-pages26-config-independent-output-modules-v2.py')),'executed':False},'coverage_complete':False,'scope':'Independent read of genuine configuration-only producer success. Current26/baseline25 audits,31 assets/current53/current owners remain included; older Git archives remain exact. Original command/time/status and pruning scope are preserved. No actual Pages build/deployment/live result or full coverage is inferred.'}
p=Path('/tmp/pages26-config-independent-modules-output-v3.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(p),'sha256':H(p),'config_sha256':report['config_sha256'],'included_bytes':included}))
