"""Stage a concrete audited27 publication through exact explicit path bindings.

Code review/preparation imply no commit, push, Pages build, or live success.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse,copy,hashlib,json,shutil,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_stage_publication27_v5.py'
REPORT='reports/full-coverage/publication27-prestage-v1.json';BUDGET=850000000
MANIFEST='reports/full-coverage/checkpoint-27-manifest.json';SELECTION='reports/full-coverage/checkpoint-27-selection.json'
AUDIT='reports/full-coverage/lean-checkpoint-27/verification-original.json'
EXPECTED_SELECTION='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,n):
 assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 assert not any(c in n for c in '\0\n\r*?[')
 p=root/n;assert p.resolve().is_relative_to(root.resolve()) and not p.is_symlink();return p

def read(n):return json.loads(safe(ROOT,n).read_bytes())
def zero(d):
 values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
 assert values and all(type(v) is int and v==0 for v in values)
def actual(n,command):
 d=read(n);zero(d);assert d['status']=='passed'
 cmds=[d[k] for k in ('actual_command','command') if k in d]
 work=[d[k] for k in ('actual_workdir','working_directory','cwd') if k in d]
 assert cmds and all(v==command for v in cmds)
 assert work and all(v==str(ROOT) for v in work)
 for k in ('log','raw_log'):
  if k in d:assert d[k]==d['log']
 for k in ('log_sha256','raw_log_sha256'):
  if k in d:assert d[k]==d['log_sha256']
 assert type(d['helper_sha256_before']) is dict and type(d['helper_sha256_after']) is dict
 assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']
 assert command[1] in d['helper_sha256_after']
 assert sha(safe(ROOT,d['log']))==d['log_sha256']
 for p,h in d['helper_sha256_after'].items():assert sha(safe(ROOT,p))==h
 return d

REQUIRED_EXECUTIONS={
'reports/full-coverage/pages27-supplemental-archive-configuration-execution-v1.json':['python3','book/coverage/checks/root_prepare_pages27_supplemental_archives_v2.py','--apply'],
'reports/full-coverage/prepare-checkpoint27-selection-execution-v1.json':['python3','book/coverage/prepare_checkpoint27_selection_v2.py','--plan','book/coverage/checks/future27-core/checkpoint27-installed-owner-selection-plan-v2.json','--apply'],
'reports/full-coverage/freeze-checkpoint27-execution-v1.json':['python3','book/coverage/freeze_checkpoint27_v2.py','--selection',SELECTION,'--snapshot','reports/full-coverage/checkpoint-27','--selection-sha256',EXPECTED_SELECTION],
'reports/full-coverage/prepare-checkpoint27-cache-execution-v1.json':['python3','book/coverage/checks/root_prepare_checkpoint27_cache_v1.py'],
'reports/full-coverage/verify-checkpoint27-execution-v1.json':['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/checkpoint-26')],
'reports/full-coverage/export-checkpoint27-execution-v1.json':['python3','book/coverage/export_audit27_v3.py','--snapshot','reports/full-coverage/checkpoint-27','--output','reports/full-coverage/lean-checkpoint-27'],
'reports/full-coverage/export-integrity-checkpoint27-execution-v1.json':['python3','book/coverage/checks/root_check_export27_integrity_v1.py'],
'reports/full-coverage/frozen-ledger-checkpoint27-execution-v1.json':['python3','reports/full-coverage/checkpoint-27/book/coverage/validate.py','--output','reports/full-coverage/lean-checkpoint-27/ledger-audit.json'],
'reports/full-coverage/static-checkpoint27-execution-v1.json':['python3','book/validate.py','--allow-reviewed-corrections','--output','reports/full-coverage/integration-27.json'],
'reports/full-coverage/prepare-documentation27-execution-v1.json':['python3','book/coverage/checks/root_prepare_checkpoint27_documentation_v6.py'],
'reports/full-coverage/prepare-publication27-execution-v1.json':['python3','book/coverage/prepare_publication.py','27'],
'reports/full-coverage/publication27-ledger-check-execution-v1.json':['python3','reports/book/publication-repo/book/coverage/validate.py','--output','reports/full-coverage/publication-checks/ledger-checkpoint-27.json'],
'reports/full-coverage/pages27-config-execution-v2.json':['python3','book/coverage/checks/root_prepare_pages27_config_v5.py','--apply'],
'reports/full-coverage/root-source55-final-owner-integration27-execution-v1.json':['python3','book/coverage/validate.py','--output','reports/full-coverage/root-source55-final-owner-integration27-v1.json'],
'reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json':['python3','book/coverage/checks/root_integrate_owner27_candidates_v2.py','book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json','--apply'],
'reports/full-coverage/prepare-browser27-execution-v1.json':['python3','book/coverage/checks/root_prepare_browser27_v1.py'],
'reports/full-coverage/browser-source55-checkpoint27-execution-v1.json':['python3','book/coverage/checks/root_browser_source55_run27_v1.py'],
'reports/full-coverage/publication27-browser-original-copy-execution-v2.json':['python3','book/coverage/checks/root_copy_browser27_originals_for_publication_v2.py'],
}
def closed_peer(name,status,aliases,expected,prepared,working):
 peer=read(name);assert peer['status']==status and peer['errors']==[]
 closed=peer['closed_evidence_sha256'];assert type(closed) is dict and closed
 for original,h in closed.items():
  if Path(original).is_absolute():
   row=aliases[original+'::'+h];assert row['sha256']==h;n=row['file']
  else:n=original
  assert sha(safe(ROOT,n))==h,n
  if expected.get(n)==h:continue
  if n in prepared and sha(safe(PUB,n))==h:continue
  # The current raw Applied owner is retained separately from its reviewed
  # published metadata pruning. It must never overwrite the publication owner.
  assert original==n=='book/coverage/applied.json' and working[n]==h,n
  row=aliases[original+'::'+h];retained=row['file']
  assert row['sha256']==h and retained!=n and sha(safe(ROOT,retained))==h
  assert expected.get(retained)==h or (retained in prepared and sha(safe(PUB,retained))==h)
 return peer

def dirty():
 raw=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout
 result=set()
 for row in filter(None,raw.decode().split('\0')):
  assert len(row)>=4 and row[:2] not in ('R ',' R','C ',' C') and 'D' not in row[:2],row
  result.add(row[3:])
 return result

def staged():return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.split(b'\0') if n}
def prepare(plan_name):
 assert Path(__file__).resolve()==ROOT/SELF
 assert not safe(ROOT,REPORT).exists() and not safe(PUB,REPORT).exists()
 plan=read(plan_name);assert plan['status']=='root_explicit_audited27_publication_stage_inputs'
 assert plan['helper']=={'file':SELF,'sha256':sha(ROOT/SELF)} and plan['coverage_complete'] is False
 pr=plan['independent_helper_review'];assert sha(safe(ROOT,pr['file']))==pr['sha256'];peer=read(pr['file'])
 assert peer['status']=='passed_independent_checkpoint27_publication_stager_full_code_review' and peer['errors']==[]
 assert peer['helper_sha256']==sha(ROOT/SELF)
 manifest,selection,audit=map(read,(MANIFEST,SELECTION,AUDIT))
 assert sha(safe(ROOT,SELECTION))==EXPECTED_SELECTION==manifest['selection_sha256']
 assert manifest['snapshot']=='reports/full-coverage/checkpoint-27' and manifest['status']=='formal_verification_passed_partial_coverage'
 assert manifest['proof_files']==selection['proof_files'] and len(selection['proof_files'])==selection['proof_file_count']==1175 and selection['new_file_count']==8
 assert selection['coverage_complete'] is False and audit['status']=='passed'
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()} and audit['proof_file_count']==1175
 assert audit['theorem_count']==len(audit['declarations'])==len(audit['axiom_dependencies'])==9644
 assert {r['name'] for r in audit['declarations']}==set(audit['axiom_dependencies'])
 assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert all(set(v)<=set(audit['allowed_standard_axioms']) for v in audit['axiom_dependencies'].values())
 assert audit['checks']
 for r in audit['checks']:zero(r)
 assert sum(r.get('evidence_mode')=='fresh_kernel_replay' for r in audit['checks'])==8
 assert sum(r.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for r in audit['checks'])==1167
 assert manifest['successful_verification']['report']==AUDIT and manifest['successful_verification']['report_sha256']==sha(safe(ROOT,AUDIT))
 frozen=manifest['frozen_inputs_sha256'];prepared_name='reports/full-coverage/publication-prepared-27-files.json';prepared=read(prepared_name)
 assert type(prepared) is list and prepared and len(prepared)==len(set(prepared))
 for n in prepared:safe(PUB,n)
 assert plan['prepared_file_list']=={'file':prepared_name,'sha256':sha(safe(ROOT,prepared_name))}
 paths=set(prepared);derived=set(frozen)
 derived.update('reports/full-coverage/checkpoint-27/'+n for n in frozen if n.startswith('reports/full-coverage/source-history/'))
 external=['reports/full-coverage/README.md','reports/full-coverage/integration-27.json',MANIFEST,SELECTION,'reports/full-coverage/checkpoint-27-ledger-manifest.json','reports/full-coverage/browser-checkpoint-27.json','reports/full-coverage/browser-corrections-27-inputs.json','reports/full-coverage/browser-corrections-27.json','reports/full-coverage/browser-corrections-27.log']
 external += [p.relative_to(ROOT).as_posix() for directory in ('reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-27') for p in safe(ROOT,directory).glob('*') if p.is_file()]
 derived.update(n for n in external if safe(ROOT,n).is_file())
 assert paths==derived,'prepared file list differs from the actual preparation source enumeration'
 expected=dict(plan['supplemental_inputs_sha256']);assert expected and all(type(h) is str and len(h)==64 for h in expected.values())
 assert '_config.yml' not in expected
 assert not any(n.startswith(('verification/lean/','SafeLearning/')) for n in expected)
 for n,h in expected.items():
  safe(ROOT,n);safe(PUB,n)
  if n in frozen and n not in {'book/coverage/progress.json','reports/full-coverage/README.md'}:assert h==frozen[n],n
 assert not set(expected)&{'book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json','book/coverage/material-corrections.json'}
 assert SELF in expected and plan_name not in expected
 expected[plan_name]=sha(safe(ROOT,plan_name));expected[pr['file']]=pr['sha256']
 overrides={'book/coverage/progress.json','reports/full-coverage/README.md'}
 assert overrides<=set(expected)
 for n,h in frozen.items():
  assert sha(safe(ROOT,manifest['snapshot']+'/'+n))==h,n
  assert safe(PUB,n).is_file(),n
  if n not in overrides:assert sha(safe(PUB,n))==h,n
 for n,r in selection['proof_files'].items():assert sha(safe(ROOT,n))==sha(safe(PUB,n))==r['sha256'],n
 assets={n:h for n,h in frozen.items() if n.startswith('SafeLearning/')};assert len(assets)==31
 for n,h in assets.items():assert sha(safe(ROOT,n))==sha(safe(PUB,n))==h
 assert frozen['book/coverage/inventory.json']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
 assert frozen['book/coverage/material-corrections.json']=='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
 prior=read('reports/full-coverage/checkpoint-26-manifest.json')
 assert len(prior['proof_files'])==1167 and set(prior['proof_files'])<=set(manifest['proof_files'])
 assert all(manifest['proof_files'][n]['sha256']==r['sha256'] for n,r in prior['proof_files'].items())
 for owner in ('core','foundations','applied','modules'):
  n='book/coverage/'+owner+'.json';assert sha(safe(ROOT,n))==manifest['working_inputs_sha256'][n]
  removed=manifest['excluded_unreferenced_ledger_metadata'][owner]
  assert removed==prior['excluded_unreferenced_ledger_metadata'][owner] and len(removed)==(3 if owner=='applied' else 0)
  body=copy.deepcopy(read(n))
  for source in removed:assert source not in manifest['proof_files'];body['proof_files'].pop(source)
  assert body==json.loads(safe(PUB,n).read_bytes())
 content_ref=selection['previous_frozen_input_content_binding'];assert sha(safe(ROOT,content_ref['file']))==content_ref['sha256']
 bindings=read(content_ref['file']);rows=bindings['input_bindings'];assert bindings['original_input_count']==len(rows)==47277
 assert {r['original_frozen_path']:r['sha256'] for r in rows}==prior['frozen_inputs_sha256']
 for r in rows:
  n=r['retained_input'];assert n in paths and sha(safe(ROOT,n))==sha(safe(PUB,n))==r['sha256'],n
 ledgern='reports/full-coverage/publication-checks/ledger-checkpoint-27.json';ledger=read(ledgern)
 assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
 assert ledger['inventory_sha256']==frozen['book/coverage/inventory.json']
 for row in ledger['domains']:assert row['ledger_sha256']==sha(safe(PUB,'book/coverage/'+row['domain']+'.json'))
 base_config=read('reports/full-coverage/pages27-config-preparation-v1.json')
 config=read('reports/full-coverage/pages27-supplemental-archive-configuration-v1.json')
 assert base_config['status']=='passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build' and base_config['excluded_count']==129
 assert base_config['config_sha256']=='37afb173e76aee80569b4903ca88b39c5e12d4729a65627f447d2060842db1ea'
 assert config['status']=='passed_exact_checkpoint27_supplemental_archive_configuration_requires_actual_stage_and_pages'
 assert config['previous_configuration_report']=={'file':'reports/full-coverage/pages27-config-preparation-v1.json','sha256':sha(ROOT/'reports/full-coverage/pages27-config-preparation-v1.json')}
 assert config['previous_configuration']['sha256']==base_config['config_sha256']==sha(safe(ROOT,config['previous_configuration']['file']))
 added={'book/coverage/checks/future27-core/original-documentation27-foundations-review-v1','book/coverage/checks/future27-core/original-pages27-config5-actual-output-independent-modules-v2','reports/full-coverage/working-inventory55-timestamp-regeneration-before-restoration28-v1.json',REPORT}
 assert set(config['exclusions'])==set(base_config['exclusions'])|added and config['new_literal_exclusions']==sorted(added)
 assert config['required_publication_files_sha256']==base_config['required_publication_files_sha256'] and config['required_download_count']==1284
 assert config['status']=='passed_exact_checkpoint27_supplemental_archive_configuration_requires_actual_stage_and_pages' and config['coverage_complete'] is False
 exclusions=config['exclusions'];assert len(exclusions)==len(set(exclusions))==config['excluded_count']==133
 for n in exclusions:safe(ROOT,n)
 assert config['website_budget_bytes']==BUDGET and sha(safe(PUB,'_config.yml'))==config['config_sha256']
 for n,h in config['required_publication_files_sha256'].items():assert sha(safe(PUB,n))==h
 aliases=plan['original_byte_aliases'];assert type(aliases) is dict
 config_peer=closed_peer('book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json','passed_independent_actual_checkpoint27_pages_configuration',aliases,expected,paths,manifest['working_inputs_sha256'])
 assert config_peer['helper']==base_config['helper'] and config_peer['config_sha256']==base_config['config_sha256'] and config_peer['excluded_count']==129
 assert base_config['helper']=={'file':'book/coverage/checks/root_prepare_pages27_config_v5.py','sha256':'d7e2a4764f4678d6e7dc7c6443a732fc60224b733633db3a1646628801ebd101'}
 assert config['helper']=={'file':'book/coverage/checks/root_prepare_pages27_supplemental_archives_v2.py','sha256':'97472d2120970e89a97cdab394ab9e5c6d6f3e67b8081adfe30e5f7507891191'}
 supplemental_peer=closed_peer('book/coverage/checks/future27-core/pages27-supplemental-archives-independent-modules-output-v1.json','passed_independent_actual_checkpoint27_supplemental_archive_configuration',aliases,expected,paths,manifest['working_inputs_sha256'])
 assert supplemental_peer['helper']==config['helper'] and supplemental_peer['config_sha256']==config['config_sha256'] and supplemental_peer['excluded_count']==133
 production_peer_name='book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json'
 assert sha(safe(ROOT,production_peer_name))=='d2d887d743e2760825e765580bbb0f12f83829636b6e9696e40abe33cc2830c8'
 production_peer=closed_peer(production_peer_name,'passed',aliases,expected,paths,manifest['working_inputs_sha256'])
 assert production_peer['selection']=={'file':SELECTION,'sha256':EXPECTED_SELECTION}
 assert (production_peer['proof_files'],production_peer['new_sources'],production_peer['public_theorem_or_lemma_exports'],production_peer['old_frozen_paths_retained_exact'])==(1175,8,9644,47277)
 assert production_peer['all_claim_declarations_selected'] is True and production_peer['coverage_complete'] is False
 assert production_peer['actual_aggregate_or_publication_claim'] is False
 doc=read('reports/full-coverage/progress-checkpoint27-preparation-update-v2.json')
 for key in ('current_progress','current_readme'):
  r=doc[key];assert sha(safe(ROOT,r['file']))==r['sha256']==expected[r['file']]
 progress=read('book/coverage/progress.json')
 assert progress['verified_checkpoint']['proof_files']==1175 and progress['verified_checkpoint']['theorems']==9644
 assert progress['verified_checkpoint']['coverage_complete'] is False and progress['current_documented_material_corrections']==55
 assert progress['live_delivery_status']=='checkpoint27_awaiting_actual_pages_and_live_checks' and progress['live_delivery_evidence'] is None
 assert set(plan['actual_execution_records'])==set(REQUIRED_EXECUTIONS)
 assert len(plan['actual_execution_records'])==len(REQUIRED_EXECUTIONS)
 for n,command in REQUIRED_EXECUTIONS.items():
  d=actual(n,command);assert n in expected and d['log'] in expected
  assert expected[n]==sha(safe(ROOT,n)) and expected[d['log']]==d['log_sha256']
 browser=read('reports/full-coverage/browser-checkpoint-27.json')
 assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['source_sha256']==assets
 assert (browser['page_count'],browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'],browser['screenshot_count'])==(29,145,10,135,48)
 for n,h in expected.items():assert sha(safe(ROOT,n))==h,n
 paths.update(expected);paths.update(('_config.yml',REPORT))
 for n in paths:safe(PUB,n)
 assert dirty()<=paths and staged()<=paths,sorted(dirty()-paths)
 kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
 included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
 delta=sum(safe(ROOT,n).stat().st_size-(safe(PUB,n).stat().st_size if safe(PUB,n).is_file() else 0) for n in expected if kept(n))
 record={'status':'passed_explicit_audited_checkpoint27_publication_whitelist_ready_to_stage','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(ROOT/SELF),'selection_sha256':EXPECTED_SELECTION,'manifest_sha256':sha(ROOT/MANIFEST),'sources':1175,'public_theorems':9644,'new_sources':8,'current55_assets_sha256':assets,'config_sha256':config['config_sha256'],'staged_paths':sorted(paths),'additional_closed_paths_sha256':expected,'actual_execution_records':plan['actual_execution_records'],'coverage_complete':False,'included_website_bytes_before_copy':included,'closed_replacement_byte_delta':delta,'publication_still_awaits_actual_commit_push_pages_and_live_checks':True}
 payload=(json.dumps(record,separators=(',',':'))+'\n').encode();assert 0<=included+delta+(len(payload) if kept(REPORT) else 0)<BUDGET
 return paths,expected,payload,config['config_sha256']

def main():
 p=argparse.ArgumentParser();p.add_argument('--plan',required=True);args=p.parse_args()
 paths,expected,payload,config_sha=prepare(args.plan)
 for n,h in expected.items():
  destination=safe(PUB,n);destination.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(ROOT,n),destination);assert sha(destination)==h
 with safe(ROOT,REPORT).open('xb') as f:f.write(payload)
 shutil.copyfile(safe(ROOT,REPORT),safe(PUB,REPORT))
 assert dirty()<=paths and staged()<=paths
 assert sha(safe(PUB,'_config.yml'))==config_sha
 subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=b''.join(n.encode()+b'\0' for n in sorted(paths)),check=True)
 assert staged() and staged()<=paths
 for n,h in expected.items():assert sha(safe(PUB,n))==h
 subprocess.run(['git','diff','--cached','--check'],cwd=PUB,check=True)
 assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
 print(json.dumps({'status':'passed','actual_staged_paths':len(staged()),'explicit_allowed_paths':len(paths),'coverage_complete':False}))
if __name__=='__main__':main()
