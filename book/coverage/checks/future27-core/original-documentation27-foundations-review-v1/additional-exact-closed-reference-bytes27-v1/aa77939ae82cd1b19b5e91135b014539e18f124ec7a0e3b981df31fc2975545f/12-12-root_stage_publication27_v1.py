"""Stage a concrete audited27 publication through exact explicit path bindings.

Code review/preparation imply no commit, push, Pages build, or live success.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse,copy,hashlib,json,shutil,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_stage_publication27_v1.py'
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
def actual(n):
 d=read(n);zero(d);assert d['actual_workdir']==str(ROOT)
 assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']
 assert sha(safe(ROOT,d['log']))==d['log_sha256']
 for p,h in d['helper_sha256_after'].items():assert sha(safe(ROOT,p))==h
 return d

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
 assert audit['checks'] and all(type(r['exit_code']) is int and r['exit_code']==0 for r in audit['checks'])
 assert sum(r.get('evidence_mode')=='fresh_kernel_replay' for r in audit['checks'])==8
 assert sum(r.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for r in audit['checks'])==1167
 assert manifest['successful_verification']['report']==AUDIT and manifest['successful_verification']['report_sha256']==sha(safe(ROOT,AUDIT))
 frozen=manifest['frozen_inputs_sha256'];paths=set(read('reports/full-coverage/publication-prepared-27-files.json'))
 assert set(frozen)<=paths
 expected=dict(plan['supplemental_inputs_sha256']);assert expected and all(type(h) is str and len(h)==64 for h in expected.values())
 assert not any(n.startswith('verification/lean/') for n in expected)
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
 config=read('reports/full-coverage/pages27-config-preparation-v1.json')
 assert config['status']=='passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build' and config['coverage_complete'] is False
 exclusions=config['exclusions'];assert len(exclusions)==len(set(exclusions))==config['excluded_count']==124
 for n in exclusions:safe(ROOT,n)
 assert config['website_budget_bytes']==BUDGET and sha(safe(PUB,'_config.yml'))==config['config_sha256']
 for n,h in config['required_publication_files_sha256'].items():assert sha(safe(PUB,n))==h
 config_peer=read('book/coverage/checks/future27-core/pages27-config-independent-modules-output-v3.json')
 assert config_peer['errors']==[] and config_peer['config_sha256']==config['config_sha256'] and config_peer['excluded_count']==124
 doc=read('reports/full-coverage/progress-checkpoint27-preparation-update-v2.json')
 for key in ('current_progress','current_readme'):
  r=doc[key];assert sha(safe(ROOT,r['file']))==r['sha256']==expected[r['file']]
 progress=read('book/coverage/progress.json')
 assert progress['verified_checkpoint']['proof_files']==1175 and progress['verified_checkpoint']['theorems']==9644
 assert progress['verified_checkpoint']['coverage_complete'] is False and progress['current_documented_material_corrections']==55
 assert progress['live_delivery_status']=='checkpoint27_awaiting_actual_pages_and_live_checks'
 for n in plan['actual_execution_records']:
  d=actual(n);assert n in expected and d['log'] in expected
 browser=read('reports/full-coverage/browser-checkpoint-27.json')
 assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['source_sha256']==assets
 assert (browser['page_count'],browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'],browser['screenshot_count'])==(29,145,10,135,48)
 for n,h in expected.items():assert sha(safe(ROOT,n))==h,n
 paths.update(expected);paths.update(('_config.yml',REPORT))
 assert dirty()<=paths and staged()<=paths,sorted(dirty()-paths)
 kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
 included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
 delta=sum(safe(ROOT,n).stat().st_size-(safe(PUB,n).stat().st_size if safe(PUB,n).is_file() else 0) for n in expected if kept(n))
 record={'status':'passed_explicit_audited_checkpoint27_publication_whitelist_ready_to_stage','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(ROOT/SELF),'selection_sha256':EXPECTED_SELECTION,'manifest_sha256':sha(ROOT/MANIFEST),'sources':1175,'public_theorems':9644,'new_sources':8,'current55_assets_sha256':assets,'config_sha256':config['config_sha256'],'staged_paths':sorted(paths),'additional_closed_paths_sha256':expected,'actual_execution_records':plan['actual_execution_records'],'coverage_complete':False,'included_website_bytes_before_copy':included,'closed_replacement_byte_delta':delta,'publication_still_awaits_actual_commit_push_pages_and_live_checks':True}
 payload=(json.dumps(record,separators=(',',':'))+'\n').encode();assert 0<=included+delta+len(payload)<BUDGET
 return paths,expected,payload

def main():
 p=argparse.ArgumentParser();p.add_argument('--plan',required=True);args=p.parse_args()
 paths,expected,payload=prepare(args.plan)
 for n,h in expected.items():
  destination=safe(PUB,n);destination.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(ROOT,n),destination);assert sha(destination)==h
 with safe(ROOT,REPORT).open('xb') as f:f.write(payload)
 shutil.copyfile(safe(ROOT,REPORT),safe(PUB,REPORT))
 assert dirty()<=paths and staged()<=paths
 subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=b''.join(n.encode()+b'\0' for n in sorted(paths)),check=True)
 assert staged() and staged()<=paths
 for n,h in expected.items():assert sha(safe(PUB,n))==h
 subprocess.run(['git','diff','--cached','--check'],cwd=PUB,check=True)
 assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
 print(json.dumps({'status':'passed','actual_staged_paths':len(staged()),'explicit_allowed_paths':len(paths),'coverage_complete':False}))
if __name__=='__main__':main()
