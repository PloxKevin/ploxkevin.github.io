"""Keep exact checkpoint28 downloads while excluding literal Git audit archives."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_prepare_pages28_config_v5.py'
REPORT='reports/full-coverage/pages28-config-preparation-v1.json'
BACKUP='reports/full-coverage/pages28-config-previous-original-v1.yml'
BEFORE='cc1f0f9cf93b0d9ffdff6e422bfb6b85f073e4efb0d705378adc32a46a40af23'
HEAD='8fa808699674d13e4297d226ef1530a7ec744ad0'
HEADER='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
BUDGET=850000000
ADDITIONS={
 'reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source44-19-v2',
 'reports/full-coverage/checkpoint-28','reports/full-coverage/checkpoint-27-manifest.json','reports/full-coverage/checkpoint-27-selection.json',
 'reports/full-coverage/lean-checkpoint-26','reports/full-coverage/browser-artifacts-25',
 'reports/full-coverage/owner27-originals-before-owner28-integration-v1',
 'book/coverage/checks/future28-core','book/coverage/checks/future28-foundations',
 'book/coverage/checks/applied-future28','book/coverage/checks/modules-future28',
 *['book/coverage/inventory-'+side+'-correction'+str(i)+'.json' for i in range(56,61) for side in ['before','after']]}
def safe(root,n):
 assert type(n) is str and n and Path(n).as_posix()==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 assert not any(c in n for c in '\0\n\r*?[')
 p=root/n;assert p.resolve().is_relative_to(root) and not p.is_symlink();return p
def sha(root,n):return hashlib.sha256(safe(root,n).read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(ROOT,n)}
def read(root,n):return json.loads(safe(root,n).read_bytes())
def kept(n,exclusions):return not any(n==e or n.startswith(e+'/') for e in exclusions)
def encoded(d):return (json.dumps(d,ensure_ascii=False,separators=(',',':'))+'\n').encode()
def zero(d):
 codes=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d]
 assert codes and all(type(v) is int and v==0 for v in codes)
def audit_native(d):
 zero(d)
 assert 'status' not in d or d['status']=='passed'
 cmds=[d[k] for k in ['actual_command','command'] if k in d]
 assert cmds and all(type(c) is list and c==cmds[0] for c in cmds)
 cwds=[d[k] for k in ['actual_workdir','working_directory','workdir','cwd'] if k in d]
 assert all(type(v) is str and v==cwds[0] for v in cwds)
def native(d,command):
 assert d['status']=='passed';zero(d)
 cmds=[d[k] for k in ['actual_command','command'] if k in d];assert cmds and all(c==command for c in cmds)
 cwds=[d[k] for k in ['actual_workdir','working_directory','workdir','cwd'] if k in d];assert cwds and all(v==str(ROOT) for v in cwds)
 logs=[d[k] for k in ['log','raw_log'] if k in d];digests=[d[k] for k in ['log_sha256','raw_log_sha256'] if k in d]
 assert logs and digests and all(v==logs[0] for v in logs) and all(v==digests[0] for v in digests)
 assert sha(ROOT,logs[0])==digests[0]
def actual(n,command):
 d=read(ROOT,n);native(d,command)
 helpers={command[1]:sha(ROOT,command[1])}
 assert d['helper_sha256_before']==d['helper_sha256_after']==helpers
 return d
def prepare():
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PUB,text=True).strip()==HEAD
 assert sha(PUB,'_config.yml')==BEFORE
 original=safe(PUB,'_config.yml').read_bytes();old={line[4:] for line in original.decode().splitlines() if line.startswith('  - ')}
 assert len(old)==133 and original.decode()==HEADER+''.join('  - '+n+'\n' for n in sorted(old))
 assert len(ADDITIONS)==23 and not old&ADDITIONS
 exclusions=old|ADDITIONS
 for n in exclusions:safe(PUB,n)
 after=(HEADER+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode()
 manifest=read(ROOT,'reports/full-coverage/checkpoint-28-manifest.json');selection=read(ROOT,'reports/full-coverage/checkpoint-28-selection.json')
 audit=read(ROOT,'reports/full-coverage/lean-checkpoint-28/verification-original.json')
 assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['proof_files']==selection['proof_files']
 assert manifest['selection_sha256']==sha(ROOT,'reports/full-coverage/checkpoint-28-selection.json')
 assert len(selection['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1186 and selection['new_file_count']==11
 assert audit['status']=='passed' and audit['theorem_count']==len(audit['declarations'])==len(audit['axiom_dependencies'])==9896
 for c in audit['checks']:audit_native(c)
 names=[d['name'] for d in audit['declarations']]
 assert len(names)==len(set(names)) and set(names)==set(audit['axiom_dependencies'])
 success=manifest['successful_verification']
 assert success['report']=='reports/full-coverage/lean-checkpoint-28/verification-original.json' and success['report_sha256']==sha(ROOT,success['report'])
 assert success['proof_file_count']==1186 and success['theorem_count']==9896 and type(success['all_check_exit_codes']) is int and success['all_check_exit_codes']==0
 assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==11
 assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1175
 assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert all(set(a)<=set(audit['allowed_standard_axioms']) for a in audit['axiom_dependencies'].values())
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
 required={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
 assert len([n for n in required if n.startswith('SafeLearning/')])==31
 assert required['book/coverage/inventory.json']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
 archival={n:r['sha256'] for n,r in selection['proof_files'].items()}
 assert 'verification/lean' in old and len(archival)==1186
 for n,h in archival.items():
  assert n.startswith('verification/lean/SafeLearning/') and sha(ROOT,n)==sha(PUB,n)==h
 for n in ['reports/full-coverage/checkpoint-28-manifest.json','reports/full-coverage/checkpoint-28-selection.json','reports/full-coverage/checkpoint-28-ledger-manifest.json','reports/full-coverage/integration-28.json','reports/full-coverage/browser-checkpoint-28.json','reports/full-coverage/browser-corrections-28-inputs.json','reports/full-coverage/source60-eight-captured-regions-manual-review28-v1.json','reports/full-coverage/source60-four-page-math-scroll28-v3.json']:
  required[n]=sha(ROOT,n)
 for directory in ['reports/full-coverage/lean-checkpoint-28','reports/full-coverage/browser-artifacts-28']:
  files={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in safe(ROOT,directory).rglob('*') if p.is_file()};assert files
  required.update(files)
 for n,h in required.items():assert sha(PUB,n)==h and kept(n,exclusions),n
 ledger=read(PUB,'reports/full-coverage/lean-checkpoint-28/ledger-audit.json')
 assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
 assert ledger['inventory_sha256']==required['book/coverage/inventory.json']
 assert {d['domain'] for d in ledger['domains']}=={'core','foundations','applied','modules'}
 for d in ledger['domains']:assert d['ledger_sha256']==required['book/coverage/'+d['domain']+'.json']
 browser=read(ROOT,'reports/full-coverage/browser-checkpoint-28.json')
 assert browser['source_sha256']=={n:h for n,h in required.items() if n.startswith('SafeLearning/')}
 assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['page_count']==29 and browser['requested_viewport_count']==145
 assert len(browser['pages'])==29 and all(p['status']=='passed' and p['errors']==[] for p in browser['pages'])
 assert (browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'],browser['screenshot_count'])==(145,20,125,48)
 binput=read(ROOT,'reports/full-coverage/browser-corrections-28-inputs.json')
 assert binput['actual_execution']=={'file':browser['actual_execution'],'sha256':browser['actual_execution_sha256']}
 assert sha(ROOT,binput['actual_execution']['file'])==binput['actual_execution']['sha256']
 fresh=read(ROOT,binput['actual_execution']['file'])
 native(fresh,['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source60-28-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source60-28-v1','lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'])
 assets={n:h for n,h in required.items() if n.startswith('SafeLearning/')}
 assert fresh['source_sha256_before']==fresh['source_sha256_after']==assets
 assert fresh['qa_source_sha256']==browser['qa_source_sha256'] and len(fresh['qa_source_sha256'])==2
 assert all(sha(ROOT,n)==sha(PUB,n)==h for n,h in fresh['qa_source_sha256'].items())
 assert sha(ROOT,fresh['report'])==fresh['report_sha256']
 screenshots=binput['screenshot_aliases'];assert len(screenshots)==len({r['file'] for r in screenshots})==48
 for r in screenshots:
  assert r['file'].startswith('reports/full-coverage/browser-artifacts-28/')
  assert required[r['file']]==r['sha256']==sha(ROOT,r['original'])
 scroll=read(ROOT,'reports/full-coverage/source60-four-page-math-scroll28-v3.json')
 assert scroll['status']=='passed' and scroll['errors']==[] and scroll['actual_overflow_container_count']==8 and scroll['source_sha256']==assets
 assert len(scroll['pages'])==4 and {p['file'] for p in scroll['pages']}=={'lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'}
 assert all(p['status']=='passed' and p['errors']==[] and all(c['status']=='passed' for c in p['overflow_containers']) for p in scroll['pages'])
 actual('reports/full-coverage/source60-math-scroll28-execution-v3.json',['node','book/coverage/checks/root_check_math_scroll28_v3.mjs'])
 retired={}
 for n in ['reports/full-coverage/checkpoint-27-manifest.json','reports/full-coverage/checkpoint-27-selection.json']:
  h=sha(ROOT,n);assert sha(PUB,n)==h
  original_head=subprocess.check_output(['git','show','HEAD:'+n],cwd=PUB);assert hashlib.sha256(original_head).hexdigest()==h
  retired[n]=h
 for n in ['reports/full-coverage/lean-checkpoint-26','reports/full-coverage/browser-artifacts-25','reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source44-19-v2']:
  paths={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in safe(ROOT,n).rglob('*') if p.is_file()}
  tracked={p for p in subprocess.check_output(['git','ls-files','-z','--',n],cwd=PUB,text=True).split('\0') if p};assert tracked==set(paths)
  subprocess.run(['git','diff','--quiet','HEAD','--',n],cwd=PUB,check=True)
  assert all(sha(PUB,p)==h for p,h in paths.items());retired.update(paths)
 for i in range(56,61):
  for side in ['before','after']:
   n='book/coverage/inventory-'+side+'-correction'+str(i)+'.json';assert manifest['frozen_inputs_sha256'][n]==sha(ROOT,n)==sha(PUB,n)
 prerequisites={}
 for n,cmd in [
  ('reports/full-coverage/verify-checkpoint28-execution-v1.json',['python3','reports/full-coverage/checkpoint-28/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/checkpoint-27')]),
  ('reports/full-coverage/export-checkpoint28-execution-v1.json',['python3','book/coverage/export_audit28_v1.py','--snapshot','reports/full-coverage/checkpoint-28','--output','reports/full-coverage/lean-checkpoint-28']),
  ('reports/full-coverage/prepare-publication28-execution-v1.json',['python3','book/coverage/prepare_publication.py','28'])]:
  actual(n,cmd);prerequisites[n]=sha(ROOT,n)
 for n in [REPORT,BACKUP]:assert not safe(ROOT,n).exists() and not safe(PUB,n).exists()
 included=0
 for p in PUB.rglob('*'):
  relative=p.relative_to(PUB)
  if '.git' in relative.parts or not kept(relative.as_posix(),exclusions):continue
  assert not p.is_symlink(),relative.as_posix()
  if p.is_file():included+=p.stat().st_size
 report={'status':'passed_exact_pages28_archival_configuration_requires_actual_pages_and_live_checks','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'previous_configuration':{'file':BACKUP,'sha256':BEFORE},'config_sha256':hashlib.sha256(after).hexdigest(),'exclusions':sorted(exclusions),'excluded_count':len(exclusions),'new_literal_exclusions':sorted(ADDITIONS),'required_publication_files_sha256':required,'exact_selected_lean_sources_in_git_archive_sha256':archival,'retired_original_git_archive_files_sha256':retired,'actual_prerequisite_executions_sha256':prerequisites,'website_budget_bytes':BUDGET,'included_website_bytes_including_configuration_evidence':0,'coverage_complete':False,'scope':'Only literal website inclusion changes. All archives remain byte-identical in Git; all1186 selected Lean sources remain exact in the Git archive under the unchanged verification/lean website exclusion. The9896 theorem audit,current ledgers,source60 assets and48 screenshot downloads remain hosted.'}
 base=included-len(original)+len(after)+len(original)
 for _ in range(16):
  candidate=base+len(encoded(report))
  if candidate==report['included_website_bytes_including_configuration_evidence']:break
  report['included_website_bytes_including_configuration_evidence']=candidate
 else:raise AssertionError('Configuration byte count did not converge')
 assert candidate<BUDGET
 return original,after,report
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--apply',action='store_true');args=parser.parse_args();original,after,report=prepare()
 if args.apply:
  for base in [ROOT,PUB]:
   with safe(base,BACKUP).open('xb') as f:f.write(original)
   with safe(base,REPORT).open('xb') as f:f.write(encoded(report))
  assert sha(PUB,'_config.yml')==BEFORE
  safe(PUB,'_config.yml').write_bytes(after)
  assert sha(PUB,'_config.yml')==report['config_sha256']
 print(json.dumps({'status':report['status'],'applied':args.apply,'excluded_count':report['excluded_count'],'included_website_bytes':report['included_website_bytes_including_configuration_evidence'],'report':REPORT}))
