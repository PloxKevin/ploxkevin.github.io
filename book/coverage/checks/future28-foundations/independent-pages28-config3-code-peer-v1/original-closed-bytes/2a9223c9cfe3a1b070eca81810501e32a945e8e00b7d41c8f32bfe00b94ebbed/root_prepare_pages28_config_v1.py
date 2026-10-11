"""Keep exact checkpoint28 downloads while excluding literal Git audit archives."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_prepare_pages28_config_v1.py'
REPORT='reports/full-coverage/pages28-config-preparation-v1.json'
BACKUP='reports/full-coverage/pages28-config-previous-original-v1.yml'
BEFORE='cc1f0f9cf93b0d9ffdff6e422bfb6b85f073e4efb0d705378adc32a46a40af23'
HEAD='8fa808699674d13e4297d226ef1530a7ec744ad0'
HEADER='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
BUDGET=850000000
ADDITIONS={
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
def actual(n,command):
 d=read(ROOT,n);assert d['status']=='passed'
 codes=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d]
 assert codes and all(type(v) is int and v==0 for v in codes)
 cmds=[d[k] for k in ['actual_command','command'] if k in d];assert cmds and all(c==command for c in cmds)
 cwds=[d[k] for k in ['actual_workdir','working_directory','workdir','cwd'] if k in d];assert cwds and all(v==str(ROOT) for v in cwds)
 assert sha(ROOT,d['log'])==d['log_sha256'];return d
def prepare():
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PUB,text=True).strip()==HEAD
 assert sha(PUB,'_config.yml')==BEFORE
 original=safe(PUB,'_config.yml').read_bytes();old={line[4:] for line in original.decode().splitlines() if line.startswith('  - ')}
 assert len(old)==133 and original.decode()==HEADER+''.join('  - '+n+'\n' for n in sorted(old))
 assert len(ADDITIONS)==20 and not old&ADDITIONS
 exclusions=old|ADDITIONS
 for n in exclusions:safe(PUB,n)
 after=(HEADER+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode()
 manifest=read(ROOT,'reports/full-coverage/checkpoint-28-manifest.json');selection=read(ROOT,'reports/full-coverage/checkpoint-28-selection.json')
 audit=read(ROOT,'reports/full-coverage/lean-checkpoint-28/verification-original.json')
 assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['proof_files']==selection['proof_files']
 assert manifest['selection_sha256']==sha(ROOT,'reports/full-coverage/checkpoint-28-selection.json')
 assert len(selection['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1186 and selection['new_file_count']==11
 assert audit['status']=='passed' and audit['theorem_count']==len(audit['declarations'])==len(audit['axiom_dependencies'])==9896
 assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
 assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==11
 assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1175
 assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert all(set(a)<=set(audit['allowed_standard_axioms']) for a in audit['axiom_dependencies'].values())
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
 required={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
 assert len([n for n in required if n.startswith('SafeLearning/')])==31
 assert required['book/coverage/inventory.json']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
 for n,r in selection['proof_files'].items():required[n]=r['sha256']
 for n in ['reports/full-coverage/checkpoint-28-manifest.json','reports/full-coverage/checkpoint-28-selection.json','reports/full-coverage/checkpoint-28-ledger-manifest.json','reports/full-coverage/integration-28.json','reports/full-coverage/browser-checkpoint-28.json','reports/full-coverage/browser-corrections-28-inputs.json','reports/full-coverage/source60-eight-captured-regions-manual-review28-v1.json','reports/full-coverage/source60-four-page-math-scroll28-v3.json']:
  required[n]=sha(ROOT,n)
 for directory in ['reports/full-coverage/lean-checkpoint-28','reports/full-coverage/browser-artifacts-28']:
  files={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in safe(ROOT,directory).rglob('*') if p.is_file()};assert files
  required.update(files)
 for n,h in required.items():assert sha(PUB,n)==h and kept(n,exclusions),n
 assert read(PUB,'reports/full-coverage/lean-checkpoint-28/ledger-audit.json')['integrity_status']=='passed'
 browser=read(ROOT,'reports/full-coverage/browser-checkpoint-28.json')
 assert browser['source_sha256']=={n:h for n,h in required.items() if n.startswith('SafeLearning/')}
 assert (browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'],browser['screenshot_count'])==(145,20,125,48)
 scroll=read(ROOT,'reports/full-coverage/source60-four-page-math-scroll28-v3.json');assert scroll['status']=='passed' and scroll['errors']==[] and scroll['actual_overflow_container_count']==8
 retired={}
 for n in ['reports/full-coverage/checkpoint-27-manifest.json','reports/full-coverage/checkpoint-27-selection.json']:
  h=sha(ROOT,n);assert sha(PUB,n)==h
  original_head=subprocess.check_output(['git','show','HEAD:'+n],cwd=PUB);assert hashlib.sha256(original_head).hexdigest()==h
  retired[n]=h
 for n in ['reports/full-coverage/lean-checkpoint-26','reports/full-coverage/browser-artifacts-25']:
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
 included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix(),exclusions))
 report={'status':'passed_exact_pages28_archival_configuration_requires_actual_pages_and_live_checks','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'previous_configuration':{'file':BACKUP,'sha256':BEFORE},'config_sha256':hashlib.sha256(after).hexdigest(),'exclusions':sorted(exclusions),'excluded_count':len(exclusions),'new_literal_exclusions':sorted(ADDITIONS),'required_publication_files_sha256':required,'retired_original_git_archive_files_sha256':retired,'actual_prerequisite_executions_sha256':prerequisites,'website_budget_bytes':BUDGET,'included_website_bytes_including_configuration_evidence':0,'coverage_complete':False,'scope':'Only literal website inclusion changes. All archives remain byte-identical in Git; current1186 selected sources,9896 theorem audit,current ledgers, source60 assets and48 screenshot downloads remain hosted.'}
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
