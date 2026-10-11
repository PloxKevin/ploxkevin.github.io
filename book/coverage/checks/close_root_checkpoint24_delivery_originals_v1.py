"""Close completed24 delivery bytes before any live25 integration."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future25-core/closed-checkpoint24-delivery-originals-v1'
OUT=BASE/'closed-original-byte-aliases-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(n):
 assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
 assert not any(c in n for c in ('\0','\n','\r'))
 p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def read(n):return json.loads(safe(n).read_text())
assert not OUT.exists() and not BASE.exists()
content='13d6823f7378a9d2b9737242763cf19b9b321b28';metadata='fdaee6318200e9090876c6ea840958c53ac2021e'
for attempt,commit in [(1,content),(2,metadata)]:
 live=read('reports/full-coverage/live-checkpoint-24-attempt'+str(attempt)+'.json')
 pages=read('reports/full-coverage/pages-checkpoint-24-attempt'+str(attempt)+'.json')
 assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31 and live['commit']==live['remote_main']==commit
 assert pages['status']=='passed'
assert subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT/'reports/book/publication-repo',check=True,capture_output=True).stdout.decode().strip()==metadata
stems=['stage-publication24-execution-v1','stage-publication24-execution-v2','stage-publication24-execution-v3',
 'publication24-content-commit-execution-v1','publication24-content-push-execution-v1',
 'publication24-pages-watch-execution-v1','publication24-pages-view-execution-v1','publication24-pages-artifact-execution-v1','live24-attempt1-execution-v1',
 'publication24-delivery-progress-update-execution-v1','publication24-delivery-metadata-stage-execution-v1','publication24-delivery-metadata-commit-execution-v1','publication24-delivery-metadata-push-execution-v1',
 'publication24-metadata-pages-watch-execution-v1','publication24-metadata-pages-view-execution-v1','publication24-metadata-pages-artifact-execution-v1','live24-attempt2-execution-v1',
 'publication24-delivery-metadata-code-independent-root-execution-v1','publication24-delivery-metadata-code-independent-root-execution-v2']
failed={'stage-publication24-execution-v1','stage-publication24-execution-v2','publication24-delivery-metadata-code-independent-root-execution-v1'}
names=set()
for stem in stems:
 n='reports/full-coverage/'+stem+'.json';d=read(n);expected=1 if stem in failed else 0
 assert type(d['actual_exit_code']) is int and d['actual_exit_code']==expected
 assert sha(safe(d['log']))==d['log_sha256'];names.update([n,d['log']])
for n in ['book/coverage/progress.json','reports/full-coverage/README.md','reports/full-coverage/publication24-prestage-v2.json','reports/full-coverage/publication24-prestage-v3.json',
 'reports/full-coverage/publication24-delivery-metadata-prestage-v1.json','reports/full-coverage/progress-checkpoint24-before-preparation-original-v1.json','reports/full-coverage/README-checkpoint24-before-preparation-original-v1.md',
 'reports/full-coverage/progress-checkpoint24-preparation-update-v1.json','reports/full-coverage/progress-checkpoint24-before-delivery-update-original-v1.json','reports/full-coverage/README-checkpoint24-before-delivery-update-original-v1.md','reports/full-coverage/progress-checkpoint24-delivery-update-v1.json']:
 names.add(n)
for attempt in [1,2]:
 for name in ['live-checkpoint-24-attempt'+str(attempt)+'.json','pages-checkpoint-24-attempt'+str(attempt)+'.json','pages-checkpoint-24-attempt'+str(attempt)+'.log']:names.add('reports/full-coverage/'+name)
for n in ['root_stage_publication24_v1.py','root_stage_publication24_v2.py','root_stage_publication24_v3.py','root_stage_publication24_v4.py','root_stage_publication24_recovery_v5.py','root_stage_publication24_recovery_v6.py','root_update_publication24_delivery_progress_v1.py','root_stage_publication24_delivery_metadata_v1.py','root_stage_publication24_delivery_metadata_v2.py','root_stage_publication24_delivery_metadata_v3.py','root_stage_publication24_delivery_metadata_v4.py','root_prepare_checkpoint24_documentation_v1.py','root_prepare_checkpoint24_documentation_v2.py','root_prepare_pages24_config_v1.py','root_prepare_pages24_config_v2.py']:
 names.add('book/coverage/checks/'+n)
peer_names=['publication24-stage-independent-review-v1.json','publication24-stage-independent-review-v2.json','publication24-stage-independent-review-v3.json','publication24-stage-independent-review-v4.json','publication24-stage-recovery-independent-review-v6.json','publication24-delivery-metadata-helpers-independent-foundations-review-v1.json','publication24-delivery-metadata-helpers-independent-foundations-review-v2.json','publication24-delivery-metadata-helpers-independent-foundations-review-v3.json','pages24-config-independent-output-review-v1.json']
for name in peer_names:
 n='book/coverage/checks/future24-core/'+name;peer=read(n);names.add(n)
 for original,h in peer['closed_evidence_sha256'].items():
  if Path(original).is_absolute():
   row=peer['original_closed_byte_aliases'][original];assert row['sha256']==h;ncopy=row['file']
  else:ncopy=original
  assert sha(safe(ncopy))==h;names.add(ncopy)
progress=read('book/coverage/progress.json')
assert progress['publication_status']=='checkpoint24_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
assert progress['verified_checkpoint']['proof_files']==1144 and progress['verified_checkpoint']['theorems']==9279
protected={n:r['sha256'] for n,r in read('reports/full-coverage/checkpoint-24-manifest.json')['proof_files'].items()}
protected.update({n:h for n,h in read('reports/full-coverage/checkpoint-24-manifest.json')['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']}})
for n,h in protected.items():assert sha(safe(n))==h
rows=[]
for n in sorted(names):
 original=safe(n);assert original.is_file() and not original.is_symlink()
 target=BASE/'original-root'/n;target.parent.mkdir(parents=True,exist_ok=True)
 with target.open('xb') as f:f.write(original.read_bytes())
 assert sha(original)==sha(target)
 rows.append({'original':{'file':n,'sha256':sha(original)},'immutable_original_byte_copy':{'file':target.relative_to(ROOT).as_posix(),'sha256':sha(target)}})
runner=Path('/tmp/root_actual_step24_v1.py');copy=BASE/'original-tmp/root_actual_step24_v1.py';copy.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(runner,copy);assert sha(runner)==sha(copy)
for n,h in protected.items():assert sha(safe(n))==h
record={'status':'completed_checkpoint24_actual_content_and_metadata_delivery_original_bytes_closed',
 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':content,'metadata_commit':metadata,
 'both_actual_pages_runs_and_all31_live_assets_passed':True,'aliases':rows,
 'original_absolute_recorder_byte_alias':{'original_absolute_path':str(runner),'canonical_file':copy.relative_to(ROOT).as_posix(),'sha256':sha(copy)},
 'scope':'Original source/helper/review/execution/report/README/progress bodies and all actual times remain exact. New aliases close delivered24 provenance before owner25 integration, without a new compiler or mathematical review claim.'}
with OUT.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','closed_original_root_files':len(rows),'actual_content_commit':content,'actual_metadata_commit':metadata,'live_owners_unchanged':True}))
