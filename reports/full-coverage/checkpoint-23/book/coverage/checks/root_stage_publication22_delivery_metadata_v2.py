from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil,subprocess
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo';R=ROOT/'reports/full-coverage'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
commit=read(R/'live-checkpoint-22-attempt1.json')['commit']
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,capture_output=True,check=True).stdout.decode().strip()==commit
assert read(R/'live-checkpoint-22-attempt1.json')['status']=='passed_all31_asset_sha256'
assert read(R/'pages-checkpoint-22-attempt1.json')['status']=='passed'
workflow=read(R/'publication22-pages-view-execution-v1.log')
assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
assert all(j['conclusion']=='success' for j in workflow['jobs'])
names={'book/coverage/progress.json','reports/full-coverage/README.md','book/coverage/checks/root_stage_publication22_delivery_metadata_v2.py'}
for base in ['publication22-content-commit-execution-v1','publication22-content-push-execution-v1','publication22-pages-watch-execution-v1','publication22-pages-view-execution-v1','publication22-pages-artifact-execution-v1','live22-attempt1-execution-v1','stage-publication22-execution-v1', 'stage-publication22-additional-evidence-execution-v1']:
 names.update('reports/full-coverage/'+base+ext for ext in ['.json','.log'])
for name in ['live-checkpoint-22-attempt1.json','pages-checkpoint-22-attempt1.json','pages-checkpoint-22-attempt1.log','progress-checkpoint22-before-delivery-update-original-v1.json','README-checkpoint22-before-delivery-update-original-v1.md','progress-checkpoint22-delivery-update-v1.json','publication-checkpoint22-staging-execution.json','publication-checkpoint22-staging-whitelist.json','publication-checkpoint22-stage-pathspec.nul','lean-checkpoint-22/export-output-integrity-v1.json']:
 names.add('reports/full-coverage/'+name)
for name in ['publication-checkpoint22-additional-execution-evidence-v1.json', 'publication-checkpoint22-additional-evidence-pathspec-v1.nul', 'README-checkpoint22-before-audit-update-original-v1.md']:
 names.add('reports/full-coverage/'+name)
for p in (ROOT/'book/coverage/checks').glob('publication22-additional-evidence-stager-independent-modules-*'):
 if p.is_file():names.add(p.relative_to(ROOT).as_posix())
assert any('independent-modules-review' in n for n in names)
for p in (ROOT/'book/coverage/checks').glob('publication22-helper-independent-applied-*'):
 if p.is_file():names.add(p.relative_to(ROOT).as_posix())
manifest=read(R/'checkpoint-22-manifest.json')
for n,d in manifest['frozen_inputs_sha256'].items():
 if n.startswith('SafeLearning/'):
  assert sha(PUB/n)==d,n
for n in sorted(names):
 p=ROOT/n;target=PUB/n
 assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000,n
 target.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(p,target)
 assert sha(p)==sha(target),n
record=R/'publication22-delivery-metadata-prestage-v1.json';assert not record.exists()
record.write_text(json.dumps(dict(status='passed_explicit_actual_delivery_metadata',checked_at_utc=datetime.now(timezone.utc).isoformat(),content_commit=commit,coverage_complete=False,paths_sha256={n:sha(ROOT/n) for n in sorted(names)}),indent=2)+'\n')
names.add(str(record.relative_to(ROOT)));shutil.copyfile(record,PUB/record.relative_to(ROOT))
for argv in [['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],['git','ls-files','--others','--exclude-standard','-z']]:
 output=subprocess.run(argv,cwd=PUB,capture_output=True,check=True).stdout
 assert {x.decode() for x in output.split(b'\0') if x}<=names
subprocess.run(['git','add','-f','--',*sorted(names)],cwd=PUB,check=True)
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,capture_output=True,check=True).stdout
staged_names={x.decode() for x in staged.split(b'\0') if x}
assert staged_names and staged_names<=names
print(json.dumps(dict(status='passed',staged_paths=len(staged_names),allowed_paths=len(names),coverage_complete=False)))
