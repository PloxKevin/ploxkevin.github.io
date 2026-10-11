"""Stage exact completed delivery evidence and explicitly updated progress."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
REPORTS=ROOT/'reports/full-coverage'
SELF='book/coverage/checks/root_stage_publication23_delivery_metadata_v1.py'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def safe(name):
    assert name and not Path(name).is_absolute() and '..' not in Path(name).parts
    assert not any(c in name for c in ('\0','\n','\r'))
    return name
def dirty():
    out=set()
    for cmd in [['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],
                ['git','ls-files','--others','--exclude-standard','-z']]:
        out.update(x.decode() for x in subprocess.run(cmd,cwd=PUB,capture_output=True,check=True).stdout.split(b'\0') if x)
    return out

live=read(REPORTS/'live-checkpoint-23-attempt1.json')
commit=live['commit']
assert live['status']=='passed_all31_asset_sha256'
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,capture_output=True,check=True).stdout.decode().strip()==commit
assert read(REPORTS/'pages-checkpoint-23-attempt1.json')['status']=='passed'
workflow=read(REPORTS/'publication23-pages-view-execution-v1.log')
assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
assert all(j['conclusion']=='success' for j in workflow['jobs'])
manifest=read(REPORTS/'checkpoint-23-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['proof_files'])==1131
for name,digest in manifest['frozen_inputs_sha256'].items():
    if name.startswith('SafeLearning/'):assert sha(ROOT/name)==sha(PUB/name)==digest,name
progress=read(ROOT/'book/coverage/progress.json')
assert progress['last_published_content_commit']==commit
assert progress['verified_checkpoint']['proof_files']==1131 and progress['verified_checkpoint']['theorems']==9193
assert progress['live_delivery_evidence']=='reports/full-coverage/live-checkpoint-23-attempt1.json'
assert progress['verified_checkpoint']['coverage_complete'] is False

names={SELF,'book/coverage/progress.json','reports/full-coverage/README.md'}
names.add('book/coverage/checks/publication23-budget-repair-original-author-draft-byte-aliases-v1.json')
for p in (ROOT/'book/coverage/checks/publication23-budget-repair-author-history').rglob('*'):
    if p.is_file():names.add(p.relative_to(ROOT).as_posix())
for stem in ['publication23-content-commit-execution-v1','publication23-content-push-execution-v1',
             'publication23-pages-watch-execution-v1','publication23-pages-view-execution-v1',
             'publication23-pages-artifact-execution-v1','live23-attempt1-execution-v1',
             'stage-publication23-execution-v1','stage-publication23-additional-evidence-execution-v1',
             'publication23-ledger-check-execution-v1']:
    p=REPORTS/(stem+'.json');row=read(p)
    assert row['actual_exit_code']==0 and sha(ROOT/row['log'])==row['log_sha256']
    names.update('reports/full-coverage/'+stem+suffix for suffix in ['.json','.log'])
for name in ['live-checkpoint-23-attempt1.json','pages-checkpoint-23-attempt1.json',
             'pages-checkpoint-23-attempt1.log','progress-checkpoint23-before-delivery-update-original-v1.json',
             'README-checkpoint23-before-delivery-update-original-v1.md','progress-checkpoint23-delivery-update-v1.json',
             'README-checkpoint23-before-audit-update-original-v1.md','README-checkpoint23-audit-update-v1.json',
             'publication-checkpoint23-additional-execution-evidence-v1.json',
             'publication-checkpoint23-additional-evidence-pathspec-v1.nul',
             'publication-checkpoint23-staging-execution.json','publication-checkpoint23-staging-whitelist.json',
             'publication-checkpoint23-stage-pathspec.nul','lean-checkpoint-23/export-output-integrity-v1.json',
             'frozen-ledger-checkpoint23-v1.json']:
    names.add('reports/full-coverage/'+name)
for pattern in ['publication23-additional-evidence-*','publication23-helper-independent-foundations-*',
                'pages23-config-independent-modules-*']:
    for p in (ROOT/'book/coverage/checks').glob(pattern):
        if p.is_file():names.add(p.relative_to(ROOT).as_posix())
assert 'book/coverage/checks/publication23-additional-evidence-helper-independent-foundations-review-v1.json' in names
assert all(not n.startswith('verification/lean/') for n in names)
expected={}
for name in sorted(names):
    source=ROOT/safe(name)
    assert source.is_file() and not source.is_symlink() and source.stat().st_size<100_000_000,name
    expected[name]=sha(source)
assert dirty()<=names
record=REPORTS/'publication23-delivery-metadata-prestage-v1.json'
assert not record.exists()
for name,digest in expected.items():
    source=ROOT/name;target=PUB/name;target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
    assert sha(source)==sha(target)==digest,name
record.write_text(json.dumps({'status':'passed_explicit_completed_delivery_metadata',
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':commit,
    'paths_sha256':expected,'coverage_complete':False},indent=2)+'\n')
name=record.relative_to(ROOT).as_posix();shutil.copyfile(record,PUB/name);names.add(name)
assert dirty()<=names
subprocess.run(['git','add','-f','--',*sorted(names)],cwd=PUB,check=True)
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,capture_output=True,check=True).stdout
staged_names={x.decode() for x in staged.split(b'\0') if x}
assert staged_names and staged_names<=names
print(json.dumps({'status':'passed','staged_paths':len(staged_names),'allowed_paths':len(names),'coverage_complete':False}))
