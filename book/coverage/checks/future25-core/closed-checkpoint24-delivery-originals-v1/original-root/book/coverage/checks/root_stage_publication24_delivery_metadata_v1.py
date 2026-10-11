"""Stage only closed24 delivery evidence and the actual progress update."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,shutil,subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
REPORTS=ROOT/'reports/full-coverage'
SELF=Path(__file__).relative_to(ROOT).as_posix()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n
    assert p.resolve().is_relative_to(ROOT.resolve())
    return p
def dirty():
    result=set()
    for cmd in [['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],
                ['git','ls-files','--others','--exclude-standard','-z']]:
        result.update(s.decode() for s in subprocess.run(cmd,cwd=PUB,capture_output=True,check=True).stdout.split(b'\0') if s)
    return result

out=REPORTS/'publication24-delivery-metadata-prestage-v1.json'
assert not out.exists()
live=read(REPORTS/'live-checkpoint-24-attempt1.json')
commit=live['commit']
assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31 and live['remote_main']==commit
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==commit
assert read(REPORTS/'pages-checkpoint-24-attempt1.json')['status']=='passed'
workflow=read(REPORTS/'publication24-pages-view-execution-v1.log')
assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
assert workflow['jobs'] and all(j['conclusion']=='success' for j in workflow['jobs'])
manifest=read(REPORTS/'checkpoint-24-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1144
for n,d in manifest['frozen_inputs_sha256'].items():
    if n.startswith('SafeLearning/'):assert sha(safe(n))==sha(PUB/n)==d
progress=read(ROOT/'book/coverage/progress.json')
assert progress['last_published_content_commit']==commit
assert progress['verified_checkpoint']['proof_files']==1144 and progress['verified_checkpoint']['theorems']==9279
assert progress['live_delivery_evidence']=='reports/full-coverage/live-checkpoint-24-attempt1.json'
assert progress['publication_status']=='checkpoint24_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
assert progress['verified_checkpoint']['coverage_complete'] is False
update=read(REPORTS/'progress-checkpoint24-delivery-update-v1.json')
assert update['content_commit']==commit and update['coverage_complete'] is False
for n,d in update['updated_sha256'].items():assert sha(safe(n))==d

names={SELF,'book/coverage/checks/root_update_publication24_delivery_progress_v1.py',
       'book/coverage/progress.json','reports/full-coverage/README.md'}
for stem in ['stage-publication24-execution-v1','publication24-delivery-progress-update-execution-v1',
    'publication24-content-commit-execution-v1','publication24-content-push-execution-v1',
    'publication24-pages-watch-execution-v1','publication24-pages-view-execution-v1',
    'publication24-pages-artifact-execution-v1','live24-attempt1-execution-v1']:
    p=REPORTS/(stem+'.json');d=read(p)
    assert d['actual_exit_code']==0 and sha(safe(d['log']))==d['log_sha256']
    names.update([p.relative_to(ROOT).as_posix(),d['log']])
for n in ['publication24-prestage-v1.json','live-checkpoint-24-attempt1.json',
    'pages-checkpoint-24-attempt1.json','pages-checkpoint-24-attempt1.log',
    'progress-checkpoint24-before-delivery-update-original-v1.json',
    'README-checkpoint24-before-delivery-update-original-v1.md','progress-checkpoint24-delivery-update-v1.json']:
    names.add('reports/full-coverage/'+n)
peer_name='book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v1.json'
peer=read(safe(peer_name))
assert 'passed' in peer['status'] and peer.get('errors',[])==[]
assert peer['helpers_sha256']=={n:sha(safe(n)) for n in [SELF,'book/coverage/checks/root_update_publication24_delivery_progress_v1.py']}
names.add(peer_name)
for n,d in peer['closed_evidence_sha256'].items():assert sha(safe(n))==d;names.add(n)
assert all(not n.startswith('verification/lean/') for n in names)
expected={}
for n in sorted(names):
    p=safe(n);assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000
    expected[n]=sha(p)
assert dirty()<=names,sorted(dirty()-names)
for n,d in expected.items():
    target=PUB/n;target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(safe(n),target)
    assert sha(safe(n))==sha(target)==d
record={'status':'passed_explicit_completed24_delivery_metadata',
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':commit,
    'paths_sha256':expected,'coverage_complete':False}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
n=out.relative_to(ROOT).as_posix();shutil.copyfile(out,PUB/n);names.add(n)
assert dirty()<=names
payload=''.join(n+'\0' for n in sorted(names)).encode()
subprocess.run(['git','add','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
staged={s.decode() for s in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.split(b'\0') if s}
assert staged and staged<=names
print(json.dumps({'status':'passed','staged_paths':len(staged),'allowed_paths':len(names),'coverage_complete':False}))
