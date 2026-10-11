"""Recover the explicit24 whitelist after the genuine ignored-log git-add failure."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,shutil,subprocess
ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
REPORT='reports/full-coverage/publication24-prestage-v3.json'
OLD='reports/full-coverage/publication24-prestage-v2.json'
FAILED='reports/full-coverage/stage-publication24-execution-v2.json'
PEER='book/coverage/checks/future24-core/publication24-stage-recovery-independent-review-v6.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve())
    return p
def read(n):return json.loads(safe(n).read_text())
def changed():
    raw=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout
    result=set()
    for entry in filter(None,raw.decode().split('\0')):
        assert entry[:2] not in {'R ',' R','C ',' C'} and 'D' not in entry[:2],entry
        result.add(entry[3:])
    return result
def staged():
    return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.split(b'\0') if n}
assert not safe(REPORT).exists() and not (PUB/REPORT).exists()
assert sha(safe(OLD))=='903483c4cff8031b23845a78f984794914d00a103953fe2ffb3fc17b6142d5f8'
assert sha(safe(OLD))==sha(PUB/OLD)
old=read(OLD)
assert old['status']=='passed_explicit_audited_checkpoint24_publication_whitelist_ready_to_stage'
assert old['helper_sha256']==sha(safe('book/coverage/checks/root_stage_publication24_v4.py'))=='79bd0379d3618510918c13ff4e646796ca56fa8fad594432394ae05246984e8d'
failed=read(FAILED)
assert type(failed['actual_exit_code']) is int and failed['actual_exit_code']==1
assert failed['actual_command']==['python3','book/coverage/checks/root_stage_publication24_v4.py']
assert failed['helper_sha256_before']==failed['helper_sha256_after']=={'book/coverage/checks/root_stage_publication24_v4.py':old['helper_sha256']}
assert sha(safe(failed['log']))==failed['log_sha256']=='7f4e4d89c4193db7c7a27bd35c7ee6f62270f45e0220e7b53139e2af44c674e9'
assert b'git add' in safe(failed['log']).read_bytes() or b"Command '['git', 'add'" in safe(failed['log']).read_bytes()
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
assert sha(safe('reports/full-coverage/checkpoint-24-manifest.json'))==old['manifest_sha256']=='5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0'
assert sha(safe('reports/full-coverage/checkpoint-24-selection.json'))==old['selection_sha256']=='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
assert old['sources']==1144 and old['public_theorems']==9279 and old['coverage_complete'] is False
assert sha(PUB/'_config.yml')==old['config_sha256']=='11ac06530cbae6f0c63e84afb63d2a85e60ad6c666899044a50c3b799a293965'
progress=read('book/coverage/progress.json')
assert progress['publication_status']=='checkpoint24_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
assert progress['live_delivery_status']=='checkpoint24_awaiting_actual_pages_and_live_checks'
assert len(old['staged_paths'])==len(set(old['staged_paths']))==45213
paths=set(old['staged_paths'])
assert len(manifest['frozen_inputs_sha256'])==40485 and set(manifest['frozen_inputs_sha256'])<=paths
expected={}
for n in sorted(paths):
    if n=='_config.yml':digest=old['config_sha256']
    elif n in manifest['frozen_inputs_sha256'] and n!='book/coverage/progress.json':digest=manifest['frozen_inputs_sha256'][n]
    else:
        source=safe(n);assert source.is_file() and not source.is_symlink()
        digest=sha(source)
    destination=PUB/n;assert destination.is_file() and not destination.is_symlink() and sha(destination)==digest,n
    expected[n]=digest
assets={n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets==old['source52_assets_sha256']
for n,d in assets.items():assert sha(safe(n))==d
peer=read(PEER)
assert 'passed' in peer['status'] and peer.get('errors',[])==[] and peer['helper_sha256']==sha(Path(__file__))
assert sha(safe('book/coverage/checks/root_stage_publication24_recovery_v5.py'))=='dfddae1d82dd15e5432df357a2f6d9eef54d65b85050db93fa39c5aab6aa04dd'
extra={SELF,PEER,OLD,FAILED,failed['log'],'book/coverage/checks/root_stage_publication24_recovery_v5.py'}
for n,d in peer['closed_evidence_sha256'].items():assert sha(safe(n))==d;extra.add(n)
assert changed()<=paths|extra and staged()<=paths|extra
for n in extra:
    source=safe(n);assert source.is_file() and not source.is_symlink()
    target=PUB/n;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
    expected[n]=sha(source);assert sha(target)==expected[n]
paths.update(extra)
assert all(not n.startswith('book/coverage/checks/future25') and not n.startswith('book/coverage/checks/future26') for n in paths)
record={'status':'passed_explicit_checkpoint24_whitelist_recovery_ready_for_actual_git_stage',
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),
    'previous_prestage':{'file':OLD,'sha256':sha(safe(OLD))},'original_failed_execution':{'file':FAILED,'sha256':sha(safe(FAILED))},
    'validated_paths_count':len(expected),
    'validated_paths_sha256_fingerprint':hashlib.sha256(json.dumps(expected,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
    'additional_closed_paths_sha256':{n:expected[n] for n in sorted(extra)},
    'selection_sha256':old['selection_sha256'],'manifest_sha256':old['manifest_sha256'],
    'sources':1144,'public_theorems':9279,'source52_assets_sha256':assets,
    'coverage_complete':False,'awaiting_actual_commit_push_pages_and_live_checks':True}
with safe(REPORT).open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
shutil.copyfile(safe(REPORT),PUB/REPORT);paths.add(REPORT)
assert changed()<=paths and staged()<=paths
payload=''.join(n+'\0' for n in sorted(paths)).encode()
subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
assert staged() and staged()<=paths
for n,d in expected.items():assert sha(PUB/n)==d,n
assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
print(json.dumps({'status':'passed_explicit_staging','whitelist':len(paths),'actual_staged_paths':len(staged()),'sources':1144,'theorems':9279,'coverage_complete':False}))
