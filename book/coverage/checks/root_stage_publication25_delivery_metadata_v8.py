"""Stage completed25 delivery evidence after actual commit, Pages and31 live hashes.

Root executes this helper. Native data and independent approvals are mandatory;
authoring or reviewing this draft does not establish a delivery result.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
REPORT='reports/full-coverage/publication25-delivery-metadata-prestage-v1.json'
PEER='book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v8.json'
UPDATER='book/coverage/checks/root_update_publication25_delivery_progress_v1.py'
UPDATER_SHA='7adfb8e7c031973f3f538fc23b441aef0098753c3eef322d0929e7b16820e99d'
UPDATER_PEER='book/coverage/checks/future25-core/publication25-delivery-updater-independent-applied-review-v1.json'
PRIMARY_HELPER='book/coverage/checks/root_stage_publication25_v8.py'
PRIMARY_PEER='book/coverage/checks/future25-core/publication25-stage-independent-review-v8.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert str(Path(n))==n and not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def target(n):
    safe(n);p=PUB/n;assert p.resolve().is_relative_to(PUB.resolve());return p
def read(n):return json.loads(safe(n).read_text())
def actual(n,code=0):
    d=read(n);codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert codes and all(type(c) is int and c==code for c in codes)
    logs=[d[k] for k in ('log','raw_log') if k in d];hashes=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
    assert logs and hashes and all(x==logs[0] for x in logs) and all(x==hashes[0] for x in hashes)
    assert sha(safe(logs[0]))==hashes[0];return d,logs[0]
def dirty():
    raw=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout
    out=set()
    for entry in filter(None,raw.decode().split('\0')):
        assert entry[:2] not in {'R ',' R','C ',' C'} and 'D' not in entry[:2],entry
        out.add(entry[3:])
    return out
def staged():
    return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,
       check=True,capture_output=True).stdout.split(b'\0') if n}
def add_peer(n,names):
    p=read(n);assert 'passed' in p['status'] and p.get('errors',[])==[];names.add(n)
    aliases=p.get('original_closed_byte_aliases',{});assert isinstance(aliases,dict)
    targets=set()
    for original,row in aliases.items():
        assert isinstance(original,str) and Path(original).is_absolute() and not any(c in original for c in ('\0','\n','\r'))
        assert isinstance(row,dict) and set(row)=={'file','sha256'}
        assert row['file'] not in targets and sha(safe(row['file']))==row['sha256']
        targets.add(row['file']);names.add(row['file'])
    for original,digest in p.get('closed_evidence_sha256',{}).items():
        if Path(original).is_absolute():
            assert original in aliases and aliases[original]['sha256']==digest;n2=aliases[original]['file']
        else:n2=original
        assert sha(safe(n2))==digest;names.add(n2)
    return p

def main():
    assert not safe(REPORT).exists() and not target(REPORT).exists()
    live_name='reports/full-coverage/live-checkpoint-25-attempt1.json';live=read(live_name);commit=live['commit']
    assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31 and live['remote_main']==commit
    assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==commit
    pages_name='reports/full-coverage/pages-checkpoint-25-attempt1.json';pages=read(pages_name)
    assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==commit
    workflow=read('reports/full-coverage/publication25-pages-view-execution-v1.log')
    assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
    assert workflow['jobs'] and all(j['conclusion']=='success' for j in workflow['jobs'])
    manifest=read('reports/full-coverage/checkpoint-25-manifest.json')
    assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1156
    assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets)==31 and len({row['source'] for row in live['assets']})==31
    assert {row['source']:row['expected_sha256'] for row in live['assets']}==assets
    for row in live['assets']:
        assert row['http_status']==200 and row['matches'] is True
        assert row['actual_sha256']==row['expected_sha256']==sha(safe(row['source']))
    for n,h in assets.items():assert sha(safe(n))==sha(target(n))==h,n
    progress=read('book/coverage/progress.json')
    assert progress['last_published_content_commit']==commit
    assert progress['verified_checkpoint']['proof_files']==1156 and progress['verified_checkpoint']['theorems']==9369
    assert progress['verified_checkpoint']['coverage_complete'] is False
    assert progress['live_delivery_evidence']==live_name and progress['live_delivery_status']==live['status']
    assert progress['publication_status']=='checkpoint25_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
    update_name='reports/full-coverage/progress-checkpoint25-delivery-update-v1.json';update=read(update_name)
    assert update['status']=='passed_actual_checkpoint25_delivery_progress_update'
    assert update['content_commit']==commit and update['coverage_complete'] is False
    assert set(update['updated_sha256'])=={'book/coverage/progress.json','reports/full-coverage/README.md'}
    assert isinstance(update['evidence_sha256'],dict) and update['evidence_sha256']
    for n,h in update['evidence_sha256'].items():assert sha(safe(n))==h,n
    assert update['helper']=={'file':UPDATER,'sha256':UPDATER_SHA} and sha(safe(UPDATER))==UPDATER_SHA
    for n,h in update['updated_sha256'].items():assert sha(safe(n))==h,n
    native_name='reports/full-coverage/publication25-prestage-v1.json';native=read(native_name)
    assert native['status']=='passed_explicit_audited_checkpoint25_publication_whitelist_ready_to_stage'
    assert native['helper_sha256']==sha(safe(PRIMARY_HELPER))
    assert (native['sources'],native['public_theorems'],native['new_sources'])==(1156,9369,12)
    assert native['coverage_complete'] is False and native['source52_assets_sha256']==assets
    assert native['selection_sha256']==sha(safe('reports/full-coverage/checkpoint-25-selection.json'))
    assert native['manifest_sha256']==sha(safe('reports/full-coverage/checkpoint-25-manifest.json'))
    assert native['config_sha256']==sha(PUB/'_config.yml')
    assert len(native['staged_paths'])==len(set(native['staged_paths']))
    names={SELF,PEER,'book/coverage/checks/root_stage_publication25_delivery_metadata_v1.py','book/coverage/checks/root_stage_publication25_delivery_metadata_v2.py',
      'book/coverage/checks/root_stage_publication25_delivery_metadata_v3.py',
      'book/coverage/checks/root_stage_publication25_delivery_metadata_v4.py',
      'book/coverage/checks/root_stage_publication25_delivery_metadata_v5.py',
      'book/coverage/checks/root_stage_publication25_delivery_metadata_v6.py',
      'book/coverage/checks/root_stage_publication25_delivery_metadata_v7.py',
      'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v7.json',
      'book/coverage/checks/root_stage_publication25_v7.py',
      'book/coverage/checks/future25-core/publication25-stage-independent-review-v7.json',
      'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v6.json',
      'book/coverage/checks/root_stage_publication25_v6.py',
      'book/coverage/checks/future25-core/publication25-stage-independent-review-v6.json',
      'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v3.json',UPDATER,UPDATER_PEER,PRIMARY_HELPER,PRIMARY_PEER,
      'book/coverage/progress.json','reports/full-coverage/README.md',native_name,live_name,pages_name,
      'reports/full-coverage/pages-checkpoint-25-attempt1.log',update_name,
      'reports/full-coverage/progress-checkpoint25-before-delivery-update-original-v1.json',
      'reports/full-coverage/README-checkpoint25-before-delivery-update-original-v1.md'}
    closed={}
    for stem in ['stage-publication25-execution-v3','publication25-delivery-progress-update-execution-v1',
       'publication25-content-commit-execution-v1','publication25-content-push-execution-v1',
       'publication25-pages-watch-execution-v1','publication25-pages-view-execution-v1',
       'publication25-pages-artifact-execution-v1','live25-attempt1-execution-v1']:
        n='reports/full-coverage/'+stem+'.json';d,log=actual(n);names.update([n,log])
        closed[n]=sha(safe(n));closed[log]=sha(safe(log))
        if stem=='stage-publication25-execution-v3':
            assert d['actual_command']==['python3',PRIMARY_HELPER]
            assert d['helper_sha256_before']==d['helper_sha256_after']=={PRIMARY_HELPER:native['helper_sha256']}
    failed_name='reports/full-coverage/stage-publication25-execution-v1.json'
    failed,log=actual(failed_name,1);names.update([failed_name,log])
    closed[failed_name]=sha(safe(failed_name));closed[log]=sha(safe(log))
    assert failed['actual_command']==['python3','book/coverage/checks/root_stage_publication25_v6.py']
    assert failed['helper_sha256_before']==failed['helper_sha256_after']=={'book/coverage/checks/root_stage_publication25_v6.py':sha(safe('book/coverage/checks/root_stage_publication25_v6.py'))}
    failed2_name='reports/full-coverage/stage-publication25-execution-v2.json'
    failed2,log2=actual(failed2_name,1);names.update([failed2_name,log2])
    closed[failed2_name]=sha(safe(failed2_name));closed[log2]=sha(safe(log2))
    assert failed2['actual_command']==['python3','book/coverage/checks/root_stage_publication25_v7.py']
    assert failed2['helper_sha256_before']==failed2['helper_sha256_after']=={'book/coverage/checks/root_stage_publication25_v7.py':sha(safe('book/coverage/checks/root_stage_publication25_v7.py'))}
    for n in [PEER,UPDATER_PEER,PRIMARY_PEER,
       'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v7.json',
       'book/coverage/checks/future25-core/publication25-stage-independent-review-v7.json',
       'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v3.json',
       'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v6.json',
       'book/coverage/checks/future25-core/publication25-stage-independent-review-v6.json']:
        if n in {'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v7.json','book/coverage/checks/future25-core/publication25-stage-independent-review-v7.json'}:
            old=add_peer(n,names)
            old_helper='book/coverage/checks/root_stage_publication25_delivery_metadata_v7.py' if 'metadata-stager' in n else 'book/coverage/checks/root_stage_publication25_v7.py'
            assert old['helper_sha256']==sha(safe(old_helper))
            continue
        if n in {'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v6.json','book/coverage/checks/future25-core/publication25-stage-independent-review-v6.json'}:
            old=add_peer(n,names)
            old_helper='book/coverage/checks/root_stage_publication25_delivery_metadata_v6.py' if 'metadata-stager' in n else 'book/coverage/checks/root_stage_publication25_v6.py'
            assert old['helper_sha256']==sha(safe(old_helper))
            continue
        if n.endswith('publication25-delivery-metadata-stager-independent-foundations-review-v3.json'):
            old=add_peer(n,names)
            assert old['helper_sha256']==sha(safe('book/coverage/checks/root_stage_publication25_delivery_metadata_v3.py'))
            continue
        p=add_peer(n,names)
        helper=SELF if n==PEER else UPDATER if n==UPDATER_PEER else PRIMARY_HELPER
        assert p['helper_sha256']==sha(safe(helper))
    expected={}
    for n in names:
        assert not n.startswith('verification/lean/') and not n.startswith('book/coverage/checks/future26'),n
        p=safe(n);assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000
        expected[n]=sha(p)
    assert dirty()<=names and staged()<=names,sorted(dirty()-names)
    for n,h in expected.items():
        p=target(n);p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(n),p)
        assert sha(safe(n))==sha(p)==h,n
    out={'status':'passed_explicit_completed25_delivery_metadata','checked_at_utc':datetime.now(timezone.utc).isoformat(),
      'helper_sha256':sha(Path(__file__)),'content_commit':commit,'paths_sha256':expected,
      'closed_actual_execution_evidence_sha256':closed,'coverage_complete':False}
    with safe(REPORT).open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
    shutil.copyfile(safe(REPORT),target(REPORT));names.add(REPORT)
    assert dirty()<=names and staged()<=names
    payload=''.join(n+'\0' for n in sorted(names)).encode()
    subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
    assert staged() and staged()<=names
    for n,h in expected.items():assert sha(target(n))==h,n
    assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
    print(json.dumps({'status':'passed','actual_staged_paths':len(staged()),'allowed_paths':len(names),'coverage_complete':False}))

if __name__=='__main__':main()
