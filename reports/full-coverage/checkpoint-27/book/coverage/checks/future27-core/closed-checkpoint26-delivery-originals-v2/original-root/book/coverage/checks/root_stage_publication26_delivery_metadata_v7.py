"""Stage only completed26 delivery metadata after actual Pages and all live hashes.

Root executes this helper; code authorship establishes no delivery or Git result.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess
ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
REPORT='reports/full-coverage/publication26-delivery-metadata-prestage-v1.json'
PEER='book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v7.json'
UPDATER='book/coverage/checks/root_update_publication26_delivery_progress_v4.py'
UPDATER_PEER='book/coverage/checks/future26-core/publication26-delivery-updater-independent-applied-review-v4.json'
PRIMARY_HELPER='book/coverage/checks/root_stage_publication26_v4.py'
PRIMARY_PEER='book/coverage/checks/future26-core/publication26-stage-independent-review-v4.json'

def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert str(Path(n))==n and not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def target(n):
    safe(n);p=PUB/n;assert p.resolve().is_relative_to(PUB.resolve());return p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def zero(d,code=0):
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(v) is int and v==code for v in values)
def actual(n,code=0):
    d=read(n);zero(d,code)
    logs=[d[k] for k in ('log','raw_log') if k in d]
    hashes=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
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
    return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.split(b'\0') if n}
def peer_evidence(n,paths):
    peer=read(n);assert 'passed' in peer['status'] and peer.get('errors',[])==[];paths.add(n)
    aliases=peer.get('original_closed_byte_aliases',{})
    if isinstance(aliases,list):
        assert all(isinstance(r,dict) and set(r)=={'original_path','file','sha256'} for r in aliases)
        assert len({r['original_path'] for r in aliases})==len(aliases)
        aliases={r['original_path']:{'file':r['file'],'sha256':r['sha256']} for r in aliases}
    assert isinstance(aliases,dict)
    canonical={}
    for original,row in aliases.items():
        assert isinstance(original,str) and Path(original).is_absolute() and not any(c in original for c in ('\0','\n','\r'))
        assert isinstance(row,dict) and set(row)=={'file','sha256'}
        n2,digest=row['file'],row['sha256']
        assert isinstance(digest,str) and len(digest)==64 and all(c in '0123456789abcdef' for c in digest)
        assert n2 not in canonical or canonical[n2]==digest
        assert sha(safe(n2))==digest;canonical[n2]=digest;paths.add(n2)
    closed=peer.get('closed_evidence_sha256',{});assert isinstance(closed,dict)
    for original,digest in closed.items():
        if Path(original).is_absolute():
            assert original in aliases and aliases[original]['sha256']==digest;n2=aliases[original]['file']
        else:n2=original
        assert sha(safe(n2))==digest;paths.add(n2)
    return peer


def main():
    assert not safe(REPORT).exists() and not target(REPORT).exists()
    live_name='reports/full-coverage/live-checkpoint-26-attempt2.json';live=read(live_name);commit=live['commit']
    assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31 and live['remote_main']==commit
    assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==commit
    pages_name='reports/full-coverage/pages-checkpoint-26-attempt2.json';pages=read(pages_name)
    assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==commit
    workflow=read('reports/full-coverage/publication26-pages-view-execution-v1.log')
    assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
    assert workflow['jobs'] and all(j['conclusion']=='success' for j in workflow['jobs'])
    manifest_name='reports/full-coverage/checkpoint-26-manifest.json';manifest=read(manifest_name)
    assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1167
    assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets)==31 and len({row['source'] for row in live['assets']})==31
    assert {row['source']:row['expected_sha256'] for row in live['assets']}==assets
    for row in live['assets']:
        assert row['http_status']==200 and row['matches'] is True
        assert row['actual_sha256']==row['expected_sha256']==sha(safe(row['source']))
    for n,h in assets.items():assert sha(safe(n))==sha(target(n))==h,n
    audit_name='reports/full-coverage/lean-checkpoint-26/verification-original.json';audit=read(audit_name)
    assert audit['status']=='passed' and audit['proof_file_count']==1167 and audit['theorem_count']==9503
    assert manifest['successful_verification']['report_sha256']==sha(safe(audit_name))
    assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
    assert {d['name'] for d in audit['declarations']}==set(audit['axiom_dependencies'])
    progress=read('book/coverage/progress.json')
    assert progress['last_published_content_commit']==commit
    assert progress['verified_checkpoint']['proof_files']==1167 and progress['verified_checkpoint']['theorems']==9503
    assert progress['verified_checkpoint']['coverage_complete'] is False
    assert progress['live_delivery_evidence']==live_name and progress['live_delivery_status']==live['status']
    assert progress['publication_status']=='checkpoint26_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
    update_name='reports/full-coverage/progress-checkpoint26-delivery-update-v1.json';update=read(update_name)
    assert update['status']=='passed_actual_checkpoint26_delivery_progress_update' and update['content_commit']==commit and update['coverage_complete'] is False
    assert set(update['updated_sha256'])=={'book/coverage/progress.json','reports/full-coverage/README.md'}
    assert isinstance(update['evidence_sha256'],dict) and update['evidence_sha256']
    for n,h in update['evidence_sha256'].items():assert sha(safe(n))==h,n
    assert update['helper']=={'file':UPDATER,'sha256':sha(safe(UPDATER))}
    for n,h in update['updated_sha256'].items():assert sha(safe(n))==h,n
    native_name='reports/full-coverage/publication26-prestage-v1.json';native=read(native_name)
    assert native['status']=='passed_explicit_audited_checkpoint26_publication_whitelist_ready_to_stage'
    assert native['helper_sha256']==sha(safe(PRIMARY_HELPER))
    assert (native['sources'],native['public_theorems'],native['new_sources'])==(1167,9503,11)
    assert native['coverage_complete'] is False and native['source53_assets_sha256']==assets
    assert native['selection_sha256']==sha(safe('reports/full-coverage/checkpoint-26-selection.json'))
    assert native['manifest_sha256']==sha(safe(manifest_name)) and native['config_sha256']==sha(PUB/'_config.yml')
    assert len(native['staged_paths'])==len(set(native['staged_paths']))
    for n,h in native['additional_closed_paths_sha256'].items():
        assert sha(target(n))==h,n
        if n not in update['updated_sha256']:assert sha(safe(n))==h,n
    names={SELF,PEER,UPDATER,UPDATER_PEER,PRIMARY_HELPER,PRIMARY_PEER,native_name,live_name,pages_name,update_name,
        'book/coverage/progress.json','reports/full-coverage/README.md','reports/full-coverage/pages-checkpoint-26-attempt2.log',
        'reports/full-coverage/progress-checkpoint26-before-delivery-update-original-v1.json',
        'reports/full-coverage/README-checkpoint26-before-delivery-update-original-v1.md',
        'book/coverage/checks/root_stage_publication26_v1.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v1.py',
        'book/coverage/checks/root_prepare_pages26_config_v1.py','book/coverage/checks/pages26-config-helper-independent-foundations-review-v1.json',
        'book/coverage/checks/root_prepare_pages26_config_v2.py','book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json',
        'book/coverage/checks/root_stage_publication26_v2.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v2.py',
        'book/coverage/checks/future26-core/publication26-stage-independent-review-v2.json',
        'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v2.json',
        'book/coverage/checks/root_stage_publication26_v3.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v3.py',
        'book/coverage/checks/future26-core/publication26-stage-independent-review-v3.json',
        'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v3.json',
        'reports/full-coverage/stage-publication26-execution-v1.json','reports/full-coverage/stage-publication26-execution-v1.log',
        'book/coverage/checks/root_stage_publication26_delivery_metadata_v4.py',
        'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v4.json',
        'book/coverage/checks/root_update_publication26_delivery_progress_v1.py',
        'book/coverage/checks/future26-core/publication26-delivery-updater-independent-applied-review-v1.json',
        'book/coverage/checks/root_update_publication26_delivery_progress_v2.py',
        'book/coverage/checks/root_stage_publication26_delivery_metadata_v5.py',
        'book/coverage/checks/root_update_publication26_delivery_progress_v3.py',
        'book/coverage/checks/root_stage_publication26_delivery_metadata_v6.py'}
    names.update(update['evidence_sha256'])
    closed={}
    for stem in ('stage-publication26-execution-v2','publication26-delivery-progress-update-execution-v1',
        'publication26-content-commit-execution-v1','publication26-content-push-execution-v1',
        'publication26-pages-watch-execution-v1','publication26-pages-view-execution-v1',
        'publication26-pages-artifact-execution-v1','live26-attempt2-execution-v1'):
        n='reports/full-coverage/'+stem+'.json';d,log=actual(n);names.update([n,log]);closed[n]=sha(safe(n));closed[log]=sha(safe(log))
        if stem=='stage-publication26-execution-v2':
            assert d['actual_command']==['python3',PRIMARY_HELPER]
            assert d['helper_sha256_before']==d['helper_sha256_after']=={PRIMARY_HELPER:native['helper_sha256']}
        if stem=='publication26-delivery-progress-update-execution-v1':
            assert d['actual_command']==['python3',UPDATER]
            assert d['helper_sha256_before']==d['helper_sha256_after']=={UPDATER:sha(safe(UPDATER))}
    for n in (PEER,UPDATER_PEER,PRIMARY_PEER):
        peer=peer_evidence(n,names)
        helper=SELF if n==PEER else UPDATER if n==UPDATER_PEER else PRIMARY_HELPER
        assert peer['helper_sha256']==sha(safe(helper))
    expected={}
    for n in names:
        assert not n.startswith('verification/lean/'),n
        p=safe(n);assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000;expected[n]=sha(p)
    assert dirty()<=names and staged()<=names,sorted(dirty()-names)
    out={'status':'passed_explicit_completed26_delivery_metadata','checked_at_utc':datetime.now(timezone.utc).isoformat(),
        'helper_sha256':sha(Path(__file__)),'content_commit':commit,'paths_sha256':expected,
        'closed_actual_execution_evidence_sha256':closed,'coverage_complete':False}
    exclusions=read('reports/full-coverage/pages26-config-preparation-v1.json')['exclusions']
    assert len(exclusions)==len(set(exclusions))==116
    assert all(isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in ('\0','\n','\r','*','?','[','{')) for n in exclusions)
    kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
    included_now=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
    replacements=sum(safe(n).stat().st_size-(target(n).stat().st_size if target(n).is_file() else 0) for n in expected if kept(n))
    out['included_website_bytes_before_explicit_copy']=included_now;out['included_closed_replacement_byte_delta']=replacements
    record_bytes=(json.dumps(out,indent=2)+'\n').encode()
    assert 0<=included_now+replacements+(len(record_bytes) if kept(REPORT) else 0)<850_000_000
    for n,h in expected.items():
        p=target(n);p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(n),p)
        assert sha(safe(n))==sha(p)==h,n
    with safe(REPORT).open('xb') as f:f.write(record_bytes)
    shutil.copyfile(safe(REPORT),target(REPORT));names.add(REPORT)
    assert dirty()<=names and staged()<=names
    payload=''.join(n+'\0' for n in sorted(names)).encode()
    subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
    assert staged() and staged()<=names
    for n,h in expected.items():assert sha(target(n))==h,n
    assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
    print(json.dumps({'status':'passed','actual_staged_paths':len(staged()),'allowed_paths':len(names),'coverage_complete':False}))

if __name__=='__main__':main()
