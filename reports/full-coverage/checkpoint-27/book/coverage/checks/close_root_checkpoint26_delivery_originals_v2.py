"""Close completed26 content and metadata delivery before current27 edits."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess
ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
BASE=ROOT/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2'
ACTIVE='close-checkpoint26-delivery-originals-execution-v2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert str(Path(n))==n and not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def actual(stem,code=0):
    p=REPORTS/(stem+'.json');d=read(p)
    codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert codes and all(type(c) is int and c==code for c in codes)
    assert sha(safe(d['log']))==d['log_sha256'];return d

def main():
    assert not BASE.exists()
    manifest=read(REPORTS/'checkpoint-26-manifest.json')
    assert manifest['status']=='formal_verification_passed_partial_coverage'
    assert len(manifest['proof_files'])==1167
    assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    owners={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {
        'book/coverage/'+owner+'.json' for owner in ['core','foundations','applied','modules','applied-promotions']}}
    assert len(assets)==31 and len(owners)==5
    protected={n:row['sha256'] for n,row in manifest['proof_files'].items()}
    protected.update(assets);protected.update(owners)
    for n,h in protected.items():assert sha(safe(n))==h,n
    commits={}
    for attempt in [2,3]:
        live=read(REPORTS/f'live-checkpoint-26-attempt{attempt}.json')
        pages=read(REPORTS/f'pages-checkpoint-26-attempt{attempt}.json')
        assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31
        assert len({r['source'] for r in live['assets']})==31
        assert {r['source']:r['expected_sha256'] for r in live['assets']}==assets
        for row in live['assets']:
            assert type(row['http_status']) is int and row['http_status']==200 and row['matches'] is True
            assert row['actual_sha256']==row['expected_sha256']
        assert live['commit']==live['remote_main']==pages['commit']==pages['expected_commit']
        page_codes=[pages[k] for k in ('actual_exit_code','exit_code') if k in pages]
        assert page_codes and all(type(c) is int and c==0 for c in page_codes)
        assert pages['status']=='passed';commits[attempt]=live['commit']
        d=actual(f'live26-attempt{attempt}-execution-v1')
        assert d['actual_command']==['python3','book/coverage/verify_live19.py','26',live['commit'],'--attempt',str(attempt)]
    assert commits[2]!=commits[3]
    assert subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT/'reports/book/publication-repo',check=True,capture_output=True).stdout.decode().strip()==commits[3]
    for stem in ['publication26-content-push-execution-v1','publication26-delivery-metadata-push-execution-v1',
        'publication26-pages-watch-execution-v1','publication26-metadata-pages-watch-execution-v1']:
        actual(stem)
    for stem,commit in [('publication26-pages-view-execution-v1',commits[2]),('publication26-metadata-pages-view-execution-v1',commits[3])]:
        d=actual(stem);w=read(safe(d['log']))
        assert w['headSha']==commit and w['status']=='completed' and w['conclusion']=='success'
        assert w['jobs'] and all(j['conclusion']=='success' for j in w['jobs'])
    actual('live26-attempt1-execution-v1',1)
    actual('stage-publication26-execution-v1',1)
    progress=read(ROOT/'book/coverage/progress.json')
    assert progress['publication_status']=='checkpoint26_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
    assert progress['last_published_content_commit']==commits[2]
    assert progress['verified_checkpoint']['proof_files']==1167 and progress['verified_checkpoint']['theorems']==9503
    assert progress['verified_checkpoint']['coverage_complete'] is False
    assert sha(ROOT/'book/coverage/inventory.json')==sha(ROOT/'book/coverage/inventory-after-correction53.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
    assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections'])==53
    names={ROOT/'book/coverage/progress.json',REPORTS/'README.md',ROOT/'book/coverage/inventory.json',ROOT/'book/coverage/material-corrections.json'}
    names.update(safe(n) for n in owners)
    for p in REPORTS.glob('*26*'):
        if p.is_file() and p.suffix in {'.json','.log','.md','.yml'} and p.stem!=ACTIVE:
            names.add(p)
            if p.suffix=='.json' and '-execution-' in p.name:
                d=read(p);codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
                assert codes and all(type(c) is int and c in {0,1} and c==codes[0] for c in codes)
                assert sha(safe(d['log']))==d['log_sha256'];names.add(safe(d['log']))
    for p in (ROOT/'book/coverage/checks').glob('*26*.py'):names.add(p)
    for p in (ROOT/'book/coverage/checks/future26-core').glob('*.json'):
        if any(s in p.name for s in ['publication26','checkpoint26','pages26']):names.add(p)
    for p in (ROOT/'book/coverage/checks').glob('pages26-*.json'):names.add(p)
    originals={}
    for p in names:
        assert p.is_file() and not p.is_symlink() and p.is_relative_to(ROOT)
        originals[p.relative_to(ROOT).as_posix()]=sha(p)
    rows=[]
    for n,h in sorted(originals.items()):
        p=safe(n);assert sha(p)==h
        target=BASE/'original-root'/n;target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as f:f.write(p.read_bytes())
        assert sha(target)==h
        rows.append({'original':{'file':n,'sha256':h},'immutable_original_byte_copy':{'file':target.relative_to(ROOT).as_posix(),'sha256':h}})
    recorder=Path('/tmp/root_actual_step26_v1.py');alias=BASE/'original-tmp'/recorder.name
    alias.parent.mkdir(parents=True,exist_ok=True)
    with alias.open('xb') as f:f.write(recorder.read_bytes())
    assert sha(alias)==sha(recorder)
    for n,h in protected.items():assert sha(safe(n))==h,n
    out={'status':'completed_checkpoint26_actual_content_and_metadata_delivery_original_bytes_closed',
        'closed_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':commits[2],'metadata_commit':commits[3],
        'both_actual_pages_runs_and_all31_live_assets_passed':True,'retained_failed_stager3_and_first_live_dns_attempt':True,
        'aliases':rows,'original_absolute_recorder_byte_alias':{'original_absolute_path':str(recorder),'canonical_file':alias.relative_to(ROOT).as_posix(),'sha256':sha(alias)},
        'scope':'Exact completed26 reports/helpers/reviews/actual successes and failures/source53 inventory/owners/progress/README bytes and original times preserved before current27 edits. The active closer JSON/log is explicitly excluded until completed; no coverage added.'}
    with (BASE/'closed-original-byte-aliases-v1.json').open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'passed','closed_original_root_files':len(rows),'content_commit':commits[2],'metadata_commit':commits[3],'live_owners_unchanged':True}))
if __name__=='__main__':main()
