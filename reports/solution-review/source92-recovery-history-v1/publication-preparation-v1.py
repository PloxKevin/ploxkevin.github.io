"""Stage the exact verified recovery without caches or candidate/archive trees."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy

BASE='book/solutions/releases/source92-opening-v1'
PUB=ROOT/'reports/book/publication-repo'
READY='reports/solution-review/source92-recovery-ready-v1.json'
PLAN='reports/solution-review/source92-publication-plan-v1.json'
STAGED='reports/solution-review/source92-publication-staged-v1.json'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=PUB,text=True).strip()


def prepare():
    ready=h.read(READY);plan=h.read(BASE+'/plan-v1.json')
    assert ready['status']=='passed_installed_source92_openings_and_partial_formal_piece02_ready'
    assert not git('status','--porcelain')
    assert git('rev-parse','HEAD')=='f280ebf994f7ca02be959e35f9a97876d0313d46'
    files=set(plan['site_after_sha256'])|{r['file'] for r in plan['files']}
    files.update(r['file'] for r in ready['documents'])
    files.update({READY,'book/coverage/source91-piece02/README.md'})
    for directory in [BASE,'book/solutions/opening-step-review-v1','book/solutions/module-opening-step-review-v1',
                      'book/coverage/source91-piece02','reports/full-coverage/source91-piece02']:
        for parent,ds,fs in os.walk(ROOT/directory):
            ds[:]=[d for d in ds if d not in {'candidates','browser-artifacts-v1','qa-shots-v1','__pycache__'}]
            for filename in fs:
                path=Path(parent)/filename
                if path.is_symlink() or path.suffix in {'.lock','.png','.pdf'}:continue
                assert path.is_file()
                files.add(path.relative_to(ROOT).as_posix())
    # Actual audit reports and logs, without proof snapshot sources or caches.
    for directory in ['reports/full-coverage/runtime-source91-piece02-v1/reports/lean-verification',
                      'reports/solution-review/runtime-source92-piece02-v1/reports/lean-verification']:
        for path in (ROOT/directory).iterdir():
            assert path.is_file() and not path.is_symlink()
            if path.name=='kernel-progress.json':continue
            files.add(path.relative_to(ROOT).as_posix())
    for path in (ROOT/'reports/solution-review').glob('source92-*-native-v*.json'):
        files.add(path.relative_to(ROOT).as_posix())
        n=h.read(path.relative_to(ROOT).as_posix())
        files.update([n['log'],n['started_receipt']])
    files.add('reports/solution-review/module-opening-step-review-v1.json')
    for shot in h.read(BASE+'/opening-capture-v1.json')['shots']:files.add(shot['path'])
    audit=h.read(ready['selected_audit']['file'])
    aggregate='verification/lean/SafeLearning.lean'
    audit_aggregate='reports/solution-review/runtime-source92-piece02-v1/'+aggregate
    records=[]
    for name in sorted(files|{aggregate,'verification/lean/SafeLearning/CompleteModulesLandscapeSource91ARPartII.lean'}):
        assert not {'.git','.lake','source-objects','__pycache__'}.intersection(Path(name).parts)
        source=audit_aggregate if name==aggregate else name
        after=h.ref(source)['sha256']
        target=PUB/name
        before=h.sha(target.read_bytes()) if target.is_file() else None
        records.append({'file':name,'source':h.ref(source),'before_sha256':before,'after_sha256':after})
    assert sum(r['file'].startswith('SafeLearning/') for r in records)==31
    h.json_put(PLAN,{'status':'prepared_exact_source92_publication','expected_head':git('rev-parse','HEAD'),
        'release_ready':h.ref(READY),'helper':h.ref(BASE+'/publish_recovery.py'),'files':records,
        'site_sha256':plan['site_after_sha256'],'selected_proof_sha256':audit['proof_sha256'],
        'caches_candidate_trees_and_unselected_proofs_published':False})
    print({'files':len(records),'bytes':sum(h.path(r['source']['file']).stat().st_size for r in records),'plan':h.ref(PLAN)})


def stage(expected):
    assert h.ref(PLAN)['sha256']==expected
    p=h.read(PLAN)
    assert h.ref(READY)==p['release_ready'] and git('rev-parse','HEAD')==p['expected_head']
    for r in p['files']:
        assert h.ref(r['source']['file'])==r['source']
        target=PUB/r['file']
        now=h.sha(target.read_bytes()) if target.is_file() else None
        assert now in {r['before_sha256'],r['after_sha256']}
    for r in p['files']:
        target=PUB/r['file'];target.parent.mkdir(parents=True,exist_ok=True)
        now=h.sha(target.read_bytes()) if target.is_file() else None
        if now!=r['after_sha256']:atomic_copy(target,h.path(r['source']['file']).read_bytes())
    proofs={p.relative_to(PUB).as_posix():h.sha(p.read_bytes()) for p in (PUB/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
    assert proofs==p['selected_proof_sha256']
    for r in p['files']:assert h.sha((PUB/r['file']).read_bytes())==r['after_sha256']
    # Stage explicit paths. Other portfolio files are outside this recovery.
    for start in range(0,len(p['files']),200):
        subprocess.run(['git','add','--']+[r['file'] for r in p['files'][start:start+200]],cwd=PUB,check=True)
    dirty=git('diff','--cached','--name-only').splitlines()
    assert set(dirty)<=set(r['file'] for r in p['files'])
    assert not git('diff','--name-only')
    for name in dirty:
        row=next(r for r in p['files'] if r['file']==name)
        raw=subprocess.check_output(['git','show',':'+name],cwd=PUB)
        assert h.sha(raw)==row['after_sha256']
    h.json_put(STAGED,{'status':'passed_exact_source92_publication_index',
        'plan':h.ref(PLAN),'changed_paths':dirty,'files':len(p['files']),
        'proof_files':1272,'reader_assets':31,'unexpected_paths':[]})
    print({'status':'staged_exact','changed_paths':len(dirty),'proof_files':1272,'reader_assets':31})


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['prepare','stage'])
    parser.add_argument('--plan-sha256');args=parser.parse_args()
    prepare() if args.command=='prepare' else stage(args.plan_sha256)
