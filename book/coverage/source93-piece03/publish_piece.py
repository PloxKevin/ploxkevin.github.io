"""Stage exact verified proof sources/evidence and observe GitHub Pages delivery.

No commit or push is hidden in this helper. A plan binds the preexisting clean
checkout and every staged byte. Only the selected proof set is publishable.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c
sys.path.insert(0,str(ROOT/'book/solutions'))
from solution_release import atomic_copy

HERE='book/coverage/source93-piece03'
REPORTS='reports/full-coverage/source93-piece03'
RUNTIME='reports/full-coverage/runtime-source93-piece03-v1'
AUDIT=RUNTIME+'/reports/lean-verification/verification.json'
PLAN=REPORTS+'/publication-plan-v1.json'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=PUB,text=True).strip()


def stage():
    ledger=c.read(HERE+'/ledger-v1.json');audit=c.read(AUDIT)
    assert ledger['audit']==c.ref(AUDIT) and audit['status']=='passed'
    assert not git('status','--porcelain')
    assert git('rev-parse','HEAD')==git('rev-parse','origin/main')
    prior=c.read('reports/solution-review/runtime-source93-foundations-v1/reports/lean-verification/verification.json')
    published={p.relative_to(PUB).as_posix():c.sha(p.read_bytes()) for p in
               (PUB/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
    assert published==prior['proof_sha256']
    for name,digest in audit['proof_sha256'].items():assert c.ref(name)['sha256']==digest
    for name,digest in audit['source_sha256'].items():assert c.ref(name)['sha256']==digest
    assert c.ref('verification/lean/SafeLearning.lean')['sha256']==audit['project_sha256']['verification/lean/SafeLearning.lean']
    files={
        'README.md','book/solutions/RELEASE.md','book/coverage/README.md',
        'book/coverage/CONTINUATION.md','book/coverage/progress.json','verification/lean/README.md',
        'verification/lean/SafeLearning.lean',
        'verification/lean/SafeLearning/CompleteModulesGaussianTailRounding.lean',
        'verification/lean/SafeLearning/CompleteModulesLandscapeSource93RoundingBridge.lean',
        'reports/solution-review/source93-publication-finish-v1.json',
        'reports/solution-review/source93-final-closure-native-v1.json',
        'reports/solution-review/source93-final-closure-native-v1.log'}
    for directory in [HERE,REPORTS,RUNTIME+'/reports/lean-verification']:
        files.update(p.relative_to(ROOT).as_posix() for p in (ROOT/directory).rglob('*')
                     if p.is_file() and not p.name.endswith('.lock'))
    files.discard(PLAN)
    # A separate review receipt is included only if it was actually supplied.
    if ledger['independent_review']:files.add(ledger['independent_review']['file'])
    rows=[]
    for name in sorted(files):
        assert not {'.git','.lake','__pycache__'}.intersection(Path(name).parts)
        assert name!=PLAN
        if name.endswith('.started.json'):
            assert c.path(name.removesuffix('.started.json')+'.json').is_file(), 'Unfinished native command: '+name
        source=c.ref(name);target=PUB/name
        rows.append(dict(file=name,source=source,before_sha256=c.sha(target.read_bytes()) if target.is_file() else None))
    c.json_put(PLAN,dict(status='prepared_exact_selected_source93_piece03_publication',
        expected_head=git('rev-parse','HEAD'),ledger=c.ref(HERE+'/ledger-v1.json'),files=rows,
        site_sha256=audit['source_sha256'],proof_sha256=audit['proof_sha256'],
        unselected_future_proofs_included=False,caches_included=False,helper=c.ref(HERE+'/publish_piece.py')))
    for row in rows:
        assert c.ref(row['file'])==row['source']
        target=PUB/row['file'];target.parent.mkdir(parents=True,exist_ok=True)
        if row['source']['sha256']!=row['before_sha256']:
            atomic_copy(target,c.path(row['file']).read_bytes())
    target=PUB/PLAN;target.parent.mkdir(parents=True,exist_ok=True)
    atomic_copy(target,c.path(PLAN).read_bytes())
    names=sorted(files|{PLAN})
    for offset in range(0,len(names),150):
        subprocess.run(['git','add','-f','--',*names[offset:offset+150]],cwd=PUB,check=True)
    changed=git('diff','--cached','--name-only').splitlines()
    assert set(changed)<=set(names) and not git('diff','--name-only')
    for name in changed:
        assert c.sha(subprocess.check_output(['git','show',':'+name],cwd=PUB))==c.ref(name)['sha256']
    selected={p.relative_to(PUB).as_posix():c.sha(p.read_bytes()) for p in
              (PUB/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
    assert selected==audit['proof_sha256']
    for name,digest in audit['source_sha256'].items():assert c.sha((PUB/name).read_bytes())==digest
    c.json_put(REPORTS+'/publication-staged-v1.json',dict(status='passed_exact_publication_index',
        plan=c.ref(PLAN),changed_paths=changed,reader_assets_unchanged=31,
        selected_proof_files=1274,selected_theorems=11544,unexpected_paths=[]))
    print(dict(status='staged_exact',changed_paths=len(changed),reader_assets_unchanged=31,
               evidence_bytes=sum(c.path(n).stat().st_size for n in files)))


def observe(args):
    assert len(args.commit)==40 and all(x in '0123456789abcdef' for x in args.commit)
    assert args.attempt>0
    commands=[]
    def run(argv):
        p=subprocess.run(argv,cwd=PUB,text=True,capture_output=True)
        commands.append(dict(command=argv,actual_exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr))
        assert p.returncode==0,(argv,p.stderr)
        return p.stdout
    remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0]
    pages=json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']))
    runs=json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs?per_page=15']))['workflow_runs']
    runs=[r for r in runs if r['head_sha']==args.commit and r['name']=='pages build and deployment']
    jobs=[]
    for row in runs:
        jobs.extend(json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs/'+str(row['id'])+'/jobs']))['jobs'])
    audit=c.read(AUDIT)
    def asset(item):
        name,digest=item
        url='https://ploxkevin.github.io/'+name+'?formal-piece03='+args.commit[:12]+'&attempt='+str(args.attempt)
        row=dict(file=name,url=url,expected_sha256=digest,matches=False)
        try:
            req=urllib.request.Request(url,headers={'Cache-Control':'no-cache'})
            with urllib.request.urlopen(req,timeout=30) as response:
                row.update(http_status=response.status,actual_sha256=c.sha(response.read()))
            row['matches']=row['http_status']==200 and row['actual_sha256']==digest
        except Exception as error:row['error']=str(error)
        return row
    with ThreadPoolExecutor(max_workers=8) as pool:assets=list(pool.map(asset,audit['source_sha256'].items()))
    passed=bool(remote==args.commit and pages.get('status')=='built' and pages.get('commit')==args.commit
        and runs and all(r['status']=='completed' and r['conclusion']=='success' for r in runs)
        and len(jobs)>=3 and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs)
        and len(assets)==31 and all(r['matches'] for r in assets))
    report=dict(status='passed_all31_live_assets_and_pages_jobs' if passed else 'not_yet_confirmed',
        commit=args.commit,phase=args.phase,attempt=args.attempt,checked_at_utc=datetime.now(timezone.utc).isoformat(),
        audit=c.ref(AUDIT),remote_main=remote,pages=pages,runs=runs,jobs=jobs,assets=assets,actual_commands=commands)
    c.json_put(REPORTS+'/'+args.phase+'-delivery-attempt'+str(args.attempt)+'.json',report)
    print(dict(status=report['status'],matching_assets=sum(r['matches'] for r in assets),jobs=len(jobs),pages_status=pages.get('status')))
    if not passed:sys.exit(1)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['stage','observe'])
    parser.add_argument('--commit');parser.add_argument('--phase',choices=['content','metadata'])
    parser.add_argument('--attempt',type=int)
    args=parser.parse_args()
    if args.command=='stage':stage()
    else:
        assert args.commit and args.phase and args.attempt
        observe(args)
