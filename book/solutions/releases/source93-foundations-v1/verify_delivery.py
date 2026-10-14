"""Observe one exact Source93 commit, all Pages jobs and all thirty-one assets."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

ROOT=Path(__file__).resolve().parents[4]
PUB=ROOT/'reports/book/publication-repo'
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
BASE='book/solutions/releases/source93-foundations-v1'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit',required=True);parser.add_argument('--phase',choices=['content','metadata'],required=True)
    parser.add_argument('--attempt',type=int,required=True)
    args=parser.parse_args()
    assert len(args.commit)==40 and all(c in '0123456789abcdef' for c in args.commit) and args.attempt>0
    observed=[]
    def run(argv):
        p=subprocess.run(argv,cwd=PUB,text=True,capture_output=True)
        observed.append(dict(command=argv,actual_exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr))
        assert p.returncode==0,(argv,p.stderr)
        return p.stdout
    remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0]
    pages=json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']))
    runs=json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs?per_page=15']))['workflow_runs']
    runs=[r for r in runs if r['head_sha']==args.commit and r['name']=='pages build and deployment']
    jobs=[]
    for r in runs:
        jobs.extend(json.loads(run(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs/'+str(r['id'])+'/jobs']))['jobs'])
    stamp=datetime.now(timezone.utc).isoformat()
    ready=h.read(BASE+'/ready.json')
    def asset(item):
        name,digest=item
        url='https://ploxkevin.github.io/'+name+'?source93='+args.commit[:12]+'&attempt='+str(args.attempt)
        row=dict(file=name,url=url,expected_sha256=digest,matches=False)
        try:
            request=urllib.request.Request(url,headers={'Cache-Control':'no-cache'})
            with urllib.request.urlopen(request,timeout=30) as response:
                raw=response.read();row.update(http_status=response.status,actual_sha256=h.sha(raw))
            row['matches']=row['http_status']==200 and row['actual_sha256']==digest
        except Exception as error:row['error']=str(error)
        return row
    with ThreadPoolExecutor(max_workers=8) as pool:assets=list(pool.map(asset,ready['reader_assets_sha256'].items()))
    passed=(remote==args.commit and pages.get('status')=='built' and pages.get('commit')==args.commit
            and runs and all(r['status']=='completed' and r['conclusion']=='success' for r in runs)
            and len(jobs)>=3 and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs)
            and len(assets)==31 and all(a['matches'] for a in assets))
    result=dict(status='passed_all31_live_assets_and_pages_jobs' if passed else 'not_yet_confirmed',
                commit=args.commit,phase=args.phase,attempt=args.attempt,checked_at_utc=stamp,
                ready=h.ref(BASE+'/ready.json'),remote_main=remote,pages=pages,runs=runs,jobs=jobs,
                assets=assets,actual_commands=observed)
    h.json_put('reports/solution-review/source93-'+args.phase+'-delivery-attempt'+str(args.attempt)+'.json',result)
    print(dict(status=result['status'],matching_assets=sum(a['matches'] for a in assets),pages_status=pages.get('status'),jobs=len(jobs)))
    if not passed:sys.exit(1)


if __name__=='__main__':main()
