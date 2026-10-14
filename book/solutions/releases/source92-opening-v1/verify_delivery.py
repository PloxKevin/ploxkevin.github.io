"""Observe the exact remote commit, three Pages jobs and all 31 live assets."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import urllib.request

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
PUB=ROOT/'reports/book/publication-repo'
BASE='book/solutions/releases/source92-opening-v1'


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--commit',required=True)
    p.add_argument('--phase',choices=['content','metadata'],required=True);p.add_argument('--attempt',type=int,required=True)
    a=p.parse_args();assert len(a.commit)==40 and all(c in '0123456789abcdef' for c in a.commit) and a.attempt>0
    prefix='reports/solution-review/source92-'+a.phase+'-delivery-attempt'+str(a.attempt)
    assert not h.path(prefix+'.json').exists()
    stamp=datetime.now(timezone.utc).isoformat();observations=[]
    def observe(command,label):
        start=time.monotonic();result=subprocess.run(command,cwd=PUB,capture_output=True)
        name=prefix+'-'+label+'.log';h.put(name,result.stdout+result.stderr)
        observations.append({'command':command,'cwd':str(PUB),'exit_code':result.returncode,
            'elapsed_seconds':time.monotonic()-start,'log':h.ref(name)})
        return result
    result=observe(['git','ls-remote','origin','refs/heads/main'],'remote')
    remote=result.stdout.split()[0].decode() if result.returncode==0 and result.stdout.split() else None
    def fetch(item):
        name,digest=item;url='https://ploxkevin.github.io/'+name+'?source92='+a.commit[:12]+'&checked='+stamp
        row={'file':name,'expected_sha256':digest,'url':url}
        try:
            request=urllib.request.Request(url,headers={'Cache-Control':'no-cache'})
            with urllib.request.urlopen(request,timeout=30) as response:
                row.update(http_status=response.status,actual_sha256=hashlib.sha256(response.read()).hexdigest())
            row['matches']=row['http_status']==200 and row['actual_sha256']==digest
        except Exception as e:row.update(matches=False,error=str(e))
        return row
    plan=h.read(BASE+'/plan-v1.json')
    with ThreadPoolExecutor(max_workers=8) as pool:assets=list(pool.map(fetch,sorted(plan['site_after_sha256'].items())))
    result=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'],'pages')
    pages=json.loads(result.stdout) if result.returncode==0 else {}
    result=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs?per_page=15'],'runs')
    runs=json.loads(result.stdout).get('workflow_runs',[]) if result.returncode==0 else []
    runs=[r for r in runs if r['head_sha']==a.commit and r['name']=='pages build and deployment']
    run=max(runs,key=lambda r:r['id']) if runs else None;jobs=[]
    if run:
        result=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs/'+str(run['id'])+'/jobs'],'jobs')
        jobs=json.loads(result.stdout).get('jobs',[]) if result.returncode==0 else []
    passed=(remote==a.commit and len(assets)==31 and all(r['matches'] for r in assets)
        and pages.get('status')=='built' and pages.get('commit')==a.commit
        and run and run['status']=='completed' and run['conclusion']=='success'
        and len(jobs)==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs))
    report={'status':'passed_all31_live_assets_and_all3_Pages_jobs' if passed else 'delivery_not_yet_verified',
        'checked_at_utc':stamp,'expected_commit':a.commit,'phase':a.phase,'remote_main':remote,
        'plan':h.ref(BASE+'/plan-v1.json'),'assets':assets,'Pages_build':pages,'selected_run':run,'jobs':jobs,
        'observations':observations,'full_formal_coverage_complete':False,'helper':h.ref(BASE+'/verify_delivery.py')}
    h.json_put(prefix+'.json',report)
    print(json.dumps({'status':report['status'],'commit':a.commit,'matching_assets':sum(r['matches'] for r in assets),
        'successful_jobs':sum(r.get('conclusion')=='success' for r in jobs),'report':h.ref(prefix+'.json')}))
    return 0 if passed else 1


if __name__=='__main__':raise SystemExit(main())
