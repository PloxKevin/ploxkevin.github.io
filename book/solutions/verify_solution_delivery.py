"""Verify every Source91 site asset and actual GitHub Pages jobs in a fresh attempt."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time
import urllib.request

import solution_review as review
import solution_release as release

PUB=review.ROOT/'reports/book/publication-repo'


def observe(command,label,report_root):
    start=time.monotonic()
    result=subprocess.run(command,cwd=PUB,capture_output=True)
    name=report_root+'-'+label+'.log';review.put(name,result.stdout+result.stderr)
    return result,{'actual_command':command,'actual_workdir':str(PUB),'actual_exit_code':result.returncode,
                   'elapsed_seconds':time.monotonic()-start,'log':review.ref(name)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan-sha256',required=True)
    parser.add_argument('--commit',required=True)
    parser.add_argument('--phase',choices=['content','metadata'],required=True)
    parser.add_argument('--attempt',type=int,required=True)
    args=parser.parse_args()
    assert len(args.commit)==40 and all(c in '0123456789abcdef' for c in args.commit) and args.attempt>0
    plan=release.load_plan(args.plan_sha256)
    prefix='reports/solution-review/source91-'+args.phase+'-delivery-attempt'+str(args.attempt)
    assert not review.path(prefix+'.json').exists()
    stamp=datetime.now(timezone.utc).isoformat()
    remote,remote_record=observe(['git','ls-remote','origin','refs/heads/main'],'remote',prefix)
    remote_head=remote.stdout.split()[0].decode() if remote.returncode==0 and remote.stdout.split() else None
    def fetch(item):
        name,expected=item
        url='https://ploxkevin.github.io/'+name+'?source91='+args.commit[:12]+'&checked='+stamp
        row={'source':name,'url':url,'expected_sha256':expected};start=time.monotonic()
        try:
            request=urllib.request.Request(url,headers={'Cache-Control':'no-cache'})
            with urllib.request.urlopen(request,timeout=30) as response:
                row.update(http_status=response.status,actual_sha256=hashlib.sha256(response.read()).hexdigest())
            row['matches']=row['http_status']==200 and row['actual_sha256']==expected
        except Exception as error:
            row.update(matches=False,error=str(error))
        row['elapsed_seconds']=time.monotonic()-start
        return row
    with ThreadPoolExecutor(max_workers=8) as pool:
        assets=list(pool.map(fetch,sorted(plan['site_source91_sha256'].items())))
    pages,pages_record=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'],'pages-build',prefix)
    build=json.loads(pages.stdout) if pages.returncode==0 else {}
    runs,runs_record=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs?per_page=15'],'actions-runs',prefix)
    data=json.loads(runs.stdout) if runs.returncode==0 else {}
    matches=[r for r in data.get('workflow_runs',[]) if r['head_sha']==args.commit and r['name']=='pages build and deployment']
    jobs=[];jobs_record=None;run=None
    if matches:
        run=max(matches,key=lambda r:r['id'])
        result,jobs_record=observe(['gh','api','repos/PloxKevin/ploxkevin.github.io/actions/runs/'+str(run['id'])+'/jobs'],'actions-jobs',prefix)
        jobs=json.loads(result.stdout).get('jobs',[]) if result.returncode==0 else []
    passed=(remote_head==args.commit and len(assets)==31 and all(r['matches'] for r in assets)
            and build.get('status')=='built' and build.get('commit')==args.commit
            and run is not None and run['status']=='completed' and run['conclusion']=='success'
            and len(jobs)==3 and all(r['status']=='completed' and r['conclusion']=='success' for r in jobs))
    report={'status':'passed_source91_all31_live_assets_and_all3_Pages_jobs' if passed else 'delivery_not_yet_verified',
            'checked_at_utc':stamp,'expected_commit':args.commit,'remote_main':remote_head,'phase':args.phase,
            'plan':review.ref(release.PLAN),'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),
            'assets':assets,'remote_observation':remote_record,'Pages_build_observation':pages_record,
            'Pages_build':build,'actions_runs_observation':runs_record,'actions_jobs_observation':jobs_record,
            'selected_run':run,'jobs':jobs,'coverage_complete':False,
            'formal_source_correspondence_for_rewritten_answers':'pending_explicit_rebase'}
    review.json_put(prefix+'.json',report)
    print(json.dumps({'status':report['status'],'matching_assets':sum(r['matches'] for r in assets),
                      'successful_jobs':sum(r['conclusion']=='success' for r in jobs),'report':review.ref(prefix+'.json')}))
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
