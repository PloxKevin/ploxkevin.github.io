"""Plan and atomically stage exact approved solution bytes in the publication checkout.

No Git mutation is performed. Root commits/pushes only after checking the exact
plan and staged diff. An interrupted copy accepts only planned before/after bytes.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

import solution_review as review
import solution_release as release

ROOT=review.ROOT
PUB=ROOT/'reports/book/publication-repo'


def target(name):
    p=Path(name)
    assert name and not p.is_absolute() and p.as_posix()==name
    assert not {'..','.git','.lake','__pycache__','source-objects'}.intersection(p.parts)
    assert not any(part.startswith(('runtime-','isolated-runtime','archive')) for part in p.parts)
    assert not p.name.endswith(('.pyc','.lock','.olean','.ilean','.o','.trace'))
    result=PUB/p
    assert result.resolve().is_relative_to(PUB) and not result.is_symlink()
    assert all(not q.is_symlink() for q in result.parents if q.is_relative_to(PUB))
    return result


def git(args):
    result=subprocess.run(['git',*args],cwd=PUB,capture_output=True)
    assert result.returncode==0,result.stderr.decode()
    return result.stdout


def current(path):
    return review.sha(path.read_bytes()) if path.is_file() else None


def dirty():
    result={}
    for row in git(['status','--porcelain','-z','--untracked-files=all']).split(b'\0'):
        if not row:continue
        assert len(row)>3 and row[2:3]==b' ' and row[:2].decode() in {' M','M ','MM','A ','??'},'Unexpected deletion/rename/index state'
        result[row[3:].decode()]=row[:2].decode()
    return result


def prepare(args):
    assert git(['symbolic-ref','--short','HEAD']).decode().strip()=='main'
    assert git(['rev-parse','HEAD']).decode().strip()==args.expected_head
    assert not dirty(),'Publication checkout has unrelated edits'
    ready=review.read(args.ready)
    assert ready['status'] in {'passed_source91_all556_release_ready_for_publication','passed_source91_content_delivered_metadata_ready'}
    files=review.read(args.files)
    assert isinstance(files,list) and 0<len(files)<5000 and len(files)==len(set(files))
    records=[]
    for name in sorted(files):
        source=review.path(name);destination=target(name)
        assert source.is_file() and source.stat().st_size<95_000_000,name
        records.append({'file':name,'sha256':review.sha(source.read_bytes()),'before_sha256':current(destination)})
    plan={'schema':'solution-publication.stage.v1','status':'ready_exact_solution_publication_stage',
          'phase':args.phase,'expected_publication_head':args.expected_head,'release_ready':review.ref(args.ready),
          'input_file_list':review.ref(args.files),'helper':review.ref(Path(__file__).relative_to(ROOT).as_posix()),
          'files':records,'includes_runtime_or_cache':False,'Git_commit_push_or_live_delivery_claimed':False}
    review.json_put(args.plan,plan)
    print(json.dumps({'plan':review.ref(args.plan),'files':len(records),'bytes':sum(review.path(r['file']).stat().st_size for r in records)}))


def apply(args):
    assert review.ref(args.plan)['sha256']==args.plan_sha256
    plan=review.read(args.plan)
    assert plan['status']=='ready_exact_solution_publication_stage'
    assert git(['symbolic-ref','--short','HEAD']).decode().strip()=='main'
    assert git(['rev-parse','HEAD']).decode().strip()==plan['expected_publication_head']
    release.exact(plan['release_ready']);release.exact(plan['helper']);release.exact(plan['input_file_list'])
    intended={r['file']:r for r in plan['files']}
    assert set(dirty())<=set(intended)|{args.plan},'Unrelated dirty file in publication checkout'
    for row in plan['files']:
        assert review.ref(row['file'])['sha256']==row['sha256'],row['file']
        assert current(target(row['file'])) in {row['before_sha256'],row['sha256']},row['file']
    plan_destination=target(args.plan)
    assert current(plan_destination) in {None,args.plan_sha256},'Conflicting publication plan'
    for row in plan['files']:
        destination=target(row['file']);destination.parent.mkdir(parents=True,exist_ok=True)
        if current(destination)!=row['sha256']:
            release.atomic_copy(destination,review.path(row['file']).read_bytes())
    plan_destination.parent.mkdir(parents=True,exist_ok=True)
    if not plan_destination.exists():release.atomic_copy(plan_destination,review.path(args.plan).read_bytes())
    assert all(current(target(r['file']))==r['sha256'] for r in plan['files'])
    assert set(dirty())<=set(intended)|{args.plan}
    report={'status':'passed_exact_solution_publication_staging','plan':review.ref(args.plan),
            'expected_head':plan['expected_publication_head'],'files':len(plan['files']),
            'actual_dirty_files':dirty(),'Git_commit_push_or_live_delivery_claimed':False}
    review.json_put(args.report,report)
    print(json.dumps({'status':report['status'],'files':len(plan['files']),'dirty_files':len(report['actual_dirty_files']),'report':review.ref(args.report)}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['prepare','apply'])
    parser.add_argument('--phase',choices=['content','metadata'])
    parser.add_argument('--expected-head')
    parser.add_argument('--ready')
    parser.add_argument('--files')
    parser.add_argument('--plan',required=True)
    parser.add_argument('--plan-sha256')
    parser.add_argument('--report')
    args=parser.parse_args()
    if args.action=='prepare':
        assert all([args.phase,args.expected_head,args.ready,args.files]);prepare(args)
    else:
        assert args.plan_sha256 and args.report;apply(args)


if __name__=='__main__':main()
