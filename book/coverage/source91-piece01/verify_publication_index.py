"""Require the publication index and worktree to contain every exact planned file."""
import argparse
import hashlib
import json
import subprocess

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3]/'book/solutions'))
import solution_review as review
import common as piece_records
import stage_publication as staging


def git(args):
    result=subprocess.run(['git',*args],cwd=staging.PUB,capture_output=True)
    assert result.returncode==0,result.stderr.decode()
    return result.stdout


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan',required=True)
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    plan=review.read(args.plan)
    assert plan['status']=='ready_exact_solution_publication_stage'
    assert git(['rev-parse','HEAD']).decode().strip()==plan['expected_publication_head']
    assert git(['symbolic-ref','--short','HEAD']).decode().strip()=='main'
    rows={r['file']:r['sha256'] for r in plan['files']}
    rows[args.plan]=review.ref(args.plan)['sha256']
    changed={s.decode() for s in git(['diff','--cached','--name-only','-z']).split(b'\0') if s}
    assert changed and changed<=set(rows),'Unplanned index changes'
    assert set(staging.dirty())<=set(rows),'Unplanned worktree changes'
    index={}
    for raw in git(['ls-files','--stage','-z']).split(b'\0'):
        if not raw:continue
        metadata,name=raw.split(b'\t',1);mode,oid,stage=metadata.split()
        assert stage==b'0','Unmerged index'
        index[name.decode()]=(mode.decode(),oid.decode())
    algorithm=git(['rev-parse','--show-object-format']).decode().strip()
    assert algorithm in {'sha1','sha256'}
    for name,expected in rows.items():
        data=review.path(name).read_bytes()
        assert review.sha(data)==expected and review.sha(staging.target(name).read_bytes())==expected,name
        assert name in index and index[name][0] in {'100644','100755'},'Missing planned index file: '+name
        blob=b'blob '+str(len(data)).encode()+b'\0'+data
        assert hashlib.new(algorithm,blob).hexdigest()==index[name][1],'Index bytes differ: '+name
    report={'status':'passed_exact_planned_publication_index_and_worktree','plan':review.ref(args.plan),
        'planned_files_including_plan':len(rows),'actual_changed_index_files':len(changed),
        'expected_head':plan['expected_publication_head'],'object_format':algorithm,
        'commit_push_or_delivery_claimed':False}
    piece_records.json_put(args.report,report)
    print(json.dumps(report))


if __name__=='__main__':main()
