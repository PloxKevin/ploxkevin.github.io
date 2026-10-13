"""Adopt explicit, hash-bound independent draft reviews into the review queue.

This updates review status only. It never changes teaching sources or formal
coverage and cannot infer pedagogical approval from a preservation check.
"""
import argparse
import copy
import hashlib
import json
import os
import tempfile
from collections import Counter
from datetime import datetime,timezone
from pathlib import Path
import solution_review as review

def sha(data):return hashlib.sha256(data).hexdigest()
def atomic(path,data):
    fd,tmp=tempfile.mkstemp(prefix='.'+path.name+'-',dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as stream:
            stream.write(data);stream.flush();os.fsync(stream.fileno())
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--review',action='append',required=True)
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    tracker_name=review.BASELINE+'/review-tracker.json'
    tracker_path=review.path(tracker_name)
    before=tracker_path.read_bytes();tracker=json.loads(before)
    manifest,baseline=review.load(review.BASELINE)
    assert tracker['baseline']==review.ref(review.BASELINE+'/manifest.json')
    index={e['inventory_key']:e for e in baseline}
    queue={e['inventory_key']:e for e in tracker['exercises']}
    assert len(queue)==len(index)==556
    adopted=[];seen=set()
    for name in args.review:
        report=review.read(name);report_ref=review.ref(name)
        assert str(report['status']).startswith('approved'),name
        assert not report.get('issues') and not report.get('errors'),name
        draft_ref=report['draft'];assert review.ref(draft_ref['file'])['sha256']==draft_ref['sha256']
        value=review.read(draft_ref['file'])
        if isinstance(value,dict):
            found=[value[k] for k in ['exercises','solutions','proposals'] if k in value]
            assert len(found)==1;value=found[0]
        proposals={e['inventory_key']:e for e in value}
        groups=[report[k] for k in ('exercises','exercise_reviews') if k in report]
        assert len(groups)==1,'Independent review must contain one explicit exercise list'
        review_rows=groups[0]
        reviewed={e['inventory_key']:e for e in review_rows}
        assert len(proposals)==len(value)==len(reviewed)==len(review_rows)
        assert proposals.keys()==reviewed.keys(),name
        for key,decision in proposals.items():
            assert key not in seen,'Conflicting independent review: '+key
            seen.add(key);source=index[key];item=reviewed[key]
            assert decision['source_file']==source['source_file']
            assert decision['original_solution_sha256']==source['solution']['sha256']
            assert item.get('verdict',item.get('decision_verdict'))=='approved',key
            assert decision['decision']==item['decision'] and decision['decision'] in {'retain','replace'}
            body=decision.get('replacement_html',source['solution']['html'])
            if decision['decision']=='retain':assert body==source['solution']['html']
            else:assert isinstance(body,str) and sha(body.encode())!=source['solution']['sha256']
            selected_hash=sha(body.encode())
            assert item.get('selected_solution_sha256',item.get('reviewed_solution_sha256'))==selected_hash,key
            rationale=item.get('reasoning') or item.get('depth_review')
            assert rationale and decision['thoroughness_rationale'],key
            assert not item.get('issues') and not item.get('errors') and not item.get('remaining_gaps'),key
            row=queue[key]
            row.update(status='independently_approved_draft_pending_adoption',decision=decision['decision'],
                       exercise_specific_rationale=decision['thoroughness_rationale'],
                       independent_reasoning=rationale,selected_solution_sha256=selected_hash,
                       draft=copy.deepcopy(draft_ref),independent_review=report_ref,
                       review_family='manual_mathematics_and_student_depth')
            for criterion in row['criteria'].values():
                criterion.update(status='approved_in_independent_review',evidence={'review':report_ref,'inventory_key':key})
        adopted.append(report_ref)
    counts=Counter(e['status'] for e in tracker['exercises'])
    tracker['updated_at_utc']=datetime.now(timezone.utc).isoformat()
    tracker['counts']=dict(counts)
    tracker['canonical_adoption_claimed']=False
    tracker['formal_coverage_changed']=False
    data=(json.dumps(tracker,indent=2,ensure_ascii=False)+'\n').encode()
    evidence={'status':'passed_explicit_independent_review_queue_update',
              'tracker_before_sha256':sha(before),'tracker_after_sha256':sha(data),
              'adopted_review_records':adopted,'explicitly_reviewed_this_update':len(seen),
              'counts':dict(counts),'canonical_sources_modified':False,'formal_coverage_changed':False,
              'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix())}
    # Validate every record before any mutation, and preserve the prior queue.
    report_path=review.path(args.report,writable=True);assert not report_path.exists()
    previous='book/solutions/tracker-history/'+sha(before)+'.json'
    review.put(previous,before);evidence['prior_tracker']=review.ref(previous)
    review.json_put(args.report,evidence)
    assert tracker_path.read_bytes()==before,'Tracker changed concurrently'
    atomic(tracker_path,data)
    print(json.dumps({'report':review.ref(args.report),'counts':dict(counts)}))

if __name__=='__main__':main()
