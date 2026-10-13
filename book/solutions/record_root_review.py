"""Bind Root's exercise-specific manual review notes to exact selected bytes.

Approval comes from explicit notes written after reading each exercise. This
helper checks identities and completeness; it does not evaluate answer depth.
"""
import argparse
import hashlib
import json
from datetime import datetime,timezone
from pathlib import Path
import solution_review as review

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['draft','notes','preservation','report']:parser.add_argument('--'+key,required=True)
    args=parser.parse_args()
    manifest,baseline=review.load(review.BASELINE)
    index={e['inventory_key']:e for e in baseline}
    draft=review.read(args.draft)
    if isinstance(draft,dict):
        groups=[draft[k] for k in ['exercises','solutions','proposals'] if k in draft]
        assert len(groups)==1;draft=groups[0]
    notes=review.read(args.notes)
    assert isinstance(notes,list)
    decisions={e['inventory_key']:e for e in draft}
    handwritten={e['inventory_key']:e for e in notes}
    assert len(decisions)==len(draft)==len(handwritten)==len(notes)
    assert decisions.keys()==handwritten.keys()
    pages={index[k]['source_file'] for k in decisions}
    assert len(pages)==1
    assert set(decisions)=={e['inventory_key'] for e in baseline if e['source_file'] in pages}
    preservation=review.read(args.preservation)
    assert preservation['status']=='passed_explicit_solution_draft_preservation'
    assert any(r['file']==args.draft and r['sha256']==review.ref(args.draft)['sha256'] for r in preservation['drafts'])
    candidates=[]
    for r in preservation['candidates']:
        assert review.ref(r['candidate_file'])['sha256']==r['sha256']
        candidates.append(review.ref(r['candidate_file']))
    rows=[];issues=[]
    for key,decision in decisions.items():
        e=index[key];note=handwritten[key]
        assert decision['original_solution_sha256']==e['solution']['sha256']
        body=decision.get('replacement_html',e['solution']['html'])
        if decision['decision']=='retain':assert body==e['solution']['html']
        else:assert decision['decision']=='replace' and review.sha(body.encode())!=e['solution']['sha256']
        assert note['verdict'] in {'approved','needs_revision'} and note['reasoning']
        row=dict(note,ordinal=e['ordinal'],decision=decision['decision'],original_solution_sha256=e['solution']['sha256'],
                 selected_solution_sha256=review.sha(body.encode()))
        row.setdefault('issues',[])
        if note['verdict']=='approved':
            assert not row['issues']
            row.update(all_requested_parts_addressed=True,mathematics_and_assumptions_checked=True,reader_depth_checked=True)
        else:issues.append({'inventory_key':key,'reason':note['reasoning']})
        rows.append(row)
    result={'schema_version':1,'status':'approved_all_selected_solutions' if not issues else 'needs_revision',
            'reviewer':'/root independent of page author','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
            'draft':review.ref(args.draft),'manual_review_notes':review.ref(args.notes),
            'baseline':review.ref(review.BASELINE+'/pages/'+next(iter(pages)).split('/')[-1]+'.json'),
            'preservation':review.ref(args.preservation),'candidate_files':candidates,
            'criteria':review.ref('book/solutions/README.md'),'page_contract':review.ref('page_contract.md'),
            'counts':{'exercises':len(rows),'approved':len(rows)-len(issues),'needs_revision':len(issues)},
            'method':'Root read the complete questions and selected solutions, checked each requested part, computations/proofs, relevant hypotheses and student-followable reasoning. Manual notes encode these specific findings; this helper only binds their identities.',
            'exercises':rows,'issues':issues,'canonical_sources_modified':False,'formal_verification_claimed':False}
    review.json_put(args.report,result)
    print(json.dumps({'report':review.ref(args.report),'status':result['status'],'counts':result['counts']}))

if __name__=='__main__':main()
