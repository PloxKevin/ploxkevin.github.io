"""Exercise interruption/resume and preflight refusal in a disposable fixture.

The fixture bypasses review loading to isolate installation behavior; it never
approves a curriculum answer or changes actual teaching sources.
"""
import argparse
import copy
import json
from pathlib import Path
import tempfile

import solution_review as review
import solution_release as release


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    original_root=review.ROOT
    protected={n:review.ref(n)['sha256'] for n in ['SafeLearning/primer-linalg.html','book/chapters/primer-linalg.html',release.HERE]}
    cases=[]
    # The real current queue cannot approve a release while a row is pending.
    tracker=review.read(review.BASELINE+'/review-tracker.json')
    pending=copy.deepcopy(tracker)
    pending['exercises'][0]['status']='pending_pedagogical_review'
    try:
        release.approved_selection(pending)
    except AssertionError as error:
        assert str(error)=='Some solutions still need independent review'
        cases.append({'case':'pending_review_refused','status':'passed'})
    else:
        raise AssertionError('Pending review was accepted')
    loader,copy_file=release.load_plan,release.atomic_copy
    with tempfile.TemporaryDirectory(prefix='.release-interruption-fixture-',dir=original_root/'book/solutions') as directory:
        review.ROOT=Path(directory)
        try:
            plan={'files':[],'site_source90_sha256':{},'site_source91_sha256':{},'counts':{'fixture_files':2}}
            for i in range(2):
                name='SafeLearning/fixture'+str(i)+'.html';old=('original'+str(i)).encode();new=('expanded'+str(i)).encode()
                path=review.ROOT/name;path.parent.mkdir(exist_ok=True);path.write_bytes(old)
                before=release.RELEASE+'/old'+str(i);after=release.RELEASE+'/new'+str(i)
                review.put(before,old);review.put(after,new)
                plan['files'].append({'file':name,'before':review.ref(before),'after':review.ref(after),
                                     'before_sha256':review.sha(old),'after_sha256':review.sha(new)})
                plan['site_source90_sha256'][name]=review.sha(old);plan['site_source91_sha256'][name]=review.sha(new)
            review.json_put(release.PLAN,plan)
            release.load_plan=lambda fingerprint:plan
            second=review.path(plan['files'][1]['file'])
            second.write_bytes(b'unexpected user edit')
            try:
                release.apply('fixture')
            except AssertionError:
                assert review.ref(plan['files'][0]['file'])['sha256']==plan['files'][0]['before_sha256']
                cases.append({'case':'unexpected_later_file_refused_before_any_mutation','status':'passed'})
            else:
                raise AssertionError('Unexpected bytes accepted')
            second.write_bytes(release.exact(plan['files'][1]['before']).read_bytes())
            def interrupt_second(target,data):
                if target==second:
                    raise RuntimeError('Simulated interruption before the second atomic replacement')
                copy_file(target,data)
            release.atomic_copy=interrupt_second
            try:
                release.apply('fixture')
            except RuntimeError as error:
                assert str(error).startswith('Simulated interruption')
                assert review.ref(plan['files'][0]['file'])['sha256']==plan['files'][0]['after_sha256']
                assert review.ref(plan['files'][1]['file'])['sha256']==plan['files'][1]['before_sha256']
                assert not review.path('reports/solution-review/release-source91-installation-v1.json').exists()
                cases.append({'case':'interruption_retains_first_complete_file_and_no_success_claim','status':'passed'})
            else:
                raise AssertionError('Interruption fixture did not run')
            release.atomic_copy=copy_file
            release.apply('fixture')
            assert all(review.ref(r['file'])['sha256']==r['after_sha256'] for r in plan['files'])
            cases.append({'case':'mixed_before_after_state_resumes_to_exact_selected_bytes','status':'passed'})
            receipt=review.path('reports/solution-review/release-source91-installation-v1.json').read_bytes()
            release.apply('fixture')
            assert review.path('reports/solution-review/release-source91-installation-v1.json').read_bytes()==receipt
            cases.append({'case':'completed_installation_rerun_keeps_receipt_bytes','status':'passed'})
        finally:
            review.ROOT=original_root
            release.load_plan=loader;release.atomic_copy=copy_file
    assert protected=={n:review.ref(n)['sha256'] for n in protected}
    result={'status':'passed_release_interruption_and_refusal_fixtures','cases':cases,
            'helper':review.ref(release.HERE),'test':review.ref(Path(__file__).relative_to(original_root).as_posix()),
            'actual_curriculum_sources_unchanged':True,'pedagogical_approval_claimed':False,
            'scope':'Disposable two-file installation fixture and real pending-review refusal; no synthetic solution text is adopted.'}
    review.json_put(args.report,result)
    print(json.dumps({'status':result['status'],'cases':len(cases),'report':review.ref(args.report)}))


if __name__=='__main__':
    main()
