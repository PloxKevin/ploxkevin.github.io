"""Inject missing/corrupt/declined approvals into an isolated complete queue.

The actual release selector runs with only baseline loading replaced by 556
synthetic identity rows. These fixtures never approve real exercise content.
"""
import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
import solution_release as release


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    protected = [Path(__file__).relative_to(ROOT).as_posix(), release.HERE,
                 'book/solutions/solution_review.py']
    before = [review.ref(p) for p in protected]
    original_root, original_loader = review.ROOT, review.load
    cases = []
    try:
        with tempfile.TemporaryDirectory(prefix='.approval-identity-fixture-', dir=ROOT / 'book/solutions') as temp:
            review.ROOT = Path(temp)
            review.json_put(review.BASELINE + '/manifest.json', {'scope': 'synthetic identity fixture only'})
            baseline, groups = [], [[] for _ in range(22)]
            for i in range(556):
                source = 'SafeLearning/fixture-page-' + str(i % 22) + '.html'
                key = source + '#fixture-' + str(i)
                old, new = '<p>Original fixture ' + str(i) + '</p>', '<p>Expanded fixture ' + str(i) + '</p>'
                baseline.append(dict(inventory_key=key, source_file=source, solution=dict(html=old, sha256=review.sha(old.encode()))))
                groups[i % 22].append(dict(inventory_key=key, source_file=source,
                    original_solution_sha256=review.sha(old.encode()), decision='replace',
                    thoroughness_rationale='Synthetic identity test; no real pedagogical approval.', replacement_html=new))
            review.load = lambda directory: ({'scope': 'synthetic identity fixture'}, baseline)
            tracker = dict(baseline=review.ref(review.BASELINE + '/manifest.json'), exercises=[])
            report_files = []
            for group_number, proposals in enumerate(groups):
                draft = 'book/solutions/drafts/fixture-' + str(group_number) + '.json'
                report = 'reports/solution-review/fixture-' + str(group_number) + '.json'
                review.json_put(draft, dict(exercises=proposals))
                draft_ref = review.ref(draft)
                findings = [dict(inventory_key=p['inventory_key'], decision='replace', verdict='approved',
                    original_solution_sha256=p['original_solution_sha256'],
                    selected_solution_sha256=review.sha(p['replacement_html'].encode()),
                    reasoning='Synthetic identity finding; not an exercise adequacy decision.', issues=[]) for p in proposals]
                review.json_put(report, dict(status='approved_fixture_identity_checks_only', draft=draft_ref, exercises=findings, issues=[]))
                report_files.append(report)
                for proposal, finding in zip(proposals, findings):
                    tracker['exercises'].append(dict(inventory_key=proposal['inventory_key'],
                        status='independently_approved_draft_pending_adoption', draft=draft_ref,
                        independent_review=review.ref(report), selected_solution_sha256=finding['selected_solution_sha256']))
            selected = release.approved_selection(tracker)
            assert len(selected[1]) == len(selected[4]) == 556 and len(selected[2]) == len(selected[3]) == 22
            cases.append(dict(case='complete_556_identity_rows_and_22_bound_drafts_reviews', status='passed'))
            for scenario in ['pending_status', 'wrong_selected_hash', 'missing_review_row', 'declined_review_verdict', 'corrupt_bound_draft']:
                trial = copy.deepcopy(tracker)
                file = None
                saved = None
                try:
                    if scenario == 'pending_status':
                        trial['exercises'][0]['status'] = 'pending_pedagogical_review'
                    elif scenario == 'wrong_selected_hash':
                        trial['exercises'][0]['selected_solution_sha256'] = '0' * 64
                    elif scenario == 'corrupt_bound_draft':
                        file = review.path(trial['exercises'][0]['draft']['file'])
                        saved = file.read_bytes(); file.write_bytes(b'corrupted draft bytes')
                    else:
                        name = report_files[0]; file = review.path(name); saved = file.read_bytes()
                        data = json.loads(saved)
                        if scenario == 'missing_review_row':
                            data['exercises'].pop()
                        else:
                            data['exercises'][0]['verdict'] = 'needs_revision'
                        file.write_text(json.dumps(data))
                        for row in trial['exercises']:
                            if row['independent_review']['file'] == name:
                                row['independent_review'] = review.ref(name)
                    try:
                        release.approved_selection(trial)
                    except AssertionError as error:
                        cases.append(dict(case=scenario, status='passed', actual_refusal=str(error)))
                    else:
                        raise AssertionError('Unsafe approval queue accepted: ' + scenario)
                finally:
                    if file is not None:
                        file.write_bytes(saved)
    finally:
        review.ROOT = original_root; review.load = original_loader
    after = [review.ref(p) for p in protected]
    assert before == after
    result = dict(status='passed_independent_complete_queue_approval_refusals', cases=cases,
        protected_inputs_before=before, protected_inputs_after=after,
        helper=review.ref(Path(__file__).relative_to(ROOT).as_posix()), release_helper=review.ref(release.HERE),
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT), canonical_sources_modified=False,
        mathematical_or_pedagogical_adequacy_from_synthetic_fixtures_claimed=False)
    review.json_put(args.report, result)
    print(json.dumps(dict(status=result['status'], cases=len(cases), report=review.ref(args.report))))


if __name__ == '__main__':
    main()
