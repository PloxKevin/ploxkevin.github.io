"""Exercise actual release functions in disposable files, including late edits.

The loader is stubbed only for installation-fixture isolation. No fixture
authorizes teaching content or writes canonical pages.
"""
import argparse
import copy
import fcntl
import json
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
import solution_release as release


def refs(files):
    return [review.ref(f) for f in files]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    protected = [Path(__file__).relative_to(ROOT).as_posix(), release.HERE,
                 'book/solutions/test_solution_release.py',
                 'book/solutions/solution_review.py', 'book/validate.py', 'qa/check.mjs',
                 'SafeLearning/primer-linalg.html', 'book/chapters/primer-linalg.html']
    before = refs(protected)
    cases = []
    pending = copy.deepcopy(review.read(review.BASELINE + '/review-tracker.json'))
    pending['exercises'][0]['status'] = 'pending_pedagogical_review'
    try:
        release.approved_selection(pending)
    except AssertionError as error:
        assert str(error) == 'Some solutions still need independent review'
        cases.append(dict(case='actual_pending_review_gate', status='passed'))
    else:
        raise AssertionError('Pending exercise was approved')
    real_root, loader, copier = review.ROOT, release.load_plan, release.atomic_copy
    try:
        for scenario in ['replace_failure', 'post_replace_interruption', 'concurrent_lock', 'late_edit']:
            with tempfile.TemporaryDirectory(prefix='.independent-release-' + scenario + '-',
                                             dir=ROOT / 'book/solutions') as temp:
                review.ROOT = Path(temp)
                plan = dict(files=[], site_source90_sha256={}, site_source91_sha256={},
                            counts=dict(fixture_files=2))
                for i in range(2):
                    name = 'SafeLearning/fixture' + str(i) + '.html'
                    old, new = ('before' + str(i)).encode(), ('after' + str(i)).encode()
                    target = review.ROOT / name
                    target.parent.mkdir(exist_ok=True); target.write_bytes(old)
                    old_name, new_name = release.RELEASE + '/before' + str(i), release.RELEASE + '/after' + str(i)
                    review.put(old_name, old); review.put(new_name, new)
                    plan['files'].append(dict(file=name, before=review.ref(old_name), after=review.ref(new_name),
                                             before_sha256=review.sha(old), after_sha256=review.sha(new)))
                    plan['site_source90_sha256'][name] = review.sha(old)
                    plan['site_source91_sha256'][name] = review.sha(new)
                review.json_put(release.PLAN, plan)
                release.load_plan = lambda fingerprint: plan
                first, second = [review.path(r['file']) for r in plan['files']]
                final = review.path('reports/solution-review/release-source91-installation-v1.json')
                if scenario == 'replace_failure':
                    native_replace = release.os.replace
                    def fail_replace(source, target):
                        raise OSError('Injected replacement failure')
                    release.os.replace = fail_replace
                    try:
                        release.apply('fixture')
                    except OSError as error:
                        assert str(error) == 'Injected replacement failure'
                    else:
                        raise AssertionError('Replacement injection did not fire')
                    finally:
                        release.os.replace = native_replace
                    assert first.read_bytes() == b'before0' and second.read_bytes() == b'before1'
                    assert not final.exists()
                    assert not list(first.parent.glob('.fixture*-*')), 'Abandoned temporary file'
                    cases.append(dict(case='actual_atomic_replace_failure_preserves_old_and_cleans_temp', status='passed'))
                elif scenario == 'post_replace_interruption':
                    fired = False
                    def interrupt_after_first(target, data):
                        nonlocal fired
                        copier(target, data)
                        if not fired:
                            fired = True
                            raise RuntimeError('Injected interruption after completed replacement')
                    release.atomic_copy = interrupt_after_first
                    try:
                        release.apply('fixture')
                    except RuntimeError as error:
                        assert str(error).startswith('Injected interruption')
                    else:
                        raise AssertionError('Post-replacement interruption did not fire')
                    assert first.read_bytes() == b'after0' and second.read_bytes() == b'before1'
                    assert not final.exists()
                    assert not review.path(release.RELEASE + '/installation/00.json').exists()
                    release.atomic_copy = copier
                    release.apply('fixture')
                    saved = final.read_bytes()
                    release.apply('fixture')
                    assert first.read_bytes() == b'after0' and second.read_bytes() == b'after1'
                    assert final.read_bytes() == saved
                    cases.append(dict(case='post_replace_pre_receipt_interruption_resumes_and_completed_receipt_is_immutable', status='passed'))
                elif scenario == 'concurrent_lock':
                    lock_path = review.path(release.RELEASE + '/installation.lock', writable=True)
                    with lock_path.open('a') as lock:
                        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        try:
                            release.apply('fixture')
                        except BlockingIOError:
                            pass
                        else:
                            raise AssertionError('Simultaneous installation was not refused')
                    assert first.read_bytes() == b'before0' and second.read_bytes() == b'before1'
                    assert not final.exists()
                    cases.append(dict(case='actual_flock_refuses_second_installation_without_mutation', status='passed'))
                else:
                    def edit_after_first(target, data):
                        copier(target, data)
                        if target == first:
                            second.write_bytes(b'new user edit after preflight')
                    release.atomic_copy = edit_after_first
                    refused = False
                    try:
                        release.apply('fixture')
                    except AssertionError:
                        refused = True
                    preserved = second.read_bytes() == b'new user edit after preflight'
                    safe = refused and preserved and not final.exists() and first.read_bytes() == b'after0'
                    cases.append(dict(case='late_edit_after_preflight_must_not_be_overwritten',
                        status='passed' if safe else 'confirmed_defect',
                        refused=refused, unexpected_second_file_preserved=preserved,
                        first_file_is_complete=first.read_bytes() == b'after0',
                        final_success_record_exists=final.exists(),
                        actual_second_file=second.read_bytes().decode()))
                release.atomic_copy = copier
    finally:
        review.ROOT = real_root; release.load_plan = loader; release.atomic_copy = copier
    after = refs(protected)
    assert before == after, 'Real protected source changed'
    defects = [c for c in cases if c['status'] != 'passed']
    result = dict(status='needs_release_pipeline_revision' if defects else 'passed_independent_release_failure_injections',
        helper=review.ref(Path(__file__).relative_to(ROOT).as_posix()),
        release_helper=review.ref(release.HERE), cases=cases, defects=defects,
        protected_inputs_before=before, protected_inputs_after=after,
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT),
        canonical_sources_modified=False, formal_or_pedagogical_approval_from_fixtures_claimed=False)
    review.json_put(args.report, result)
    print(json.dumps(dict(status=result['status'], cases=len(cases), defects=len(defects), report=review.ref(args.report))))
    return 1 if defects else 0


if __name__ == '__main__':
    raise SystemExit(main())
