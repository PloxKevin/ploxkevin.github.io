"""Test current publication staging only in disposable Git checkouts.

Temporary Git init/add/commit establishes an isolated baseline for real status
and HEAD checks. The actual publication repository is never written.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
import solution_release as release
import stage_solution_publication as stage


def fixture_git(pub, arguments, commands):
    command = ['git', *arguments]
    result = subprocess.run(command, cwd=pub, capture_output=True, text=True)
    commands.append(dict(argv=command, cwd=str(pub), actual_exit_code=result.returncode))
    assert result.returncode == 0, result.stderr
    return result.stdout.strip()


def make_fixture(root, commands, helper_bytes):
    review.ROOT = root
    stage.PUB = root / 'reports/book/publication-repo'
    stage.PUB.mkdir(parents=True)
    site_hashes = {}
    for i in range(31):
        name = 'SafeLearning/fixture' + str(i).zfill(2) + '.html'
        old = ('original fixture ' + str(i)).encode()
        new = ('reviewed fixture ' + str(i)).encode() if i < 2 else old
        source, destination = root / name, stage.PUB / name
        source.parent.mkdir(exist_ok=True); destination.parent.mkdir(exist_ok=True)
        source.write_bytes(new); destination.write_bytes(old)
        site_hashes[name] = review.sha(new)
    new_file = 'reports/solution-review/synthetic-added.txt'
    review.put(new_file, b'new review fixture\n')
    review.put('book/solutions/stage_solution_publication.py', helper_bytes)
    ready = 'reports/solution-review/fixture-ready.json'
    review.json_put(ready, dict(status='passed_source91_all556_release_ready_for_publication',
                               site_source91_sha256=site_hashes))
    file_list = 'reports/solution-review/fixture-file-list.json'
    review.json_put(file_list, ['SafeLearning/fixture00.html', 'SafeLearning/fixture01.html', new_file])
    fixture_git(stage.PUB, ['init', '-b', 'main'], commands)
    fixture_git(stage.PUB, ['add', 'SafeLearning'], commands)
    head = fixture_git(stage.PUB, ['-c', 'user.name=Isolated Test Fixture',
        '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'Temporary fixture baseline'], commands)
    head = fixture_git(stage.PUB, ['rev-parse', 'HEAD'], commands)
    args = SimpleNamespace(expected_head=head, ready=ready, files=file_list,
        phase='content', plan='reports/solution-review/fixture-stage-plan.json',
        plan_sha256=None, report='reports/solution-review/fixture-stage-applied.json')
    return args


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    protected = [Path(__file__).relative_to(ROOT).as_posix(),
        'book/solutions/stage_solution_publication.py', 'book/solutions/solution_release.py',
        'book/solutions/solution_review.py', 'SafeLearning/style.css', 'SafeLearning/primer-linalg.html']
    refs = lambda: [review.ref(f) for f in protected]
    before = refs()
    commands, cases = [], []
    original_root, original_pub, copier = review.ROOT, stage.PUB, release.atomic_copy
    native_head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=original_pub,
                                 capture_output=True, text=True, check=True).stdout.strip()
    native_status = subprocess.run(['git', 'status', '--porcelain', '-z', '--untracked-files=all'],
                                  cwd=original_pub, capture_output=True, check=True).stdout
    stage_bytes = (ROOT / 'book/solutions/stage_solution_publication.py').read_bytes()
    scenarios = ['path_confinement', 'wrong_head', 'unrelated_edit', 'unexpected_later_destination',
                 'interrupt_resume_replay', 'late_destination_edit', 'late_source_edit',
                 'late_unplanned_site_edit', 'late_plan_destination', 'late_plan_source']
    try:
        for scenario in scenarios:
            with tempfile.TemporaryDirectory(prefix='.publication-independent-' + scenario + '-',
                                             dir=ROOT / 'book/solutions') as directory:
                root = Path(directory)
                task = make_fixture(root, commands, stage_bytes)
                first, second = stage.target('SafeLearning/fixture00.html'), stage.target('SafeLearning/fixture01.html')
                original_first, original_second = first.read_bytes(), second.read_bytes()
                if scenario == 'path_confinement':
                    rejected = []
                    for name in ['../outside', '/outside', '.git/config', '.lake/cache',
                                 'reports/runtime-checkpoint-x/file', 'reports/archive-x/file',
                                 'source-objects/object', 'foo.olean']:
                        try:
                            stage.target(name)
                        except AssertionError:
                            rejected.append(name)
                        else:
                            raise AssertionError('Unsafe destination accepted: ' + name)
                    alias = stage.PUB / 'alias'; alias.symlink_to(root / 'SafeLearning', target_is_directory=True)
                    try:
                        stage.target('alias/fixture00.html')
                    except AssertionError:
                        rejected.append('symlink_parent')
                    else:
                        raise AssertionError('Symlink parent accepted')
                    cases.append(dict(case=scenario, status='passed', rejected=rejected))
                    continue
                if scenario == 'wrong_head':
                    task.expected_head = '0' * 40
                    try:
                        stage.prepare(task)
                    except AssertionError:
                        pass
                    else:
                        raise AssertionError('Wrong HEAD accepted')
                    assert not review.path(task.plan).exists() and first.read_bytes() == original_first
                    cases.append(dict(case=scenario, status='passed'))
                    continue
                stage.prepare(task)
                task.plan_sha256 = review.ref(task.plan)['sha256']
                done = review.path(task.report)
                plan_destination = stage.target(task.plan)
                if scenario == 'unrelated_edit':
                    (stage.PUB / 'unrelated.txt').write_bytes(b'unrelated edit')
                elif scenario == 'unexpected_later_destination':
                    second.write_bytes(b'user edit before initial preflight')
                elif scenario == 'interrupt_resume_replay':
                    def interrupt(target, data):
                        copier(target, data)
                        if target == first:
                            raise RuntimeError('Interrupted after first complete atomic replacement')
                    release.atomic_copy = interrupt
                elif scenario.startswith('late_'):
                    def late(target, data):
                        copier(target, data)
                        if target != first:
                            return
                        if scenario == 'late_destination_edit':
                            second.write_bytes(b'user edit after preflight')
                        elif scenario == 'late_source_edit':
                            review.path('SafeLearning/fixture01.html').write_bytes(b'source changed after preflight')
                        elif scenario == 'late_unplanned_site_edit':
                            stage.target('SafeLearning/fixture30.html').write_bytes(b'unplanned site changed')
                        elif scenario == 'late_plan_destination':
                            plan_destination.parent.mkdir(parents=True, exist_ok=True)
                            plan_destination.write_bytes(b'unexpected destination plan')
                        elif scenario == 'late_plan_source':
                            review.path(task.plan).write_bytes(b'unexpected source plan')
                    release.atomic_copy = late
                refused = False
                try:
                    stage.apply(task)
                except (AssertionError, RuntimeError, json.JSONDecodeError):
                    refused = True
                release.atomic_copy = copier
                if scenario == 'interrupt_resume_replay':
                    assert refused and not done.exists()
                    assert first.read_bytes() == b'reviewed fixture 0' and second.read_bytes() == original_second
                    stage.apply(task); saved = done.read_bytes()
                    calls = []
                    def count_copy(target, data):
                        calls.append(str(target)); copier(target, data)
                    release.atomic_copy = count_copy
                    stage.apply(task)
                    assert not calls and done.read_bytes() == saved
                    assert review.sha(plan_destination.read_bytes()) == task.plan_sha256
                    cases.append(dict(case=scenario, status='passed', replay_copy_calls=len(calls), receipt_immutable=True))
                else:
                    safe = refused and not done.exists()
                    if scenario in {'unrelated_edit', 'unexpected_later_destination'}:
                        safe = safe and first.read_bytes() == original_first
                    if scenario == 'late_destination_edit':
                        safe = safe and second.read_bytes() == b'user edit after preflight'
                    if scenario == 'late_source_edit':
                        safe = safe and second.read_bytes() == original_second
                    if scenario == 'late_plan_destination':
                        safe = safe and plan_destination.read_bytes() == b'unexpected destination plan'
                    cases.append(dict(case=scenario, status='passed' if safe else 'confirmed_defect',
                        refused=refused, final_success_record_exists=done.exists(),
                        destination_plan_sha256=review.sha(plan_destination.read_bytes()) if plan_destination.exists() else None,
                        expected_plan_sha256=task.plan_sha256))
                release.atomic_copy = copier
    finally:
        review.ROOT = original_root; stage.PUB = original_pub; release.atomic_copy = copier
    after = refs(); assert before == after
    assert subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=original_pub,
                          capture_output=True, text=True, check=True).stdout.strip() == native_head
    assert subprocess.run(['git', 'status', '--porcelain', '-z', '--untracked-files=all'],
                          cwd=original_pub, capture_output=True, check=True).stdout == native_status
    defects = [c for c in cases if c['status'] != 'passed']
    result = dict(status='needs_publication_staging_revision' if defects else 'passed_independent_publication_staging_fixtures',
        cases=cases, defects=defects, actual_fixture_git_commands=commands,
        protected_inputs_before=before, protected_inputs_after=after,
        helper=review.ref(Path(__file__).relative_to(ROOT).as_posix()),
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT),
        actual_publication_head_before_and_after=native_head, actual_publication_checkout_written=False,
        canonical_sources_modified=False, pedagogical_or_formal_approval_from_fixtures_claimed=False)
    review.json_put(args.report, result)
    print(json.dumps(dict(status=result['status'], cases=len(cases), defects=len(defects), report=review.ref(args.report))))
    return 1 if defects else 0


if __name__ == '__main__':
    raise SystemExit(main())
