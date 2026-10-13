"""Prepare, install and validate a complete, independently reviewed solution release.

Every output is immutable. Installation accepts only recorded before/after bytes,
so a interrupted page update can be resumed without repeating or losing work.
No formal coverage is inferred from pedagogical review or structural validation.
"""
import argparse
from collections import Counter
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import solution_review as review

ROOT = review.ROOT
HERE = Path(__file__).relative_to(ROOT).as_posix()
RELEASE = 'book/solutions/releases/source91-v1'
PLAN = RELEASE + '/plan.json'
PRIOR_AUDIT = 'reports/full-coverage/runtime-checkpoint-35-source90-v1/reports/lean-verification/verification.json'


def exact(row):
    path=review.path(row['file'])
    assert review.ref(row['file'])['sha256'] == row['sha256'], 'Bound file differs: ' + row['file']
    if 'bytes' in row:
        assert path.stat().st_size == row['bytes'], 'Bound byte count differs: ' + row['file']
    return path


def rows(value):
    if isinstance(value, list):
        return value
    groups = [value[k] for k in ('exercises', 'solutions', 'proposals', 'exercise_reviews') if k in value]
    assert len(groups) == 1, 'Expected one explicit exercise list'
    return groups[0]


def approved_selection(tracker):
    manifest, baseline = review.load(review.BASELINE)
    index = {r['inventory_key']: r for r in baseline}
    queue = {r['inventory_key']: r for r in tracker['exercises']}
    assert len(queue) == len(index) == 556 and queue.keys() == index.keys()
    assert tracker['baseline'] == review.ref(review.BASELINE + '/manifest.json')
    assert all(r['status'] == 'independently_approved_draft_pending_adoption' for r in queue.values()), 'Some solutions still need independent review'
    drafts = {r['draft']['file']: r['draft'] for r in queue.values()}
    reports = {r['independent_review']['file']: r['independent_review'] for r in queue.values()}
    decisions, checked = {}, {}
    for draft in drafts.values():
        exact(draft)
        for row in rows(review.read(draft['file'])):
            key = row['inventory_key']
            assert key not in decisions and key in index
            assert row['source_file'] == index[key]['source_file']
            assert row['original_solution_sha256'] == index[key]['solution']['sha256']
            assert row['decision'] in {'retain', 'replace'} and row['thoroughness_rationale']
            body = row.get('replacement_html', index[key]['solution']['html'])
            if row['decision'] == 'retain':
                assert body == index[key]['solution']['html']
            else:
                assert body.strip() and review.sha(body.encode()) != row['original_solution_sha256']
            assert review.sha(body.encode()) == queue[key]['selected_solution_sha256']
            assert queue[key]['draft'] == draft
            decisions[key] = row
    for report_ref in reports.values():
        exact(report_ref)
        report = review.read(report_ref['file'])
        assert report['status'].startswith('approved') and not report.get('issues') and not report.get('errors')
        exact(report['draft'])
        for item in rows(report):
            key = item['inventory_key']
            assert key not in checked and queue[key]['independent_review'] == report_ref
            assert item.get('verdict', item.get('decision_verdict')) == 'approved'
            assert item['decision'] == decisions[key]['decision']
            assert item['original_solution_sha256'] == decisions[key]['original_solution_sha256']
            assert item.get('selected_solution_sha256', item.get('reviewed_solution_sha256')) == queue[key]['selected_solution_sha256']
            assert item.get('reasoning') or item.get('depth_review')
            assert not item.get('issues') and not item.get('errors') and not item.get('remaining_gaps')
            checked[key] = item
    assert checked.keys() == decisions.keys() == index.keys()
    assert len(drafts) == len(reports) == 22
    return manifest, baseline, sorted(drafts.values(), key=lambda r: r['file']), sorted(reports.values(), key=lambda r: r['file']), decisions


def prepare():
    tracker_name = review.BASELINE + '/review-tracker.json'
    tracker_raw = review.path(tracker_name).read_bytes()
    tracker = json.loads(tracker_raw)
    manifest, baseline, drafts, reports, decisions = approved_selection(tracker)
    prior = review.read(PRIOR_AUDIT)
    assert prior['status'] == 'passed' and prior['proof_file_count'] == 1267 and prior['theorem_count'] == 11472
    original_site = prior['source_sha256']
    assert len(original_site) == 31
    assert all(review.ref(name)['sha256'] == fingerprint for name, fingerprint in original_site.items()), 'Current site no longer matches the Source90 baseline'
    for name, snapshot in manifest['source_snapshots'].items():
        assert review.ref(name)['sha256'] == snapshot['sha256']
        exact(snapshot)
    candidate_dir = RELEASE + '/solution-only-candidates'
    preservation = 'reports/solution-review/release-source91-solution-only-preservation-v1.json'
    command = [sys.executable, '-B', str(ROOT / 'book/solutions/validate_solution_draft.py')]
    for draft in drafts:
        command += ['--draft', draft['file']]
    command += ['--output-dir', candidate_dir, '--report', preservation, '--require-complete-pages']
    subprocess.run(command, cwd=ROOT, check=True)
    candidate_report = review.read(preservation)
    assert len(candidate_report['retained']) + len(candidate_report['replaced']) == 556
    candidates = {r['source_file']: r for r in candidate_report['candidates']}
    # A broken TeX delimiter in an uncounted readiness question is a separate,
    # exact formatting exception, not a solution rewrite or a new exercise.
    repairs = [{'source_file': 'SafeLearning/toolkit-gp.html',
                'before': 'What bound does Cauchy–Schwarz give for $|\\langle u,v\nangle|$?',
                'after': 'What bound does Cauchy–Schwarz give for $|\\langle u,v\\rangle|$?',
                'reason': 'Restore the closing inner-product delimiter in the readiness question; the existing answer already uses the correct delimiter.',
                'semantic_question_changed': False, 'hint_changed': False}]
    installs = []
    for name, snapshot in sorted(manifest['source_snapshots'].items()):
        old = exact(snapshot).read_bytes()
        choice = candidates.get(name)
        new = review.path(choice['candidate_file']).read_bytes() if choice else old
        if choice:
            assert review.sha(new) == choice['sha256']
        for repair in repairs:
            if repair['source_file'] == name:
                before, after = repair['before'].encode(), repair['after'].encode()
                assert new.count(before) == 1 and new.count(after) == 0, 'Formatting repair is not unique'
                new = new.replace(before, after, 1)
        blob = RELEASE + '/selected-sources/' + name
        review.put(blob, new)
        installs.append({'file': name, 'before': snapshot, 'after': review.ref(blob),
                         'before_sha256': review.sha(old), 'after_sha256': review.sha(new), 'changed': old != new})
    expected_site = dict(original_site)
    expected_site.update({r['file']: r['after_sha256'] for r in installs if r['file'].startswith('SafeLearning/')})
    tracker_snapshot = RELEASE + '/independently-approved-tracker.json'
    review.put(tracker_snapshot, tracker_raw)
    plan = {'schema': 'solutions.source91.release.v1', 'status': 'all556_independently_approved_ready_for_solution_installation',
            'helper': review.ref(HERE), 'baseline_manifest': review.ref(review.BASELINE + '/manifest.json'),
            'approved_tracker': review.ref(tracker_snapshot), 'drafts': drafts, 'independent_reviews': reports,
            'solution_only_preservation': review.ref(preservation), 'formatting_exceptions': repairs,
            'counts': {'exercises': 556, 'pages': 22, **dict(Counter(r['decision'] for r in decisions.values()))},
            'files': installs, 'site_source90_sha256': original_site, 'site_source91_sha256': expected_site,
            'selected_prior_proof_audit': review.ref(PRIOR_AUDIT),
            'formal_source_correspondence_for_rewritten_answers': 'pending_explicit_rebase_no_automatic_coverage_claim',
            'historical_checkpoint35_formal_coverage_unchanged': True}
    assert review.path(tracker_name).read_bytes() == tracker_raw, 'Review queue changed during preparation'
    review.json_put(PLAN, plan)
    print(json.dumps({'plan': review.ref(PLAN), 'counts': plan['counts'], 'changed_files': sum(r['changed'] for r in installs)}))


def load_plan(fingerprint):
    assert review.ref(PLAN)['sha256'] == fingerprint, 'Release plan differs'
    plan = review.read(PLAN)
    assert plan['status'] == 'all556_independently_approved_ready_for_solution_installation'
    exact(plan['helper']); exact(plan['approved_tracker']); exact(plan['baseline_manifest'])
    approved_selection(review.read(plan['approved_tracker']['file']))
    for row in plan['files']:
        exact(row['before']); exact(row['after'])
    return plan


def atomic_copy(target, data):
    fd, temporary = tempfile.mkstemp(prefix='.' + target.name + '-', dir=target.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
        os.replace(temporary, target)
        folder = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(folder)
        finally:
            os.close(folder)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def apply(fingerprint):
    plan = load_plan(fingerprint)
    lock_path = review.path(RELEASE + '/installation.lock', writable=True)
    with lock_path.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        # Reject all unexpected bytes before changing any file.
        for row in plan['files']:
            assert review.ref(row['file'])['sha256'] in {row['before_sha256'], row['after_sha256']}, row['file']
        for name, old in plan['site_source90_sha256'].items():
            assert review.ref(name)['sha256'] in {old, plan['site_source91_sha256'][name]}, name
        for i, row in enumerate(plan['files']):
            target = review.path(row['file'])
            observed=review.sha(target.read_bytes())
            assert observed in {row['before_sha256'], row['after_sha256']}, 'Target edited after preflight: ' + row['file']
            if observed != row['after_sha256']:
                atomic_copy(target, exact(row['after']).read_bytes())
            assert review.ref(row['file'])['sha256'] == row['after_sha256'], 'Installed bytes differ: ' + row['file']
            receipt = RELEASE + '/installation/' + str(i).zfill(2) + '.json'
            review.json_put(receipt, {'file': row['file'], 'plan': review.ref(PLAN),
                                     'installed_sha256': review.ref(row['file'])['sha256']})
        assert all(review.ref(r['file'])['sha256'] == r['after_sha256'] for r in plan['files'])
        assert all(review.ref(n)['sha256'] == h for n, h in plan['site_source91_sha256'].items())
        report = {'status': 'passed_actual_all556_solution_source_installation', 'plan': review.ref(PLAN),
                  'counts': plan['counts'], 'site_source91_sha256': plan['site_source91_sha256'],
                  'formal_coverage_changed': False, 'build_and_reader_QA': 'pending'}
        review.json_put('reports/solution-review/release-source91-installation-v1.json', report)
        print(json.dumps({'status': report['status'], 'counts': plan['counts']}))


def check(fingerprint, report_name):
    plan = load_plan(fingerprint)
    manifest, baseline = review.load(review.BASELINE)
    tracker = review.read(plan['approved_tracker']['file'])
    _, _, _, _, decisions = approved_selection(tracker)
    findings, selected_rows = [], []
    for row in plan['files']:
        name = row['file']; raw = review.path(name).read_bytes()
        assert review.sha(raw) == row['after_sha256'], 'Actual installed source differs: ' + name
        restored = raw
        for repair in reversed(plan['formatting_exceptions']):
            if repair['source_file'] == name:
                before, after = repair['before'].encode(), repair['after'].encode()
                assert restored.count(before) == 0 and restored.count(after) == 1, 'Readiness delimiter repair differs'
                restored = restored.replace(after, before, 1)
        findings.append(review.validate_candidate(manifest, baseline, name, restored))
        if not name.startswith('SafeLearning/'):
            continue
        doc = review.Document(raw)
        expected = sorted((e for e in baseline if e['source_file'] == name), key=lambda e: e['ordinal'])
        actual = doc.exercises()
        assert len(actual) == len(expected)
        for source, exercise in zip(expected, actual):
            slot = review.parts(doc, exercise, source['solution']['container_kind'])['solution']
            body = decisions[source['inventory_key']].get('replacement_html', source['solution']['html'])
            assert slot['sha256'] == review.sha(body.encode()), source['inventory_key']
            selected_rows.append({'inventory_key': source['inventory_key'], 'source_file': name,
                                 'decision': decisions[source['inventory_key']]['decision'],
                                 'selected_solution_sha256': slot['sha256'], 'range': slot['range']})
    assert len(selected_rows) == 556
    assert all(review.ref(n)['sha256'] == h for n, h in plan['site_source91_sha256'].items())
    # Check actual links, disclosures, authored integration and real build
    # idempotence. The audited Source90 originals enter only the historical
    # pre-book comparison, after the exact change chain has passed above.
    spec = importlib.util.spec_from_file_location('solution_book_validation', ROOT / 'book/validate.py')
    validator = importlib.util.module_from_spec(spec); sys.modules[spec.name] = validator; spec.loader.exec_module(validator)
    source90 = {Path(n).name: exact(snapshot).read_text() for n, snapshot in manifest['source_snapshots'].items()
                if n.startswith('SafeLearning/') and Path(n).name != 'case-studies.html'}
    integration = validator.validate(True, approved_preservation_sources=source90)
    assert integration['status'] == 'PASS', integration['errors']
    report = {'status': 'passed_all556_installed_solution_preservation_and_book_integration',
              'plan': review.ref(PLAN), 'helper': review.ref(HERE), 'book_validator': review.ref('book/validate.py'),
              'counts': plan['counts'], 'solution_preservation': findings, 'selected_exercises': selected_rows,
              'explicit_formatting_exceptions': plan['formatting_exceptions'], 'book_integration': integration,
              'site_source91_sha256': plan['site_source91_sha256'],
              'formal_source_correspondence': 'pending_for_rewritten_answers', 'browser_QA_claimed': False}
    review.json_put(report_name, report)
    print(json.dumps({'report': review.ref(report_name), 'status': report['status'], 'counts': plan['counts']}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['prepare', 'apply', 'check'])
    parser.add_argument('--plan-sha256')
    parser.add_argument('--report', default='reports/solution-review/release-source91-integration-v1.json')
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare()
    elif args.action == 'apply':
        assert args.plan_sha256; apply(args.plan_sha256)
    else:
        assert args.plan_sha256; check(args.plan_sha256, args.report)


if __name__ == '__main__':
    main()
