"""Assemble, check and atomically install the recovered opening-solution pass.

Every source is checked against the frozen all-556 Source91 baseline. Resume
accepts only the exact planned before/after bytes and preserves the originals.
"""
import argparse
import copy
import fcntl
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as h
from solution_release import atomic_copy

BASE = 'book/solutions/releases/source92-opening-v1'
BASELINE = BASE + '/baseline-source91'
PRIMER = 'book/solutions/opening-step-review-v1/assessments-v2.json'
MODULE = 'book/solutions/module-opening-step-review-v1/assessments-v1.json'
PLAN = BASE + '/plan-v1.json'
SELF = BASE + '/recover_release.py'


def load_baseline():
    full = h.read(BASELINE + '/manifest.json')
    assert full['exercises'] == 556 and len(full['pages']) == 22
    rows = []
    for r in full['pages'].values():
        assert h.ref(r['file']) == r
        rows.extend(h.read(r['file'])['exercises'])
    assert len(rows) == len({r['inventory_key'] for r in rows}) == 556
    for r in full['source_snapshots'].values():
        assert h.ref(r['file']) == r
    return full, rows


def check_files(plan, *, installed):
    full, rows = load_baseline()
    assert h.ref(PRIMER) == plan['primer_assessment'] and h.ref(MODULE) == plan['module_assessment']
    checks = []
    for file in plan['files']:
        raw = h.path(file['file'] if installed else file['candidate']['file']).read_bytes()
        assert h.sha(raw) == file['after_sha256']
        check = h.validate_candidate(full, rows, file['file'], raw)
        assert {r['inventory_key'] for r in check['changed_solutions']} == set(file['changed_solution_keys'])
        checks.append(check)
    for name, digest in plan['site_after_sha256'].items():
        assert h.ref(name if installed else BASE + '/candidates/' + name)['sha256'] == digest
    return checks


def prepare():
    full, rows = load_baseline()
    baseline = {r['inventory_key']: r for r in rows}
    decisions = copy.deepcopy(h.read(PRIMER)['exercises'] + h.read(MODULE)['exercises'])
    assert len(decisions) == len({r['inventory_key'] for r in decisions}) == 113
    assert sum(r['decision'] == 'replace' for r in decisions) == 56
    splices = {}
    for row in decisions:
        original = baseline[row['inventory_key']]
        assert row['source_file'] == original['source_file']
        assert row['original_solution_sha256'] == original['solution']['sha256']
        assert row['authoring_file'] == original['authoring_file']
        if row['decision'] == 'retain':
            row['selected_solution_sha256'] = original['solution']['sha256']
            continue
        raw = row['replacement_html'].encode()
        assert h.sha(raw) != row['original_solution_sha256']
        row['selected_solution_sha256'] = h.sha(raw)
        spans = {original['source_file']: original['solution']['range'],
                 original['authoring_file']: original['authoring']['solution_range']}
        for name, span in spans.items():
            splices.setdefault(name, []).append((span['start_byte'], span['end_byte'], row['inventory_key'], raw))
    files = []
    for name, items in sorted(splices.items()):
        before = h.path(full['source_snapshots'][name]['file']).read_bytes()
        assert h.ref(name)['sha256'] == h.sha(before)
        chunks, cursor = [], 0
        for a, b, key, replacement in sorted(items):
            assert cursor <= a < b <= len(before)
            assert h.sha(before[a:b]) == baseline[key]['solution']['sha256']
            chunks.extend([before[cursor:a], replacement])
            cursor = b
        chunks.append(before[cursor:])
        after = b''.join(chunks)
        check = h.validate_candidate(full, rows, name, after)
        assert {r['inventory_key'] for r in check['changed_solutions']} == {r[2] for r in items}
        target = BASE + '/candidates/' + name
        h.put(target, after)
        files.append({'file': name, 'before_sha256': h.sha(before), 'after_sha256': h.sha(after),
                      'original': full['source_snapshots'][name], 'candidate': h.ref(target),
                      'changed_solution_keys': sorted(r[2] for r in items)})
    for name, digest in full['site_before_sha256'].items():
        target = BASE + '/candidates/' + name
        if h.path(target).exists():
            continue
        assert h.ref(name)['sha256'] == digest
        h.put(target, h.path(name).read_bytes())
    site_after = {name: h.ref(BASE + '/candidates/' + name)['sha256'] for name in full['site_before_sha256']}
    plan = {'schema': 'solutions.source92.opening.release.v1', 'status': 'prepared_solution_only_candidates',
            'baseline': h.ref(BASELINE + '/manifest.json'), 'primer_assessment': h.ref(PRIMER),
            'module_assessment': h.ref(MODULE), 'helper': h.ref(SELF), 'files': files,
            'site_before_sha256': full['site_before_sha256'], 'site_after_sha256': site_after,
            'counts': {'all_exercises': 556, 'reassessed': 113, 'replace': 56, 'retain': 57},
            'exercise_decisions': decisions,
            'review_provenance': 'Saved module23 and primer12 replacements receive a separate recovery review. The21 new recovery-authored replacements are explicitly self-reviewed. All retained/unselected bodies preserve their exact previous independent Source91 review lineage.',
            'all_current556_independently_reviewed_claimed': False,
            'questions_hints_anchors_scripts_and_non_solution_bytes_preserved': True}
    h.json_put(PLAN, plan)
    checks = check_files(plan, installed=False)
    h.json_put(BASE + '/preservation-v1.json', {'status': 'passed_all556_baseline_solution_only_preservation',
        'plan': h.ref(PLAN), 'counts': plan['counts'], 'checks': checks, 'reader_pages': 22,
        'changed_reader_pages': sum(r['file'].startswith('SafeLearning/') for r in files),
        'all_non_solution_bytes_preserved': True, 'all_unselected_and_retained_solution_bodies_preserved': True})
    print(json.dumps({'status': plan['status'], 'counts': plan['counts'], 'files': len(files), 'plan': h.ref(PLAN)}))


def install(expected):
    assert h.ref(PLAN)['sha256'] == expected
    plan = h.read(PLAN)
    check_files(plan, installed=False)
    browser = h.read(BASE + '/reader-QA-v1.json')
    changed_pages = {Path(r['file']).name for r in plan['files'] if r['file'].startswith('SafeLearning/')}
    assert {r['file'] for r in browser} == changed_pages
    assert all(r['status'] == 'passed' and not r['errors'] for r in browser)
    assert all(r['source_sha256'] == plan['site_after_sha256']['SafeLearning/' + r['file']] for r in browser)
    arithmetic = h.read(BASE + '/arithmetic-v1.json')
    assert arithmetic['status'] == 'passed'
    with (ROOT / BASE / 'installation.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        for row in plan['files']:
            assert h.ref(row['file'])['sha256'] in {row['before_sha256'], row['after_sha256']}
        for row in plan['files']:
            current = h.ref(row['file'])['sha256']
            assert current in {row['before_sha256'], row['after_sha256']}
            if current == row['before_sha256']:
                atomic_copy(ROOT / row['file'], h.path(row['candidate']['file']).read_bytes())
        checks = check_files(plan, installed=True)
        h.json_put(BASE + '/installation-v1.json', {'status': 'passed_installed_source92_opening_solution_only_changes',
            'plan': h.ref(PLAN), 'browser': h.ref(BASE + '/reader-QA-v1.json'),
            'arithmetic': h.ref(BASE + '/arithmetic-v1.json'), 'checks': checks, 'counts': plan['counts'],
            'questions_hints_anchors_scripts_preserved': True,
            'all_current556_independently_reviewed_claimed': False})
    print(json.dumps({'status': 'passed_installed_source92_openings', 'counts': plan['counts']}))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=['prepare', 'install', 'check'])
    p.add_argument('--plan-sha256')
    args = p.parse_args()
    if args.command == 'prepare':
        prepare()
    elif args.command == 'install':
        assert args.plan_sha256
        install(args.plan_sha256)
    else:
        assert h.ref(PLAN)['sha256'] == args.plan_sha256
        checks = check_files(h.read(PLAN), installed=True)
        print(json.dumps({'status': 'passed_installed_preservation', 'source_files': len(checks), 'exercises': 556}))


if __name__ == '__main__':
    main()
