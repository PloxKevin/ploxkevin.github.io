"""Bind completed checkpoint35 content delivery and prepare its metadata files.

Only completed native receipts and logs enter the plan; this command's active
recorder outputs are excluded. Mathematical source and proof bytes stay unchanged.
"""
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path
from prepare_runtime35 import ROOT, encode, exact, path, put, read, ref, sha

PUB = ROOT / 'reports/book/publication-repo'
CONTENT = '069532b78ff92ab0b5e84b246807289ca0d62574'
DELIVERY = 'reports/full-coverage/publication35-content-delivery-v1.json'
PLAN = 'reports/full-coverage/publication35-delivery-metadata-plan-v1.json'
HISTORY = 'reports/full-coverage/source-history/checkpoint35-before-delivery-metadata-v1'
DOCS = ['book/coverage/progress.json', 'book/coverage/CONTINUATION.md', 'reports/full-coverage/README.md']


def atomic(name, data):
    p = path(name)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, p)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def completed(name, command=None):
    d = read(name)
    assert d['status'] == 'passed' and d['actual_exit_code'] == 0
    assert sha(d['log']) == d['log_sha256']
    if command is not None:
        assert d['actual_command'] == command
    return d


def main():
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PUB, text=True).strip()
    assert head == CONTENT
    completed('reports/full-coverage/publication35-commit-execution-v1.json')
    completed('reports/full-coverage/publication35-push-execution-v1.json', ['git', 'push', 'origin', 'main'])
    completed('reports/full-coverage/live35-content-execution-v1.json')
    completed('reports/full-coverage/pages35-content-jobs-execution-v1.json')
    live = read('reports/full-coverage/live-checkpoint-35-attempt1.json')
    pages = read('reports/full-coverage/pages-checkpoint-35-attempt1.json')
    jobs = json.loads(path('reports/full-coverage/pages35-content-jobs-execution-v1.log').read_bytes())['jobs']
    assert live['status'] == 'passed_all31_asset_sha256' and live['commit'] == live['remote_main'] == CONTENT
    assert len(live['assets']) == 31 and all(a['matches'] for a in live['assets'])
    assert pages['status'] == 'passed' and pages['commit'] == pages['expected_commit'] == CONTENT
    assert len(jobs) == 3 and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
    originals = {}
    for n in DOCS:
        old = HISTORY + '/' + n
        if not path(old).exists():
            put(old, path(n).read_bytes())
        originals[n] = ref(old)
    receipt = {
        'status': 'passed_checkpoint35_actual_content_delivery', 'content_commit': CONTENT,
        'actual_commit': ref('reports/full-coverage/publication35-commit-execution-v1.json'),
        'actual_push': ref('reports/full-coverage/publication35-push-execution-v1.json'),
        'live': ref('reports/full-coverage/live-checkpoint-35-attempt1.json'),
        'pages': ref('reports/full-coverage/pages-checkpoint-35-attempt1.json'),
        'actual_live_execution': ref('reports/full-coverage/live35-content-execution-v1.json'),
        'actual_jobs_execution': ref('reports/full-coverage/pages35-content-jobs-execution-v1.json'),
        'all31_assets_verified': True, 'successful_pages_jobs': [j['name'] for j in jobs],
        'metadata_delivery_pending': True, 'coverage_complete': False}
    put(DELIVERY, encode(receipt))
    progress = read(HISTORY + '/book/coverage/progress.json')
    progress['last_published_content_commit'] = CONTENT
    progress['last_published_commit'] = CONTENT
    progress['publication_status'] = 'checkpoint35_content_Pages_and_all31_live_confirmed_metadata_pending'
    progress['live_delivery_status'] = 'passed_checkpoint35_content_Pages_and_all31_asset_hashes_metadata_pending'
    progress['live_delivery_evidence'] = {
        'previous_checkpoint34': progress['previous_checkpoint34_delivery'],
        'content_commit': CONTENT, 'actual_content_delivery': ref(DELIVERY),
        'content_live_check': receipt['live'], 'content_pages_check': receipt['pages'],
        'actual_live_execution': receipt['actual_live_execution'],
        'metadata_push_and_metadata_live_check_pending': True}
    progress['working_next_checkpoint_preparation']['status'] = 'checkpoint35_content_delivered_metadata_pending_next_work_unselected'
    progress['objective'] = 'Full mathematical exercise and teaching-material coverage with local Lean4 proofs and exact source correspondence; thorough student-followable solutions for all exercises'
    progress['solution_depth_requirement'] = {
        'user_request': 'All exercises are good; solutions must be thorough enough that a student can follow every step.',
        'status': 'in_progress_drafts_separate_from_verified_Source90', 'exercises': 556,
        'questions_and_hints_preserved': True,
        'reader_baseline': 'One first course in linear algebra and single-variable calculus.',
        'criteria': ref('book/solutions/README.md'),
        'baseline_manifest': ref('book/solutions/baseline-source90/manifest.json'),
        'tracker': 'book/solutions/baseline-source90/review-tracker.json',
        'pedagogical_completion_claimed': False}
    bodies = {'book/coverage/progress.json': encode(progress)}
    for n in DOCS[1:]:
        text = path(HISTORY + '/' + n).read_text()
        text += '\nCheckpoint35 content is published at `069532b7`. All three Pages jobs and a fresh all 31-asset hash check passed. Delivery metadata is pending; mathematical coverage remains partial.\n'
        text += '\nThe user also requested thorough, student-followable solutions for all 556 exercises. Questions and hints remain intact. The byte-bound audit and draft work are in `book/solutions/`; these drafts are separate from the verified Source90 site.\n'
        bodies[n] = text.encode()
    if not path(PLAN).exists():
        for n, data in bodies.items():
            atomic(n, data)
        files = set(DOCS + [DELIVERY, 'book/solutions/README.md', 'book/solutions/baseline-source90/manifest.json'])
        files.add(Path(__file__).relative_to(ROOT).as_posix())
        for n in ['publication35-copy-plan-v1-applied.json', 'publication35-plan-execution-v1.json',
                  'publication35-stage-execution-v1.json', 'publication35-add-execution-v1.json',
                  'publication35-commit-execution-v1.json', 'publication35-push-execution-v1.json',
                  'pages35-content-runs-execution-v1.json', 'pages35-content-jobs-execution-v1.json',
                  'live35-content-execution-v1.json']:
            name = 'reports/full-coverage/' + n
            d = completed(name) if 'execution' in n else read(name)
            files.add(name)
            if 'log' in d:
                files.add(d['log'])
            if d.get('started_receipt'):
                files.add(d['started_receipt'])
        for n in ['live-checkpoint-35-attempt1.json', 'pages-checkpoint-35-attempt1.json',
                  'pages-checkpoint-35-attempt1.log']:
            files.add('reports/full-coverage/' + n)
        for r in originals.values():
            files.add(r['file'])
        # A baseline snapshot is referenceable only when its actual bytes are
        # published as well. Include this bounded556-exercise extraction, not
        # active drafts, author outputs or an active recorder log.
        for p in path('book/solutions/baseline-source90').rglob('*'):
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'review-tracker.json':
                files.add(p.relative_to(ROOT).as_posix())
        for n in ['reports/solution-review/baseline-source90-extraction-v1.json']:
            if path(n).exists():
                files.add(n)
        plan = {'status': 'ready_completed_checkpoint35_content_receipts_metadata_publication',
            'expected_content_head': CONTENT, 'content_delivery': ref(DELIVERY),
            'files': [{'source': n, 'destination': n, 'sha256': sha(n)} for n in sorted(files)],
            'preserved_original_documents': originals, 'active_recording_outputs_included': False,
            'coverage_complete': False, 'metadata_push_or_live_claimed': False}
        put(PLAN, encode(plan))
    plan = read(PLAN)
    assert all(sha(r['source']) == r['sha256'] for r in plan['files'])
    print(json.dumps({'status': receipt['status'], 'delivery': ref(DELIVERY),
                      'metadata_plan': ref(PLAN), 'files': len(plan['files'])}))


if __name__ == '__main__':
    main()
