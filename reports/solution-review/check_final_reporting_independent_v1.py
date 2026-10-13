"""Check actual reader composition and privately rerun completed documentation."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

HELPERS = ['book/solutions/compose_reader_review.py', 'book/solutions/prepare_solution_documentation.py']
PLAN = 'book/solutions/releases/source91-v1/plan.json'
READY = 'reports/solution-review/source91-release-ready-v1.json'
DOC_RECEIPT = 'reports/solution-review/source91-documentation-v1.json'
HISTORY = 'reports/solution-review/source-history/before-source91-documentation-v1'
DOCS = ['README.md', 'book/coverage/progress.json', 'book/coverage/CONTINUATION.md',
        'reports/full-coverage/README.md', 'verification/lean/README.md', 'book/solutions/RELEASE.md']


def main():
    report_name = sys.argv[1]
    bound_names = HELPERS + [PLAN, READY, DOC_RECEIPT] + DOCS + [HISTORY + '/' + n for n in DOCS[:-1]]
    before = {n: review.ref(n)['sha256'] for n in bound_names}
    plan = review.read(PLAN)
    assert plan['counts'] == {'exercises': 556, 'pages': 22, 'retain': 305, 'replace': 251}
    for n, h in plan['site_source91_sha256'].items():
        assert review.ref(n)['sha256'] == h
    full_name = 'reports/solution-review/source91-reader-browser-v1.json'
    retry_name = 'reports/solution-review/source91-reader-book-rerun-v2.json'
    final_name = 'reports/solution-review/source91-reader-browser-final-v1.json'
    full, retry, final = (review.read(n) for n in [full_name, retry_name, final_name])
    expected = {r['file']: r for r in full if r['status'] == 'passed'}
    assert len(expected) == 28 and len(full) == 29
    assert len(retry) == 1 and retry[0]['file'] == 'book.html' and retry[0]['status'] == 'passed'
    expected['book.html'] = retry[0]
    assert len(final['pages']) == 29 and len(final['preserved_failed_page_attempts']) == 1
    for row in final['pages']:
        selected = dict(row)
        origin = selected.pop('native_attempt_origin')
        assert selected == expected[selected['file']]
        browser = review.read(origin['browser']['file'])
        assert browser[origin['row_index']] == selected
        for kind in ['native', 'browser']:
            assert review.ref(origin[kind]['file'])['sha256'] == origin[kind]['sha256']
    starts = [review.read(r['native']['file'])['started_at_utc'] for r in final['native_attempts']]
    assert starts == sorted(starts) and len(set(starts)) == 2
    assert sum(r['exerciseCounts']['total'] for r in final['pages']) == 556
    for ref in [final['helper'], final['plan']]:
        assert review.ref(ref['file'])['sha256'] == ref['sha256']
    failed = final['preserved_failed_page_attempts'][0]
    original_failed = full[failed['row_index']]
    assert original_failed['status'] == 'failed' and failed['file'] == original_failed['file'] == 'book.html'
    assert failed['errors'] == original_failed['errors']

    spec = importlib.util.spec_from_file_location('reviewed_documentation_helper', ROOT / HELPERS[1])
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    actual_path = review.path
    local_names = set(DOCS + [READY, DOC_RECEIPT])
    with tempfile.TemporaryDirectory(prefix='source91-final-reporting-') as temporary:
        fixture = Path(temporary)
        for name in DOCS + [HISTORY + '/' + n for n in DOCS[:-1]]:
            target = fixture / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(actual_path(name).read_bytes())

        def private_path(name, *, writable=False):
            if name in local_names or name.startswith(HISTORY + '/'):
                target = fixture / name
                assert target.resolve().is_relative_to(fixture)
                return target
            assert not writable, 'Unexpected private-generation write: ' + name
            return actual_path(name)

        review.path = private_path
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                helper.main()
                first_ready = review.path(READY).read_bytes()
                first_receipt = review.path(DOC_RECEIPT).read_bytes()
                helper.main()
            assert first_ready == (ROOT / READY).read_bytes() == review.path(READY).read_bytes()
            assert first_receipt == (ROOT / DOC_RECEIPT).read_bytes() == review.path(DOC_RECEIPT).read_bytes()
            assert all(review.path(n).read_bytes() == (ROOT / n).read_bytes() for n in DOCS)
            progress = review.read('book/coverage/progress.json')
            assert progress['current_site_source_version'].startswith('Source91:')
            assert progress['verified_checkpoint']['source_correspondence_version'] == 'Source90 historical exact owner ledgers'
            assert progress['solution_depth_requirement']['counts'] == plan['counts']
            ready = review.read(READY)
            assert ready['formal_source_correspondence_for_rewritten_answers'] == 'pending_explicit_rebase'
            assert ready['historical_checkpoint35_coverage_source90_only'] == {'complete': 539, 'partial': 6, 'pending': 11, 'material_reviewed': 4878, 'material_pending': 7896}
            assert not review.read(DOC_RECEIPT)['formal_coverage_promoted']
            assert not review.read(DOC_RECEIPT)['actual_publication_claimed']
        finally:
            review.path = actual_path
    after = {n: review.ref(n)['sha256'] for n in bound_names}
    assert before == after
    report = {'status': 'passed_exact_reader_composition_and_private_completed_documentation_rerun',
              'helpers': [review.ref(n) for n in HELPERS], 'plan': review.ref(PLAN),
              'reader_reports': [review.ref(n) for n in [full_name, retry_name, final_name]],
              'selected_page_origins': {'failed_full_v1_passing_rows': 28, 'passing_book_only_v2_rows': 1},
              'preserved_failed_page_attempts': 1, 'oldest_first_native_start_times': starts,
              'real_completed_readiness': review.ref(READY), 'real_completed_documentation_receipt': review.ref(DOC_RECEIPT),
              'private_real_evidence_generation_executions': 2, 'exact_document_comparisons': [review.ref(n) for n in DOCS],
              'formal_source90_counts_promoted_to_source91': False, 'canonical_or_publication_writes': False,
              'protected_before': before, 'protected_after': after,
              'scope': 'All real completed evidence gates execute unchanged. Only documentation output paths are redirected into a private temporary root. Both generated receipts and all six documents equal the actual completed bytes; the second private run preserves them exactly.'}
    review.json_put(report_name, report)
    print(json.dumps({'status': report['status'], 'report': review.ref(report_name)}))


if __name__ == '__main__':
    main()
