"""Correct the browser page list against the actual changed source fingerprints."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
REPORT = ROOT / 'reports/full-coverage/browser-checkpoint-30-changed-pages-final-v1.json'
OVERLAY = ROOT / 'reports/full-coverage/publication30-browser-document-overlay-v1.json'
OLD_DOC = ROOT / 'reports/full-coverage/source-history/README-checkpoint30-doc1-before-browser-list-correction-v1.md'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((ROOT / n).read_bytes())


def ref(n):
    return {'file': n, 'sha256': sha(ROOT / n)}


assert not REPORT.exists() and not OVERLAY.exists() and not OLD_DOC.exists()
manifest = read('reports/full-coverage/checkpoint-30-manifest.json')
prior = read('reports/full-coverage/checkpoint-29-manifest.json')
changed = sorted(n for n, h in manifest['frozen_inputs_sha256'].items()
                 if n.startswith('SafeLearning/') and n.endswith('.html') and prior['frozen_inputs_sha256'][n] != h)
assert len(changed) == 6 and 'SafeLearning/primer-basics.html' in changed
reports = ['reports/full-coverage/browser-checkpoint-30-changed6-v2.json',
           'reports/full-coverage/browser-checkpoint-30-primer0-v1.json']
natives = ['reports/full-coverage/browser30-changed6-execution-v2.json',
           'reports/full-coverage/browser30-primer0-execution-v1.json']
rows = {}; origins = {}
for report_name, native_name in zip(reports, natives):
    native = read(native_name)
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert sha(ROOT / native['log']) == native['log_sha256']
    assert native['helper_sha256_before'] == native['helper_sha256_after']
    assert native['actual_command'][:4] == ['node', 'qa/learning_review.mjs', '--report', report_name]
    for row in read(report_name):
        n = 'SafeLearning/' + row['file']
        assert row['status'] == 'passed' and row['errors'] == [] and len(row['viewports']) == 5
        assert row['source_sha256'] == manifest['frozen_inputs_sha256'][n] == sha(ROOT / n)
        assert n not in rows
        rows[n] = row; origins[n] = {'report': ref(report_name), 'actual_execution': ref(native_name)}
assert set(changed) <= set(rows) and len(rows) == 7
result = {'status': 'passed_source_exact_all_six_actual_changed_HTML_pages_browser_checks',
          'checked_at_utc': datetime.now(timezone.utc).isoformat(),
          'current_final_css_sha256': manifest['frozen_inputs_sha256']['SafeLearning/style.css'],
          'actual_changed_HTML_pages': changed, 'changed_page_viewport_count': 30,
          'changed_page_checks': {n: {'original_report_and_native': origins[n], 'original_row': rows[n]} for n in changed},
          'additional_unchanged_page_checks': {n: {'original_report_and_native': origins[n], 'original_row': rows[n]} for n in rows if n not in changed},
          'original_reports_natives_and_checked_times_rewritten': False,
          'original_list_error': 'The first six-page final browser request included unchanged primer-optimization and omitted changed primer-basics. The fresh separate Primer0 request closes that page gap; original records remain unchanged.',
          'scope': 'Six exact changed pages at five widths each, plus five additional optimization-primer widths. Capture inspection and formula scroll endpoints are separate evidence.',
          'coverage_complete': False}
assert sha(ROOT / 'SafeLearning/style.css') == result['current_final_css_sha256']
REPORT.write_text(json.dumps(result, indent=2) + '\n')
doc = ROOT / 'reports/full-coverage/README.md'
before_sha = sha(doc); shutil.copyfile(doc, OLD_DOC)
text = doc.read_text()
old = '''556 exercises and 21 application labs. [Fresh browser checks](browser-checkpoint-30-changed6-v2.json)
passed on all six changed pages at five viewport widths each. Twelve
application-region captures were independently inspected; this is a bounded
visual review.'''
new = '''556 exercises and 21 application labs. [Source-exact fresh browser checks](browser-checkpoint-30-changed-pages-final-v1.json)
passed on all six actual changed pages at five viewport widths each. Five
additional widths were checked on the unchanged optimization primer. The
initial page-list mistake is retained in the original reports and closed by
the separate fresh Primer 0 run. The application-region screenshot review is
bounded; it does not claim whole-page visual coverage.'''
assert text.count(old) == 1
doc.write_text(text.replace(old, new))
extra = [
    'reports/full-coverage/browser-checkpoint-30-changed-pages-final-v1.json',
    'reports/full-coverage/browser-checkpoint-30-primer0-v1.json',
    'reports/full-coverage/browser30-primer0-execution-v1.json',
    'reports/full-coverage/browser30-primer0-execution-v1.log',
    OLD_DOC.relative_to(ROOT).as_posix(),
    'book/coverage/checks/root_prepare_publication30_browser_overlay_v1.py',
]
extra += [p.relative_to(ROOT).as_posix() for p in (ROOT / 'reports/full-coverage/browser-artifacts-30-primer0').glob('*') if p.is_file()]
overlay = {'status': 'actual_source_exact_six_changed_pages_browser_and_corrected_document_overlay_for_staging',
           'current_manifest': ref('reports/full-coverage/checkpoint-30-manifest.json'),
           'original_prepared_publication': ref('reports/full-coverage/publication30-prepared-exact-files-v1.json'),
           'original_document': {'file': 'reports/full-coverage/README.md', 'sha256': before_sha},
           'preserved_original_document': ref(OLD_DOC.relative_to(ROOT).as_posix()),
           'replacement_root_paths_sha256': {'reports/full-coverage/README.md': sha(doc)},
           'additional_root_paths_sha256': {n: sha(ROOT / n) for n in extra},
           'actual_source_exact_changed_pages_report': ref(REPORT.relative_to(ROOT).as_posix()),
           'mathematical_HTML_proofs_assets_or_ledger_bytes_changed': False,
           'coverage_complete': False}
OVERLAY.write_text(json.dumps(overlay, indent=2) + '\n')
print(json.dumps({'status': overlay['status'], 'actual_changed_pages': 6,
                  'actual_changed_viewports': 30, 'additional_viewports': 5,
                  'overlay': ref(OVERLAY.relative_to(ROOT).as_posix())}))
