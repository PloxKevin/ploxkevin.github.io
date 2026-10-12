"""Combine actual current65 checks with exact unchanged checkpoint28 records."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT/'reports/full-coverage'
FRESH = 'reports/full-coverage/browser-source65-29-v2.json'
ACTUAL = 'reports/full-coverage/browser-source65-29-v2-execution.json'
OUTER = 'reports/full-coverage/browser29-source65-helper-execution-v2.json'
OLD = 'reports/full-coverage/browser-checkpoint-28.json'
OLD_INPUTS = 'reports/full-coverage/browser-corrections-28-inputs.json'
SCROLL = 'reports/full-coverage/source65-four-page-math-scroll29-v2.json'
SCROLL_NATIVE = 'reports/full-coverage/source65-four-page-math-scroll29-execution-v2.json'
CHANGED = {'primer-basics.html', 'primer-linalg.html', 'primer-optimization.html', 'lipsdp.html'}

def sha(n): return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n): return json.loads((ROOT/n).read_bytes())
def ref(n): return {'file': n, 'sha256': sha(n)}
def zero(d):
    assert d['status'] == 'passed' and type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0
    assert sha(d['log']) == d['log_sha256']

def main():
    fresh, actual, outer, old, old_inputs, scroll, scroll_native = [read(n) for n in [FRESH, ACTUAL, OUTER, OLD, OLD_INPUTS, SCROLL, SCROLL_NATIVE]]
    for d in [actual, outer, scroll_native]: zero(d)
    assert actual['report_sha256'] == sha(FRESH)
    sources = actual['source_sha256_before']; qa = actual['qa_source_sha256']
    assert sources == actual['source_sha256_after'] and len(sources) == 31
    assert {n for n in sources if sources[n] != old['source_sha256'][n]} == {'SafeLearning/'+n for n in CHANGED}
    assert all(sha(n) == h for n, h in {**sources, **qa}.items())
    assert qa == old['qa_source_sha256'] and old['page_count'] == 29
    assert old['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
    assert old['manual_visual_inspection']['status'] == 'all48_actual_captured_regions_inspected_with_explicit_scope_limits'
    for k in ['new_eight_capture_review']:
        assert sha(old_inputs[k]['file']) == old_inputs[k]['sha256']
    assert scroll['status'] == 'passed' and scroll['errors'] == [] and scroll['source_sha256'] == sources
    assert {r['file'] for r in scroll['pages']} == CHANGED
    assert all(r['status'] == 'passed' and all(c['status'] == 'passed' for c in r['overflow_containers']) for r in scroll['pages'])
    newpages = {p['file']: p for p in fresh}; oldpages = {p['file']: p for p in old['pages']}
    assert set(newpages) == CHANGED and len(oldpages) == 29
    targets = [REPORTS/'browser-artifacts-29', REPORTS/'browser-checkpoint-29.json', REPORTS/'browser-corrections-29-inputs.json', REPORTS/'source65-eight-captured-regions-manual-review29-v1.json']
    assert not any(p.exists() for p in targets)
    artifact, output, inputs, manual = targets
    pages, modes, aliases, captures = [], {}, [], []
    skipped = 0
    for name in sorted(oldpages):
        p = newpages[name] if name in CHANGED else oldpages[name]
        assert p['status'] == 'passed' and p['errors'] == []
        assert {v['width'] for v in p['viewports']} == {320, 390, 768, 820, 1280}
        assert all(not v['clipped'] and v['documentWidth'] <= v['width'] for v in p['viewports'])
        assert p['source_sha256'] == sources['SafeLearning/'+name]
        assert p['qa_source_sha256'] == {Path(n).name: h for n, h in qa.items()}
        pages.append(p)
        mode = 'fresh_actual_current65_browser_execution' if name in CHANGED else 'retained_exact_unchanged_source_and_QA_original28_record'
        modes[name] = {'evidence_mode': mode, 'original_report': ref(FRESH if name in CHANGED else OLD)}
        for c in p['screenshots']:
            if c['status'] == 'skipped': skipped += 1; continue
            assert c['status'] == 'passed' and c['source_sha256'] == p['source_sha256'] and sha(c['path']) == c['sha256']
            aliases.append({'original': c['path'], 'file': (artifact/Path(c['path']).name).relative_to(ROOT).as_posix(), 'sha256': c['sha256'], 'evidence_mode': mode})
            if name in CHANGED: captures.append(c)
    assert len(aliases) == 48 and len(captures) == 8 and skipped == 10
    assert len({r['file'] for r in aliases}) == 48
    artifact.mkdir()
    for r in aliases:
        shutil.copyfile(ROOT/r['original'], ROOT/r['file']); assert sha(r['file']) == r['sha256']
    observations = {
        'primer-basics.html': 'The captured chamber model, command interval, stopping-time calculation and four opened hint/solution cards are readable at both widths. The long mobile quantified display continues outside its initial right edge.',
        'primer-linalg.html': 'The captured reconstruction, singular-value, residual and four opened hint/solution cards are readable. The displayed singular-value formula occupies the available mobile width. The separate actual scroll run found no overflowing scrollable container in this captured region.',
        'primer-optimization.html': 'The captured allocation, multiplier, nonlinear clearance and four opened hint/solution cards are readable. The long mobile objective display continues outside its initial right edge.',
        'lipsdp.html': 'The captured certificate, physical scaling and two opened hint/solution cards are readable. The long mobile ReLU display continues outside its initial right edge.'}
    manual_data = {'status': 'completed_actual_eight_original_image_inspections_of_captured_regions', 'reviewer': 'Root',
        'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'inspected_captures': captures,
        'inspection_method': 'view_image with original detail for each of the eight actual captures', 'observations': observations,
        'horizontal_scroll_interaction_verified': True, 'actual_separate_scroll_result': ref(SCROLL),
        'actual_separate_scroll_execution': ref(SCROLL_NATIVE), 'whole_page_visual_approval': False,
        'scope': 'Only captured application regions at390/1280 widths. Corrected original paragraphs outside those regions and whole chapters were not visually inspected by these captures. The separate actual wheel run checks all overflowing scrollable mathematics in those four application regions at390px.'}
    manual.write_text(json.dumps(manual_data, indent=2)+'\n')
    input_data = {'actual_execution': ref(ACTUAL), 'actual_outer_helper_execution': ref(OUTER), 'entire_original_actual_body_and_time': actual,
        'fresh_original_report': ref(FRESH), 'retained_original_report': ref(OLD), 'source_sha256': sources, 'qa_source_sha256': qa,
        'pages': modes, 'screenshot_aliases': aliases, 'historical_original48_capture_review': ref(OLD_INPUTS),
        'new_eight_capture_review': ref(manual.relative_to(ROOT).as_posix()), 'actual_scroll_result': ref(SCROLL), 'actual_scroll_execution': ref(SCROLL_NATIVE)}
    inputs.write_text(json.dumps(input_data, indent=2)+'\n')
    result = {'status': 'passed_actual_changed_pages_and_exact_unchanged_evidence', 'created_at_utc': datetime.now(timezone.utc).isoformat(),
        'page_count': 29, 'requested_viewport_count': 145, 'verified_viewport_count': 145, 'fresh_verified_viewport_count': 20,
        'retained_verified_viewport_count': 125, 'source_sha256': sources, 'qa_source_sha256': qa,
        'actual_execution': ACTUAL, 'actual_execution_sha256': sha(ACTUAL), 'fresh_run_inputs': inputs.relative_to(ROOT).as_posix(),
        'fresh_run_inputs_sha256': sha(inputs.relative_to(ROOT).as_posix()), 'pages': pages, 'evidence_modes': modes,
        'screenshot_count': 48, 'skipped_capture_target_count': 10,
        'manual_visual_inspection': {'status': 'all48_actual_captured_regions_inspected_with_explicit_scope_limits', 'fresh_actual_captures': 8,
            'retained_exact_capture_count': 40, 'new_original_eight_review': ref(manual.relative_to(ROOT).as_posix()),
            'original_checkpoint28_review_closure': ref(OLD_INPUTS), 'horizontal_scroll_interaction_verified': True,
            'actual_scroll_result': ref(SCROLL), 'whole_page_visual_approval': False}, 'coverage_complete': False,
        'limits': ['Twenty fresh actual viewport checks cover four changed current65 pages. Other125 checks retain exact original source, QA, commands, results and times.',
            'Eight fresh and forty retained captures cover application regions; original correction paragraphs and whole chapters are outside visual approval.',
            'The actual horizontal wheel check establishes access to both ends of every overflowing scrollable mathematical container in the four captured application regions at390px.',
            'Browser checks do not establish mathematical correctness.']}
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'passed', 'pages': 29, 'fresh_viewports': 20, 'retained_viewports': 125, 'screenshots': 48, 'fresh_images_inspected': 8, 'retained_images_inspected': 40, 'actual_overflow_containers': scroll['actual_overflow_container_count']}))

if __name__ == '__main__': main()
