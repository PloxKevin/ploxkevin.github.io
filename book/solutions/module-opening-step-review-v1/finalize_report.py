"""Bind completed48-row manual review and actual candidate checks."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

BASE = 'book/solutions/module-opening-step-review-v1'
REPORT = 'reports/solution-review/module-opening-step-review-v1.json'


def exact(row):
    assert review.ref(row['file'])['sha256'] == row['sha256']


def native(name):
    value = review.read(name)
    assert value['status'] == 'passed' and value['actual_exit_code'] == value['recorder_exit_code'] == 0
    assert value['helper_sha256_before'] == value['helper_sha256_after'] and not value['binding_errors_after']
    assert review.ref(value['log'])['sha256'] == value['log_sha256']
    return value


def main():
    manifest = review.read(BASE + '/manifest.json')
    assessment = review.read(BASE + '/assessments-v1.json')
    preservation = review.read(BASE + '/candidate-preservation-v1.json')
    arithmetic = review.read(BASE + '/arithmetic-v1.json')
    assert assessment['counts'] == {'exercises': 48, 'pages': 16, 'replace': 23, 'retain': 25}
    rows = assessment['exercises']
    assert len(rows) == len({r['inventory_key'] for r in rows}) == 48
    assert all(r['replacement_html'] is None for r in rows if r['decision'] == 'retain')
    assert all(review.sha(r['replacement_html'].encode()) == r['selected_solution_sha256'] for r in rows if r['decision'] == 'replace')
    for source in manifest['pages']:
        assert [r['ordinal'] for r in rows if r['source_file'] == source] == [1, 2, 3]
    for ref in assessment['author_packets']:
        exact(ref)
    assert preservation['assessment'] == review.ref(BASE + '/assessments-v1.json')
    assert all(c['status'] == 'passed_solution_only_preservation' for c in preservation['source_checks'])
    assert preservation['question_hint_count_anchor_script_and_all_non_solution_bytes_preserved']
    assert preservation['all_unselected_solution_bodies_unchanged']
    assert len(arithmetic['checks']) == 20 and all(c['status'] == 'passed' for c in arithmetic['checks'])
    executions = {name: native(BASE + '/' + name) for name in ['extraction-execution-v1.json',
                  'assembly-execution-v1.json', 'arithmetic-execution-v1.json', 'candidate-render-execution-v1.json']}
    render = executions['candidate-render-execution-v1.json']
    rendered = review.read(render['log'])
    expected = {Path(c['source_file']).name for c in preservation['source_checks']
                if c['source_file'].startswith('SafeLearning/') and c['changed_solutions']}
    assert len(rendered) == len(expected) == 13 and {r['file'] for r in rendered} == expected
    for row in rendered:
        assert all(not row[k] for k in ['consoleErrors', 'pageErrors', 'leftoverDollar', 'katexErrors',
                                       'missingAnchors', 'brokenLinks', 'mobileOverflow', 'mobileOverflowExpanded']), row['file']
    for c in preservation['source_checks']:
        exact(c['candidate'])
    for name, fingerprint in manifest['protected_before'].items():
        assert review.ref(name)['sha256'] == fingerprint, name
    scope_rows = [{'inventory_key': r['inventory_key'], 'source_file': r['source_file'], 'ordinal': r['ordinal'],
                   'label': r['label'], 'authoring_file': r['authoring_file'],
                   'original_solution_sha256': r['original_solution_sha256'], 'decision': r['decision'],
                   'selected_solution_sha256': r['selected_solution_sha256'],
                   'thoroughness_rationale': r['thoroughness_rationale']} for r in rows]
    report = {'schema': 'solutions.source91.module-opening-step-review.v1',
              'status': 'completed48_manual_opening_assessments_candidates_pending_independent_review',
              'reviewer': '/root/recovery_runner35', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
              'source_version': 'Source91', 'assessment': review.ref(BASE + '/assessments-v1.json'),
              'opening_extraction': review.ref(BASE + '/manifest.json'),
              'full556_current_baseline': assessment['full556_current_baseline'],
              'page_contract': review.ref('page_contract.md'), 'counts': assessment['counts'],
              'selection_definition': manifest['selection_definition'], 'exercise_assessments': scope_rows,
              'assessment_criteria': ['Actual method and why it answers the question',
                  'Explicit symbols, assumptions and physical/statistical units',
                  'Intermediate calculations, substitutions or logical implications',
                  'Reasons for substantive steps and requested boundary/case treatment',
                  'Result interpretation and limits of the certificate'],
              'length_or_boilerplate_used_as_adequacy_criterion': False,
              'candidate_preservation': review.ref(BASE + '/candidate-preservation-v1.json'),
              'validated_source_files': len(preservation['source_checks']),
              'changed_source_files': preservation['changed_source_files'],
              'all_question_hint_exercise_count_anchor_script_and_non_solution_bytes_preserved': True,
              'all_unselected_solution_bodies_preserved': True,
              'arithmetic_checks': review.ref(BASE + '/arithmetic-v1.json'), 'arithmetic_check_count': 20,
              'actual_candidate_browser_QA': {'native_execution': review.ref(BASE + '/candidate-render-execution-v1.json'),
                  'actual_command': render['actual_command'], 'raw_report_log': review.ref(render['log']),
                  'pages_checked': 13, 'all_changed_reader_pages_checked': True,
                  'error_fields_all_zero': True, 'desktop_capture_width': 1280, 'expanded_math_checked_width': 390,
                  'full_page_screenshot_captured': True,
                  'screenshot_notes': {r['file']: r['screenshotNote'] for r in rendered if r.get('screenshotNote')},
                  'visual_scope': 'One full-page landscape screenshot was inspected to confirm explorer/layout rendering. The very long whole-page image does not provide a readable visual inspection of every replacement. Automated KaTeX/expanded-overflow checks cover all changed pages; independent readable-view review remains with integration.'},
              'actual_native_executions': [review.ref(BASE + '/' + n) for n in executions],
              'protected_current_sha256': manifest['protected_before'],
              'canonical_reader_authored_source_and_old556tracker_bytes_unchanged': True,
              'proof_owner_or_git_writes_by_this_review': False, 'compiler_executed_by_this_review': False,
              'canonical_installation_or_independent_approval_claimed': False,
              'theorem_coverage_widened_or_formal_completion_claimed': False,
              'scope': 'Read-only/candidate authoring for48 non-primer DOM openings, using exact current Source91 questions/hints/bodies and authored mirrors. All23 replacements are substantive exercise-specific reasoning;25 retains are individually justified. Integration and independent review happen separately after the frozen formal work.'}
    review.json_put(REPORT, report)
    print(json.dumps({'status': report['status'], 'counts': report['counts'], 'report': review.ref(REPORT)}))


if __name__ == '__main__':
    main()
