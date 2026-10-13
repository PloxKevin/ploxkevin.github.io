"""Bind the bounded final reporting review to its real current evidence."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review


def exact(ref):
    assert review.ref(ref['file'])['sha256'] == ref['sha256'], ref['file']


def native(name, expected_exit=0):
    value = review.read(name)
    assert value['actual_exit_code'] == value['recorder_exit_code'] == expected_exit
    assert value['status'] == ('passed' if expected_exit == 0 else 'failed')
    assert value['helper_sha256_before'] == value['helper_sha256_after']
    assert not value['binding_errors_after']
    assert review.ref(value['log'])['sha256'] == value['log_sha256']
    assert review.ref(value['started_receipt'])['sha256'] == value['started_receipt_sha256']
    return value


def main():
    report_name = 'reports/solution-review/source91-final-reporting-independent-review-v1.json'
    helpers = ['book/solutions/compose_reader_review.py', 'book/solutions/prepare_solution_documentation.py']
    helper_hashes = ['658bbec325a0a2e8001ceb2d5d6e456428fdcdd4c0f7d2ad11e03b6e524d2c19',
                     '0c3100421c090cf69521260071e5f2be1bd850e64619473c3e6deb83e56a2b5b']
    for n, h in zip(helpers, helper_hashes):
        assert review.ref(n)['sha256'] == h
    plan_name = 'book/solutions/releases/source91-v1/plan.json'
    plan = review.read(plan_name)
    assert review.ref(plan_name)['sha256'] == '58455c17c48c091f9c6934165d64d003ff43bfee7bda888d10f438d02e7cc11e'
    before = {n: review.ref(n)['sha256'] for n in helpers + [plan_name] + list(plan['site_source91_sha256'])}
    for n, h in plan['site_source91_sha256'].items():
        assert before[n] == h
    private_name = 'reports/solution-review/source91-final-reporting-private-checks-v1.json'
    private = review.read(private_name)
    assert private['status'] == 'passed_exact_reader_composition_and_private_completed_documentation_rerun'
    assert not private['canonical_or_publication_writes']
    assert private['private_real_evidence_generation_executions'] == 2
    for ref in private['helpers'] + private['reader_reports'] + private['exact_document_comparisons']:
        exact(ref)
    current_test_name = 'reports/solution-review/source91-final-documentation-independent-tests-v1.json'
    current_test = review.read(current_test_name)
    assert current_test['status'] == 'passed' and len(current_test['cases']) == 5
    assert all(c['passed'] for c in current_test['cases'])
    assert current_test['helper'] == review.ref(helpers[1])
    historical_test_name = 'reports/solution-review/source91-historical-documentation-regression-v1.json'
    historical = review.read(historical_test_name)
    assert historical['status'] == 'failed_documentation_final_byte_guard'
    gap = next(c for c in historical['cases'] if c['name'] == 'late_already_installed_edit')
    assert not gap['passed'] and gap['unexpected_late_edit_incorrectly_bound_as_success']
    exact(historical['helper'])
    assert historical['helper']['sha256'] == '5209e6c0cf0b43e2433c41a65b10540ec8df184ff45dad0d5accd375f0216679'
    execution_names = ['source91-prepare-execution-v1.json', 'source91-install-execution-v1.json',
                       'source91-book-build-execution-v1.json', 'source91-integration-execution-v1.json',
                       'source91-runtime-prepare-execution-v1.json', 'source91-lean-audit-execution-v1.json',
                       'source91-qa-check-execution-v1.json', 'source91-reader-final-composition-execution-v1.json',
                       'source91-visual-execution-v1.json', 'source91-documentation-execution-v1.json',
                       'source91-documentation-resume-execution-v1.json',
                       'source91-final-reporting-private-checks-native-v1.json',
                       'source91-final-documentation-independent-tests-native-v1.json']
    executions = {n: native('reports/solution-review/' + n) for n in execution_names}
    failed_native_name = 'reports/solution-review/source91-historical-documentation-regression-native-v1.json'
    native(failed_native_name, 1)
    original_native_name = 'reports/solution-review/source91-reader-qa-execution-v1.json'
    native(original_native_name, 1)
    retry_native_name = 'reports/solution-review/source91-reader-book-rerun-native-v2.json'
    native(retry_native_name)
    for name in ['source91-qa-check-execution-v1.json', 'source91-visual-execution-v1.json']:
        assert all(executions[name]['helper_sha256_before'][n] == h for n, h in plan['site_source91_sha256'].items())
    qa = review.read(executions['source91-qa-check-execution-v1.json']['log'])
    assert len(qa) == 29
    assert {r['file'] for r in qa} == {Path(n).name for n in plan['site_source91_sha256'] if n.endswith('.html')}
    for row in qa:
        assert all(not row[k] for k in ['consoleErrors', 'pageErrors', 'leftoverDollar', 'katexErrors',
                                       'missingAnchors', 'brokenLinks', 'mobileOverflow', 'mobileOverflowExpanded'])
    ready_name = 'reports/solution-review/source91-release-ready-v1.json'
    docs_name = 'reports/solution-review/source91-documentation-v1.json'
    ready, docs = review.read(ready_name), review.read(docs_name)
    assert ready['formal_source_correspondence_for_rewritten_answers'] == 'pending_explicit_rebase'
    assert ready['site_source91_sha256'] == plan['site_source91_sha256']
    for ref in ready['evidence'] + docs['documents'] + docs['preserved_document_sources']:
        exact(ref)
    assert not docs['formal_coverage_promoted'] and not docs['actual_publication_claimed']
    installed_name = 'reports/solution-review/source91-installed-independent-review-v1.json'
    visual_name = 'reports/solution-review/source91-final-visual-review-v1.json'
    runtime_name = 'reports/solution-review/source91-runtime-delivery-independent-review-v1.json'
    pipeline_name = 'reports/solution-review/solution-release-independent-pipeline-review-v1.json'
    installed, visual, runtime, pipeline = (review.read(n) for n in [installed_name, visual_name, runtime_name, pipeline_name])
    assert all(v['status'].startswith('approved') and not v.get('errors') for v in [installed, visual, runtime, pipeline])
    assert installed['plan']['sha256'] == visual['release_plan']['sha256'] == review.ref(plan_name)['sha256']
    assert installed['counts']['exercises'] == 556 and installed['counts']['canonical_hints_preserved'] == 427
    assert visual['counts']['source_pages_inspected'] == 22
    for ref in [visual['capture_packet'], visual['capture_native_execution']] + runtime['helpers'] + pipeline['source_files']:
        exact(ref)
    audit_name = 'reports/solution-review/source91-lean-audit-export-v1.json'
    audit = review.read(audit_name)
    assert audit['proof_files'] == 1267 and audit['public_theorems'] == 11472 and audit['fresh_build_and_all_theorem_axiom_audit']
    exact(audit['relocated_report'])
    inventory_name = 'book/solutions/releases/source91-v1/source91-inventory/inventory.json'
    inventory = review.read(inventory_name)
    assert inventory['counts']['exercises'] == 556 and inventory['counts']['material_source_units'] == 14270
    after = {n: review.ref(n)['sha256'] for n in before}
    assert before == after
    report = {
        'schema': 'solutions.source91.final_reporting_independent.v1',
        'status': 'approved_current_source91_final_reporting_helpers',
        'reviewer': '/root/recovery_runner35', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'helpers': [review.ref(n) for n in helpers], 'release_plan': review.ref(plan_name),
        'reader_composition': {
            'current_composed_report': review.ref('reports/solution-review/source91-reader-browser-final-v1.json'),
            'exact_passing_rows_from_failed_full_v1': 28, 'exact_passing_rows_from_book_only_v2': 1,
            'pages': 29, 'exercise_total': 556, 'current_asset_hashes_checked': 31,
            'original_failed_native': review.ref(original_native_name), 'passing_retry_native': review.ref(retry_native_name),
            'original_failure_retained': True, 'row_origin_refs_and_indices_verified': True,
            'declared_oldest_first_order_verified_against_actual_start_times': private['oldest_first_native_start_times'],
            'selection_rule_review': 'A failed later supplied page attempt removes its earlier passing row; missing/unfinished pages are rejected. The CLI requires attempts oldest first, and this actual invocation supplies that order.'},
        'documentation': {
            'readiness': review.ref(ready_name), 'completed_receipt': review.ref(docs_name),
            'actual_completed_execution': review.ref('reports/solution-review/source91-documentation-execution-v1.json'),
            'actual_completed_rerun': review.ref('reports/solution-review/source91-documentation-resume-execution-v1.json'),
            'private_full_real_evidence_check': review.ref(private_name), 'exact_documents_checked': len(docs['documents']),
            'original_documents_preserved': len(docs['preserved_document_sources']),
            'counts': plan['counts'], 'source91_material_units': 14270,
            'source90_formal_counts_scope': ready['historical_checkpoint35_coverage_source90_only'],
            'rewritten_answer_formal_correspondence': 'pending_explicit_rebase',
            'source90_formal_counts_promoted_to_source91': False, 'actual_publication_claimed': False,
            'current_evidence_gates_checked': 'All556 approved/installed with exact plan, static integration, raw rendered-math QA29, exact composed reader QA29, actual selected proof build/export, installed-source review, visual22 and pipeline/runtime approvals. Current review verifies their exact referenced bytes.'},
        'resolved_defect': {
            'problem': 'The original writer could bind a late edit to an already installed document as successful selected documentation.',
            'fix': 'Recheck all six documents against their selected byte strings before creating the success receipt.',
            'historical_helper': historical['helper'],
            'historical_preservation_method': 'Recovered by reversing the observed four edits and matching the exact initial source SHA; not claimed to be a pre-execution copy.',
            'actual_historical_failing_regression': review.ref(historical_test_name),
            'actual_historical_failed_native': review.ref(failed_native_name),
            'current_passing_tests': review.ref(current_test_name), 'current_case_count': 5,
            'cases': [c['name'] for c in current_test['cases']],
            'current_final_guard_refuses_late_edit_without_success_receipt': True},
        'completed_native_evidence_checked': [review.ref('reports/solution-review/' + n) for n in execution_names],
        'independent_approval_records': [review.ref(n) for n in [installed_name, visual_name, runtime_name, pipeline_name]],
        'selected_proof_audit': review.ref(audit_name), 'selected_proof_count': 1267, 'selected_public_theorems': 11472,
        'kernel_provenance_scope': 'Fresh build and all-theorem axiom audit pass for unchanged selected proof statements; identical module/import kernel results retain original provenance. No rewritten-answer coverage rebase is inferred.',
        'source91_inventory': review.ref(inventory_name), 'issues': [], 'errors': [],
        'protected_before': before, 'protected_after': after,
        'canonical_or_publication_files_modified_by_reviewer': False,
        'limits': ['No additional full browser or Lean audit is executed by this reporting review; the real completed native records are checked.',
                   'The private generation executes all actual evidence gates; only its document/receipt output paths are redirected.',
                   'Publication commit, push, Pages and live hashes remain separate actual delivery work.']}
    review.json_put(report_name, report)
    print(json.dumps({'status': report['status'], 'report': review.ref(report_name)}))


if __name__ == '__main__':
    main()
