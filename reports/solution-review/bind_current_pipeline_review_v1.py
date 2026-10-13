"""Record independent static findings and already executed failure tests."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
import solution_release as release


def main():
    report = 'reports/solution-review/solution-release-independent-pipeline-review-v1.json'
    source = {
        'book/solutions/solution_release.py': '2d0e07e4fa2f88fb0ef4a69070f40bf65bdedd65a1720237f201206d4ea86123',
        'book/solutions/test_solution_release.py': 'd63a387b97c84c2c6288a3d7b08b71b78177d4caaa6ad40d5705b7b27c57291a',
        'book/solutions/stage_solution_publication.py': '9bc102ffbe3ff7534e472927e6552871469c4d08acce6781621d4d0afc7be541',
        'book/validate.py': '7570f0a46961211ed8700f954f50ce7d8ab3d80e3f5574cc1d59e4069ea7d901',
        'qa/check.mjs': 'e14438a678f68dc05cda7f13338adcad22ce18a5c4803cf50929dccc3f093a47'}
    for file, digest in source.items():
        assert review.ref(file)['sha256'] == digest, file
    tests = ['reports/solution-review/independent-approval-gate-v1.json',
             'reports/solution-review/independent-release-failure-injections-v2.json',
             'reports/solution-review/independent-publication-staging-v1.json',
             'reports/solution-review/independent-gp-readiness-v1.json']
    executed = []
    for file in tests:
        result = review.read(file)
        assert result['status'].startswith('passed') and not result.get('defects')
        for item in result['protected_inputs_before']:
            if item['file'] in source:
                assert item['sha256'] == source[item['file']]
        executed.append(dict(report=review.ref(file), status=result['status'], cases=len(result['cases'])))
    exact_file = 'book/solutions/solution_release.py'
    exact_ref = {**review.ref(exact_file), 'bytes': review.path(exact_file).stat().st_size}
    assert release.exact(exact_ref) == review.path(exact_file)
    try:
        release.exact({**exact_ref, 'bytes': exact_ref['bytes'] + 1})
    except AssertionError as error:
        assert str(error).startswith('Bound byte count differs:')
        optional_bytes_check = 'passed_actual_matching_optional_bytes_and_mismatch_refusal'
    else:
        raise AssertionError('Incorrect optional byte count accepted')
    history = [
        'reports/solution-review/source-history/book-validate-before-solutions-v1.py',
        'reports/solution-review/source-history/qa-check-before-solutions-v1-reconstructed.mjs',
        'reports/solution-review/source-history/solution-release-before-ref-metadata-v1.py',
        'reports/solution-review/source-history/solution_release-before-late-edit-guard-v1.py',
        'reports/solution-review/source-history/stage_solution_publication-before-late-edit-guard-v1.py',
        'reports/solution-review/source-history/stage_solution_publication-before-independent-runtime-fixes-v1.py']
    prior_failure = 'reports/solution-review/independent-release-failure-injections-v1.json'
    assert review.read(prior_failure)['status'] == 'needs_release_pipeline_revision'
    book_report = 'reports/solution-review/pre-release-source90-book-integration-v2.json'
    book_native = 'reports/solution-review/pre-release-source90-book-validation-execution-v2.json'
    assert review.read(book_report)['status'] == 'PASS'
    native = review.read(book_native)
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert native['helper_sha256_before']['book/validate.py'] == source['book/validate.py']
    assert native['helper_sha256_after']['book/validate.py'] == source['book/validate.py']
    protected = [*source, *tests, *history, prior_failure, book_report, book_native,
                 Path(__file__).relative_to(ROOT).as_posix()]
    before = [review.ref(file) for file in protected]
    findings = [
        dict(area='approval_gating', verdict='approved', reasoning='The selector requires all556 exact Source90 inventory keys, approved queue statuses, hash-bound drafts and independent reports, matching original/selected solution hashes and decisions, and exercise-specific reasoning with no remaining issues. It requires22 selected drafts and22 independent reports. The six isolated complete-queue cases exercise the actual selector; they assert identities and refusals, never real pedagogical adequacy.'),
        dict(area='source_and_authoring_preservation', verdict='approved', reasoning='Preparation requires the exact Source90 all31 asset map and every immutable canonical/authoring snapshot, then uses the complete-page byte-splicing adapter. Installation accepts exact before/after bytes, validates every target again just before replacement, checks installed bytes before each immutable receipt and checks all31 assets before success. The final checker reads actual installed solutions, matches each selected body, reverses only the explicit readiness exception and verifies all remaining page bytes, questions, hints, anchors and scripts. Book labs are checked at both normal authoring and publication paths.'),
        dict(area='interruption_and_failure', verdict='approved_after_concrete_fix', reasoning='A real late second-target edit was previously overwritten after initial preflight. The preserved v1 injection records that defect honestly. Current code refuses the edit without overwriting it or writing success. Actual replacement failure cleans its scratch file and leaves the old file complete; interruption after replacement but before receipt leaves exact after/before bytes and resumes. Same-record simultaneous installation is refused by flock, and completed installation receipts remain immutable.'),
        dict(area='book_validation_diff', verdict='approved', reasoning='Read the complete diff against the preserved original. The internal approved_preservation_sources argument affects only historical pre-book comparison after the release wrapper proves exact current-byte preservation. Actual page parsing, counts, links, authored labs, anchors, scripts and disposable real-build idempotence continue to inspect current site bytes. Historical mathematical corrections are reversed as a chronological chain on the complete source before insertion removal, then the complete remaining body must equal the oldest baseline. This handles corrections inside insertion spans and intermediate preimages without broadening the allowed edit set.'),
        dict(area='gp_readiness_formatting_exception', verdict='approved_exact_bounded_exception', reasoning='The only additional source exception replaces the one malformed Cauchy–Schwarz closing delimiter in an uncounted readiness question. The actual AST-extracted repair appears once outside exercise-solution ranges. Twenty counted exercises retain exact questions, hints, solutions, IDs and scripts. The ordinary solution-only gate refuses the formatting change; reversing that one documented substitution restores every original byte, while unrelated outside edits remain refused. This is formatting repair evidence, not a new exercise or a mathematical-source rebase.'),
        dict(area='qa_output_directory_diff', verdict='approved', reasoning='The complete diff against the explicitly reconstructed prior QA helper changes only screenshot-directory selection: SAFELEARNING_QA_SHOTS may select a new artifact directory, otherwise the previous directory remains. Browser checks and their logic are unchanged. The comparison source is described as reconstructed; no false prior byte-preservation claim is made.'),
        dict(area='publication_staging', verdict='approved', reasoning='Preparation requires clean main at the supplied expected HEAD and records every root source SHA and destination before SHA. Paths reject traversal, symlinks, Git/cache/runtime/archive/source-object destinations. Apply requires the exact plan/ready/helper/file-list bindings, rejects unrelated dirty files, performs all-before preflight and rechecks each source/destination before copying, then verifies installed hashes. The separately copied plan now has its own late source/destination guards and exact final SHA. Final checks require the ready report all31 site hashes and only intended dirty paths. Ten actual disposable Git fixtures cover these gates, post-replacement interruption, zero-copy completed replay, immutable receipt and late edits. The actual publication checkout remained unchanged; the helper runs only Git read commands and Root handles real add/commit/push.'),
        dict(area='formal_coverage_scope', verdict='approved', reasoning='The release binds the historical checkpoint35 proof audit as prior evidence and explicitly marks rewritten-answer formal source correspondence pending an explicit rebase. Installation and integration receipts do not claim new proof coverage; pedagogical review, source preservation and browser checks are distinct records. No proof, owner, coverage ledger or historical receipt is edited by these helpers.')]
    after = [review.ref(file) for file in protected]
    assert before == after
    result = dict(schema_version=1, status='approved_current_solution_release_pipeline',
        reviewer='/root/recovery_runner35 independent of pipeline author',
        source_files=[dict(file=file, sha256=digest) for file, digest in source.items()],
        source_history=[review.ref(file) for file in history],
        prior_actual_failed_fixture=review.ref(prior_failure), resolved_defects=['Late destination edits after preflight were overwritten; current guards refuse and preserve them.'],
        independent_failure_and_identity_tests=executed, independent_test_case_count=sum(r['cases'] for r in executed),
        optional_reference_bytes=optional_bytes_check, inspected_existing_test_scope='Real pending queue refusal plus isolated two-file installation fixtures; loader bypass is explicitly fixture-only.',
        current_pre_release_book_validation=dict(report=review.ref(book_report), native_execution=review.ref(book_native)),
        findings=findings, issues=[], protected_inputs_before=before, protected_inputs_after=after,
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT),
        real_release_installation_executed_by_reviewer=False, actual_publication_checkout_written=False,
        canonical_sources_modified=False, new_formal_source_correspondence_claimed=False,
        scope='Independent static pipeline review plus26 isolated runtime/identity/formatting cases. Root executes and verifies the concrete full installation and publication plans separately.')
    review.json_put(report, result)
    print(json.dumps(dict(status=result['status'], report=review.ref(report), independent_cases=result['independent_test_case_count'])))


if __name__ == '__main__':
    main()
