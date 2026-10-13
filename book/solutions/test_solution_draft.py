"""Check real draft CLI preservation in temporary authorized candidate folders."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import tempfile
import solution_review as review


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    manifest, records = review.load(review.BASELINE)
    row = next(r for r in records if r['source_file'] == 'SafeLearning/primer-basics.html' and r['authoring_file'].startswith('book/chapters/'))
    protected = {n: review.ref(n)['sha256'] for n in [row['source_file'], row['authoring_file'], review.INVENTORY,
        'book/solutions/validate_solution_draft.py', 'book/solutions/solution_review.py', Path(__file__).resolve().relative_to(review.ROOT).as_posix()]}
    cases = []
    with tempfile.TemporaryDirectory(prefix='.draft-validation-fixture-', dir=review.ROOT / 'book/solutions') as temporary:
        directory = Path(temporary).relative_to(review.ROOT).as_posix()
        proposal = dict(inventory_key=row['inventory_key'], source_file=row['source_file'],
            original_solution_sha256=row['solution']['sha256'], decision='replace',
            thoroughness_rationale='Temporary preservation test fixture; no adequacy judgment.',
            replacement_html=row['solution']['html'] + '<p>Temporary fixture α → β; never adopted into the curriculum.</p>')
        for case, changed, complete, expected in [
            ('canonical_and_authored_candidates_preserved', {}, False, 0),
            ('incorrect_original_hash_refused', {'original_solution_sha256': '0' * 64}, False, 1),
            ('new_solution_script_refused_before_outputs', {'replacement_html': row['solution']['html'] + '<script>fixture()</script>'}, False, 1),
            ('incomplete_page_decisions_refused', {}, True, 1)]:
            draft = directory + '/' + case + '.json'
            report = directory + '/' + case + '-report.json'
            output = directory + '/' + case + '-candidates'
            review.json_put(draft, [{**proposal, **changed}])
            command = [sys.executable, '-B', str(review.ROOT / 'book/solutions/validate_solution_draft.py'),
                '--draft', draft, '--output-dir', output, '--report', report]
            if complete:
                command.append('--require-complete-pages')
            result = subprocess.run(command, cwd=review.ROOT, capture_output=True, text=True, timeout=20)
            passed = result.returncode == expected
            if passed and expected == 0:
                artifact = review.read(report)
                passed = len(artifact['candidates']) == 2 and len(artifact['replaced']) == 1
                passed = passed and artifact['canonical_sources_modified'] is False and artifact['pedagogical_adequacy_claimed'] is False
                passed = passed and all(c['prompts_hints_non_solution_bytes_anchors_scripts_preserved'] for c in artifact['preservation_checks'])
            elif passed:
                passed = not review.path(output).exists()
            cases.append(dict(case=case, status='passed' if passed else 'failed', actual_command=command,
                actual_workdir=str(review.ROOT), actual_exit_code=result.returncode, expected_exit_code=expected,
                stdout=result.stdout, stderr=result.stderr))
    after = {n: review.ref(n)['sha256'] for n in protected}
    code = 0 if protected == after and all(c['status'] == 'passed' for c in cases) else 1
    artifact = dict(status='passed' if code == 0 else 'failed', actual_exit_code=code,
        baseline=review.ref(review.BASELINE + '/manifest.json'), input_sha256_before=protected, input_sha256_after=after,
        cases=cases, canonical_and_authoring_inputs_unchanged=True, fixtures_removed=True,
        scope='Real draft CLI, temporary synthetic proposal text and candidates only; no curriculum changes or pedagogical approvals.')
    review.json_put(args.report, artifact)
    print(json.dumps(dict(status=artifact['status'], cases=len(cases), report=args.report)))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
