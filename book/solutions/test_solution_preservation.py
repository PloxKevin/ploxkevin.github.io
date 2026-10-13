"""Test actual Source90 byte-range validation using in-memory candidate edits."""
from pathlib import Path
import argparse
import json
import sys
import traceback
import solution_review as review


def swap(raw, span, replacement):
    return raw[:span['start_byte']] + replacement + raw[span['end_byte']:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    manifest, records = review.load(review.BASELINE)
    source = 'SafeLearning/primer-linalg.html'
    rows = [r for r in records if r['source_file'] == source]
    row = next(r for r in rows if r['hints'] and r['authoring_file'] == source)
    raw = review.path(manifest['source_snapshots'][source]['file']).read_bytes()
    before = {n: review.ref(n)['sha256'] for n in [source, 'book/chapters/primer-linalg.html', 'page_contract.md',
        review.INVENTORY, review.SELF.relative_to(review.ROOT).as_posix(), Path(__file__).resolve().relative_to(review.ROOT).as_posix()]}
    cases = []

    def run(name, candidate, should_pass, file=source):
        error, accepted = None, False
        try:
            value = review.validate_candidate(manifest, records, file, candidate)
            accepted = True
            assert value['pedagogical_adequacy_claimed'] is False
        except (AssertionError, ValueError, KeyError) as exception:
            error = str(exception)
        cases.append(dict(case=name, status='passed' if accepted == should_pass else 'failed',
            candidate_accepted=accepted, expected_acceptance=should_pass, **({'rejection_reason': error} if error else {})))

    span = row['solution']['range']
    body = raw[span['start_byte']:span['end_byte']]
    run('unchanged_full_page', raw, True)
    run('unicode_and_newline_solution_only_swap', swap(raw, span, body + '\n<p>Temporary validation fixture: α → β &amp; γ.</p>\n'.encode()), True)
    problem = next(p for p in row['problem']['fragments'] if p['text'])
    pspan = problem['range']
    original = raw[pspan['start_byte']:pspan['end_byte']]
    run('prompt_bytes_changed', swap(raw, pspan, original.replace(b'<p', b'<p data-changed="yes"', 1)), False)
    hint = row['hints'][0]['body']['range']
    run('hint_bytes_changed', swap(raw, hint, b'<p>Changed independent hint.</p>'), False)
    run('non_solution_whitespace_changed', b'\n' + raw, False)
    run('new_script_inside_solution_rejected', swap(raw, span, body + b'<script>console.log("fixture")</script>'), False)
    run('new_anchor_inside_solution_rejected', swap(raw, span, body + b'<p id="fixture-new-anchor">Fixture</p>'), False)
    run('new_inline_script_hook_rejected', swap(raw, span, body + b'<p onclick="alert(1)">Fixture</p>'), False)
    disclosure = row['solution']['disclosure_range']
    markup = raw[disclosure['start_byte']:disclosure['end_byte']]
    run('solution_disclosure_summary_changed', swap(raw, disclosure, markup.replace(b'Show worked solution', b'Show changed answer', 1)), False)
    run('solution_body_empty_rejected', swap(raw, span, b'\n '), False)
    author = 'book/chapters/primer-linalg.html'
    authored_raw = review.path(manifest['source_snapshots'][author]['file']).read_bytes()
    authored_row = next(r for r in rows if r['authoring_file'] == author)
    authored_span = authored_row['authoring']['solution_range']
    authored_body = authored_raw[authored_span['start_byte']:authored_span['end_byte']]
    run('authored_fragment_solution_only_swap', swap(authored_raw, authored_span, authored_body + b'<p>Temporary authored validation fixture.</p>'), True, author)
    case_source = 'book/case-studies.html'
    case_raw = review.path(manifest['source_snapshots'][case_source]['file']).read_bytes()
    case_row = next(r for r in records if r['authoring_file'] == case_source)
    case_span = case_row['authoring']['solution_range']
    case_body = case_raw[case_span['start_byte']:case_span['end_byte']]
    run('plain_paragraph_slot_can_gain_a_div', swap(case_raw, case_span, b'<div>' + case_body + b'</div>'), True, case_source)
    after = {n: review.ref(n)['sha256'] for n in before}
    code = 0 if before == after and all(c['status'] == 'passed' for c in cases) else 1
    result = dict(status='passed' if code == 0 else 'failed', actual_exit_code=code,
        actual_command=[sys.executable, '-B', str(Path(__file__).resolve()), *sys.argv[1:]], actual_workdir=str(Path.cwd()),
        baseline=review.ref(review.BASELINE + '/manifest.json'), input_sha256_before=before, input_sha256_after=after,
        cases=cases, canonical_or_authoring_files_modified=False,
        scope='In-memory mechanical preservation fixtures only. No fixture text is merged into the curriculum or counted as a pedagogical improvement.')
    review.json_put(args.report, result)
    print(json.dumps(dict(status=result['status'], cases=len(cases), failed_cases=[c['case'] for c in cases if c['status'] != 'passed'], report=args.report)))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
