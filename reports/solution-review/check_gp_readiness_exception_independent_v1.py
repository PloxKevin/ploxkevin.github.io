"""Verify the exact GP readiness delimiter exception without installing it."""
import argparse
import ast
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    helper = 'book/solutions/solution_release.py'
    protected = [Path(__file__).relative_to(ROOT).as_posix(), helper,
                 'book/solutions/solution_review.py', 'book/solutions/baseline-source90/manifest.json',
                 'book/solutions/baseline-source90/pages/toolkit-gp.html.json',
                 'SafeLearning/toolkit-gp.html', 'book/chapters/toolkit-gp.html']
    before = [review.ref(f) for f in protected]
    tree = ast.parse(review.path(helper).read_text())
    prepare = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'prepare')
    assignments = [n for n in ast.walk(prepare) if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == 'repairs' for t in n.targets)]
    assert len(assignments) == 1
    repairs = ast.literal_eval(assignments[0].value)
    assert len(repairs) == 1 and repairs[0]['source_file'] == 'SafeLearning/toolkit-gp.html'
    repair = repairs[0]
    assert not repair['semantic_question_changed'] and not repair['hint_changed']
    manifest, baseline = review.load(review.BASELINE)
    snapshot = manifest['source_snapshots'][repair['source_file']]
    assert review.ref(snapshot['file']) == snapshot
    raw = review.path(snapshot['file']).read_bytes()
    a, b = repair['before'].encode(), repair['after'].encode()
    assert raw.count(a) == 1 and raw.count(b) == 0
    index = raw.index(a)
    records = [e for e in baseline if e['source_file'] == repair['source_file']]
    assert records
    assert all(not (e['solution']['range']['start_byte'] <= index < e['solution']['range']['end_byte']) for e in records)
    candidate = raw.replace(a, b, 1)
    original_doc, candidate_doc = review.Document(raw), review.Document(candidate)
    assert len(original_doc.exercises()) == len(candidate_doc.exercises()) == len(records)
    for source, original, changed in zip(records, original_doc.exercises(), candidate_doc.exercises()):
        old = review.parts(original_doc, original, source['solution']['container_kind'])
        new = review.parts(candidate_doc, changed, source['solution']['container_kind'])
        for section in ['problem', 'solution']:
            assert old[section]['html'] == new[section]['html']
        assert [h['disclosure']['html'] for h in old['hints']] == [h['disclosure']['html'] for h in new['hints']]
    scripts = lambda doc: [doc.raw[doc.byte(n.start):doc.byte(n.end)] for n in doc.nodes if n.tag == 'script']
    assert scripts(original_doc) == scripts(candidate_doc)
    assert [n.attrs['id'] for n in original_doc.nodes if 'id' in n.attrs] == [n.attrs['id'] for n in candidate_doc.nodes if 'id' in n.attrs]
    try:
        review.validate_candidate(manifest, baseline, repair['source_file'], candidate)
    except AssertionError as error:
        assert str(error) == 'Non-solution page bytes changed'
        refusal = str(error)
    else:
        raise AssertionError('Unrecorded readiness exception was accepted as a solution-only edit')
    assert candidate.count(a) == 0 and candidate.count(b) == 1
    restored = candidate.replace(b, a, 1)
    assert restored == raw
    validated = review.validate_candidate(manifest, baseline, repair['source_file'], restored)
    assert validated['status'] == 'passed_solution_only_preservation'
    try:
        review.validate_candidate(manifest, baseline, repair['source_file'], restored + b'\n<!-- unrelated extra edit -->\n')
    except AssertionError as error:
        assert str(error) == 'Non-solution page bytes changed'
    else:
        raise AssertionError('An unrelated non-solution edit was hidden by the exception')
    after = [review.ref(f) for f in protected]
    assert before == after
    result = dict(status='passed_independent_exact_gp_readiness_exception',
        helper=review.ref(helper), test=review.ref(Path(__file__).relative_to(ROOT).as_posix()),
        source_snapshot=snapshot, exact_exception=repair,
        in_memory_candidate_sha256=review.sha(candidate), restored_source_sha256=review.sha(restored),
        cases=['unique_bounded_delimiter_repair_outside_exercise_solutions',
               'all_counted_questions_hints_solutions_anchors_scripts_unchanged',
               'plain_solution_only_gate_refuses_the_exception',
               'one_recorded_reverse_operation_restores_exact_original_bytes',
               'unrelated_non_solution_edit_still_refused'],
        exercise_count=len(records), unrecorded_exception_actual_refusal=refusal,
        protected_inputs_before=before, protected_inputs_after=after,
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT),
        canonical_sources_modified=False, browser_or_formal_verification_claimed=False)
    review.json_put(args.report, result)
    print(json.dumps(dict(status=result['status'], cases=len(result['cases']), report=review.ref(args.report))))


if __name__ == '__main__':
    main()
