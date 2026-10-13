"""Exercise the actual documentation-install tail in isolated temporary roots.

Approval inputs are not simulated as successful release evidence: this test
extracts only the writer's preflight/copy/receipt block by AST. It tests byte
preservation and recovery, never edits the real documents or publication tree.
"""
import argparse
import ast
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
import solution_release as release

HELPER = 'book/solutions/prepare_solution_documentation.py'
DOCS = ['README.md', 'book/coverage/progress.json', 'book/coverage/CONTINUATION.md',
        'reports/full-coverage/README.md', 'verification/lean/README.md']
HISTORY = 'reports/solution-review/source-history/before-source91-documentation-v1'
READY = 'reports/solution-review/source91-release-ready-v1.json'
RECEIPT = 'reports/solution-review/source91-documentation-v1.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    helper_raw = (ROOT / HELPER).read_bytes()
    tree = ast.parse(helper_raw, filename=HELPER)
    function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
    bodies_index = next(i for i, n in enumerate(function.body)
                        if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'bodies' for t in n.targets))
    install_nodes = function.body[bodies_index + 1:]
    assert isinstance(install_nodes[0], ast.For)
    compiled = compile(ast.fix_missing_locations(ast.Module(body=install_nodes, type_ignores=[])), HELPER, 'exec')
    original_atomic_copy = release.atomic_copy
    cases = []

    def run_case(name):
        with tempfile.TemporaryDirectory(prefix='source91-doc-review-') as temporary:
            fixture = Path(temporary)
            review.ROOT = fixture
            bodies = {n: ('selected complete bytes: ' + n + '\n').encode() for n in DOCS + ['book/solutions/RELEASE.md']}
            for n in DOCS:
                old = ('original complete bytes: ' + n + '\n').encode()
                target = review.path(n)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(old)
                review.put(HISTORY + '/' + n, old)
            helper_target = review.path(HELPER)
            helper_target.parent.mkdir(parents=True, exist_ok=True)
            helper_target.write_bytes(helper_raw)
            review.json_put(READY, {'status': 'isolated_writer_fixture_not_release_evidence'})
            scope = {'review': review, 'release': release, 'Path': Path, 'json': json,
                     '__file__': str(helper_target), 'HISTORY': HISTORY, 'READY': READY,
                     'doc_names': DOCS, 'bodies': bodies, 'plan': {'counts': {'fixture_only': True}}}
            copies = []
            injection_done = False
            edited = b'unplanned late user edit; must be preserved\n'

            def copy(target, data):
                nonlocal injection_done
                copies.append(target.relative_to(fixture).as_posix())
                if name == 'interruption_resume' and len(copies) == 2 and not injection_done:
                    injection_done = True
                    raise OSError('injected interruption before second document install')
                original_atomic_copy(target, data)
                if name == 'late_unvisited_edit' and len(copies) == 1:
                    review.path(DOCS[1]).write_bytes(edited)
                if name == 'late_already_installed_edit' and len(copies) == 2:
                    review.path(DOCS[0]).write_bytes(edited)

            release.atomic_copy = copy
            if name == 'unplanned_preflight':
                review.path(DOCS[-1]).write_bytes(edited)
            error = None
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    exec(compiled, scope)
            except (AssertionError, OSError) as exc:
                error = str(exc)
            existed_after_first = review.path(RECEIPT).exists()
            if name == 'interruption_resume':
                assert error and not existed_after_first
                assert review.path(DOCS[0]).read_bytes() == bodies[DOCS[0]]
                assert review.path(DOCS[1]).read_bytes() != bodies[DOCS[1]]
                with contextlib.redirect_stdout(io.StringIO()):
                    exec(compiled, scope)
            if name in {'normal_and_completed_replay', 'interruption_resume'}:
                assert all(review.path(n).read_bytes() == data for n, data in bodies.items())
                assert review.path(RECEIPT).exists()
                receipt_before = review.path(RECEIPT).read_bytes()
                copies_before = len(copies)
                with contextlib.redirect_stdout(io.StringIO()):
                    exec(compiled, scope)
                assert len(copies) == copies_before
                assert review.path(RECEIPT).read_bytes() == receipt_before
                passed = True
            elif name == 'unplanned_preflight':
                passed = bool(error) and not copies and not existed_after_first
                assert review.path(DOCS[-1]).read_bytes() == edited
            elif name == 'late_unvisited_edit':
                passed = bool(error) and len(copies) == 1 and not existed_after_first
                assert review.path(DOCS[1]).read_bytes() == edited
            else:
                assert name == 'late_already_installed_edit'
                assert review.path(DOCS[0]).read_bytes() == edited
                passed = bool(error) and not existed_after_first
            value = {'name': name, 'passed': passed, 'observed_error': error,
                     'actual_atomic_copy_targets': copies, 'success_receipt_after_first_attempt': existed_after_first,
                     'all_selected_document_bytes_match': all(review.path(n).read_bytes() == data for n, data in bodies.items())}
            if name == 'late_already_installed_edit' and existed_after_first:
                receipt = review.read(RECEIPT)
                bound = next(r for r in receipt['documents'] if r['file'] == DOCS[0])
                value['unexpected_late_edit_incorrectly_bound_as_success'] = bound['sha256'] == review.sha(edited)
                value['claimed_status'] = receipt['status']
            cases.append(value)

    try:
        for name in ['normal_and_completed_replay', 'interruption_resume', 'unplanned_preflight',
                     'late_unvisited_edit', 'late_already_installed_edit']:
            run_case(name)
    finally:
        review.ROOT = ROOT
        release.atomic_copy = original_atomic_copy
    assert (ROOT / HELPER).read_bytes() == helper_raw
    report = {'status': 'passed' if all(c['passed'] for c in cases) else 'failed_documentation_final_byte_guard',
              'helper': review.ref(HELPER), 'test_helper': review.ref(Path(__file__).relative_to(ROOT).as_posix()),
              'actual_command': sys.argv, 'cwd': str(Path.cwd()), 'cases': cases,
              'extracted_actual_source_lines': [install_nodes[0].lineno, install_nodes[-1].end_lineno],
              'scope': 'Actual writer tail, immutable receipt writer, and atomic copier execute in private temporary roots. Release readiness gates and real document generation are not executed. No canonical or publication file is modified.'}
    review.json_put(args.report, report)
    print(json.dumps({'status': report['status'], 'passed_cases': sum(c['passed'] for c in cases),
                      'total_cases': len(cases), 'report': review.ref(args.report)}))
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
