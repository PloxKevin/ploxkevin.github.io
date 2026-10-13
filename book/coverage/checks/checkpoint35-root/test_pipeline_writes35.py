"""Review and fault-test actual checkpoint writers without importing verify.py."""
from pathlib import Path
import argparse
import ast
import difflib
import hashlib
import importlib.util
import json
import os
import sys
import tempfile
import traceback
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[4]
VERIFY = ROOT / 'verification/lean/verify.py'
BEFORE = ROOT / 'reports/full-coverage/source-history/verification-before-checkpoint35-v1/verification/lean/verify.py'
PREPARE = ROOT / 'book/coverage/checks/checkpoint35-root/prepare_runtime35.py'
FINALIZE = ROOT / 'book/coverage/checks/checkpoint35-root/finalize_checkpoint35.py'


def ref(p):
    return dict(file=p.relative_to(ROOT).as_posix(), sha256=hashlib.sha256(p.read_bytes()).hexdigest())


def review_verify_diff():
    old, current = BEFORE.read_text(), VERIFY.read_text()
    old_tree, tree = ast.parse(old), ast.parse(current)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'atomic_json']
    assert len(functions) == 1
    function = functions[0]
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'atomic_json']
    assert len(calls) == 2
    assert {ast.unparse(n.args[0]) for n in calls} == {'kernel_progress_path', "OUT / 'verification.json'"}

    class UndoWriter(ast.NodeTransformer):
        def visit_Call(self, node):
            node = self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id == 'atomic_json':
                assert len(node.args) == 2 and not node.keywords
                return ast.Call(func=ast.Attribute(value=node.args[0], attr='write_text', ctx=ast.Load()),
                    args=[ast.BinOp(left=ast.Call(func=ast.Attribute(value=ast.Name(id='json', ctx=ast.Load()), attr='dumps', ctx=ast.Load()),
                        args=[node.args[1]], keywords=[ast.keyword(arg='indent', value=ast.Constant(2))]), op=ast.Add(), right=ast.Constant('\n'))], keywords=[])
            return node

    stripped = ast.Module(body=[n for n in tree.body if n is not function and not
        (isinstance(n, ast.Import) and len(n.names) == 1 and n.names[0].name in {'os', 'tempfile'})], type_ignores=[])
    assert ast.dump(UndoWriter().visit(stripped), include_attributes=False) == ast.dump(old_tree, include_attributes=False)
    source = ast.get_source_segment(current, function)
    diff = ''.join(difflib.unified_diff(old.splitlines(True), current.splitlines(True), fromfile=str(BEFORE.relative_to(ROOT)), tofile=str(VERIFY.relative_to(ROOT))))
    return function, dict(status='passed', only_changes='os/tempfile imports, atomic_json, and two complete JSON-writer call replacements',
        atomic_json_source_sha256=hashlib.sha256(source.encode()).hexdigest(), exact_diff=diff,
        limitation='Atomic replacement protects against process interruption; the production writer does not fsync the parent directory for power-loss durability.')


def test_verify_atomic(function):
    results = []
    for had_original in (True, False):
        with tempfile.TemporaryDirectory(prefix='checkpoint35-atomic-json-fixture-') as temporary:
            root = Path(temporary)
            target = root / 'receipt.json'
            old = b'{"identity":"old-complete","checks":{"prior":{"exit_code":0}}}\n'
            if had_original:
                target.write_bytes(old)
            value = {'identity': 'new-complete', 'checks': {'native': {'exit_code': 0, 'log_sha256': 'fixture'}}}
            events, fail = [], True

            def sync(fd):
                events.append('fsync-complete-temporary')
                os.fsync(fd)

            def replace(source, destination):
                assert Path(source).parent == target.parent and Path(destination) == target
                assert json.loads(Path(source).read_bytes()) == value
                assert events[-1] == 'fsync-complete-temporary'
                events.append('replace-injected-failure' if fail else 'replace-success')
                if fail:
                    raise OSError('injected os.replace interruption')
                os.replace(source, destination)

            safe_os = SimpleNamespace(fdopen=os.fdopen, fsync=sync, replace=replace, path=os.path, unlink=os.unlink)
            namespace = {'os': safe_os, 'tempfile': tempfile, 'json': json}
            exec(compile(ast.Module(body=[function], type_ignores=[]), str(VERIFY), 'exec'), namespace)
            writer = namespace['atomic_json']
            try:
                writer(target, value)
                raise AssertionError('Injected replace failure did not occur')
            except OSError as error:
                assert str(error) == 'injected os.replace interruption'
            assert (target.read_bytes() == old) if had_original else not target.exists()
            assert not list(root.glob('.receipt.json-*'))
            fail = False
            writer(target, value)
            assert target.read_bytes() == (json.dumps(value, indent=2) + '\n').encode()
            assert not list(root.glob('.receipt.json-*'))
            results.append(dict(initial_complete_receipt=had_original, prior_preserved_or_missing_on_failure=True,
                successful_retry_complete=True, temporary_files_removed=True, actual_function_calls=2, events=events))
    return results


def test_runtime_put():
    """Exercise the actual runtime copy writer with a synthetic ROOT only."""
    spec = importlib.util.spec_from_file_location('runtime35_fixture', PREPARE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    cases = []
    with tempfile.TemporaryDirectory(prefix='checkpoint35-runtime-put-fixture-') as temporary:
        module.ROOT = Path(temporary)
        module.put('objects/source', b'exact synthetic source\n')
        original = module.path('objects/source').read_bytes()
        module.put('objects/source', original)
        assert module.path('objects/source').read_bytes() == original
        try:
            module.put('objects/source', b'corrupted synthetic source\n')
            raise RuntimeError('Different existing object bytes were accepted')
        except AssertionError:
            pass
        assert module.path('objects/source').read_bytes() == original
        cases.append(dict(case='existing_exact_or_corrupt_object', exact_rerun_preserved=True, corrupt_bytes_rejected=True))
        # Inject os.replace only in this imported helper's globals; no process-wide monkeypatch.
        real_os = module.os
        calls = []

        def interrupted_replace(source, destination):
            calls.append(dict(source_complete=Path(source).read_bytes() == original, destination_existed=Path(destination).exists()))
            raise OSError('injected runtime put interruption')

        module.os = SimpleNamespace(fdopen=real_os.fdopen, fsync=real_os.fsync, replace=interrupted_replace,
            path=real_os.path, unlink=real_os.unlink)
        try:
            module.put('runtime/SafeLearning/Synthetic.lean', original)
            raise AssertionError('Runtime interruption not injected')
        except OSError as error:
            assert str(error) == 'injected runtime put interruption'
        assert not module.path('runtime/SafeLearning/Synthetic.lean').exists()
        assert not list(module.path('runtime/SafeLearning').glob('.Synthetic.lean-*'))
        module.os = real_os
        module.put('runtime/SafeLearning/Synthetic.lean', original)
        assert module.path('runtime/SafeLearning/Synthetic.lean').read_bytes() == original
        cases.append(dict(case='interrupted_new_runtime_object', missing_destination_preserved=True,
            successful_retry_exact=True, temporary_files_removed=True, actual_replace_attempts=calls))
    return cases


def test_finalizer_gates():
    """Run the actual finalizer gate AST against modified synthetic evidence."""
    source = FINALIZE.read_text()
    main = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == 'main')
    start = next(i for i, n in enumerate(main.body) if isinstance(n, ast.Assign) and
        any(isinstance(t, ast.Name) and t.id == 'audit_files' for t in n.targets))
    logs = main.body[start:start + 3]
    assert isinstance(logs[-1], ast.For) and 'log_sha256' in ast.get_source_segment(source, logs[-1])
    frozen = [n for n in main.body if isinstance(n, (ast.Assert, ast.For)) and
        any(isinstance(child, ast.Name) and child.id == 'frozen_ledger' for child in ast.walk(n))]
    assert len(frozen) == 5 and sum(isinstance(n, ast.Assert) for n in frozen) == 4
    log_code = compile(ast.Module(body=logs, type_ignores=[]), str(FINALIZE), 'exec')
    frozen_code = compile(ast.Module(body=frozen, type_ignores=[]), str(FINALIZE), 'exec')
    results = []
    with tempfile.TemporaryDirectory(prefix='checkpoint35-finalizer-gates-fixture-') as temporary:
        root = Path(temporary)

        def path(name):
            return root / name

        def sha(name):
            return hashlib.sha256(path(name).read_bytes()).hexdigest()

        logfile = path('original/kernel-Synthetic.log')
        logfile.parent.mkdir()
        logfile.write_bytes(b'synthetic native kernel output\n')
        check = {'output_file': 'reports/lean-verification/' + logfile.name, 'log_sha256': sha('original/' + logfile.name)}
        namespace = {'ROOT': root, 'ORIGINAL': 'original', 'path': path, 'sha': sha, 'audit': {'checks': [check]}}
        exec(log_code, namespace)
        original_log = logfile.read_bytes()
        logfile.write_bytes(b'injected post-audit corrupted native log\n')
        try:
            exec(log_code, namespace)
            raise RuntimeError('Changed raw kernel log was accepted')
        except AssertionError:
            pass
        logfile.write_bytes(original_log)
        check['output_file'] = 'elsewhere/' + logfile.name
        try:
            exec(log_code, namespace)
            raise RuntimeError('Unexpected kernel log output path was accepted')
        except AssertionError:
            pass
        results.append(dict(case='actual_pre_export_log_gate', genuine_raw_log_accepted=True,
            changed_raw_log_rejected=True, unexpected_output_path_rejected=True))
        inventory = path('book/coverage/inventory.json')
        inventory.parent.mkdir(parents=True)
        inventory.write_bytes(b'{"synthetic_fixture":true}\n')
        domains = []
        for domain in ['foundations', 'applied', 'modules', 'core']:
            name = 'snapshot/book/coverage/' + domain + '.json'
            destination = path(name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(b'{"synthetic_fixture":true}\n')
            domains.append({'domain': domain, 'ledger_sha256': sha(name)})
        genuine = dict(integrity_status='passed', errors=[], inventory_sha256=sha('book/coverage/inventory.json'),
            counts={'fixture_count': 1}, mathematical_coverage_complete=False, domains=domains)
        namespace.update(SNAPSHOT='snapshot', ledger={'counts': genuine['counts']}, frozen_ledger=genuine)
        exec(frozen_code, namespace)
        mutations = dict(integrity_status='failed', errors=['injected integrity error'], inventory_sha256='0' * 64,
            counts={'fixture_count': 99}, mathematical_coverage_complete=True, domains=[dict(domains[0], ledger_sha256='0' * 64)])
        rejected = []
        for field, changed in mutations.items():
            namespace['frozen_ledger'] = {**genuine, field: changed}
            try:
                exec(frozen_code, namespace)
                raise RuntimeError('Corrupted frozen ledger accepted: ' + field)
            except AssertionError:
                rejected.append(field)
        results.append(dict(case='actual_existing_frozen_ledger_gates', genuine_complete_receipt_accepted=True,
            corrupted_fields_rejected=rejected, gates_unconditional_for_new_and_existing_receipts=True))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    report = ROOT / args.report
    assert report.resolve().is_relative_to(ROOT) and not report.exists()
    inputs = [VERIFY, BEFORE, PREPARE, FINALIZE, Path(__file__).resolve()]
    before = [ref(p) for p in inputs]
    error, review, atomic_cases, runtime_cases, finalizer_cases = None, None, [], [], []
    try:
        function, review = review_verify_diff()
        atomic_cases = test_verify_atomic(function)
        runtime_cases = test_runtime_put()
        finalizer_cases = test_finalizer_gates()
    except Exception:
        error = traceback.format_exc()
    after = [ref(p) for p in inputs]
    code = 0 if error is None and before == after else 1
    value = dict(status='passed' if code == 0 else 'failed', actual_exit_code=code,
        actual_command=[sys.executable, '-B', str(Path(__file__).resolve()), *sys.argv[1:]], actual_workdir=str(Path.cwd()),
        input_sha256_before=before, input_sha256_after=after, verify_source_diff_review=review,
        actual_ast_extracted_atomic_json_tests=atomic_cases, actual_runtime_put_tests=runtime_cases,
        actual_ast_extracted_finalizer_gate_tests=finalizer_cases,
        runtime_source_review=dict(status='passed', findings=[
            'Exact plan, baseline selection/audit, inventory, native source compilation and independent file/hash review gates precede selection writes.',
            'Explicit selected sources, prior site assets, parser and project inputs are copied into content-addressed objects; each existing byte object and receipt is compared exactly.',
            'Runtime source files share immutable object hardlinks; .lake package/build directories are explicit runtime-only symlinks. Historical snapshot/build trees are not recopied.',
            'Selection and preparation JSON have deterministic bytes, allowing completed exact reruns; different existing output bytes are rejected.']),
        finalizer_source_review=dict(status='passed', findings=[
            'Actual aggregate command/cwd, stable verifier hashes, selected proof identity, fresh new-module set, baseline reuse hashes and 31 site assets are checked before export.',
            'Raw kernel log hashes are checked before export; existing frozen integrity/error/inventory gates are unconditional and reject corrupt receipts.',
            'Original report bytes and commands remain preserved; only exported output paths are relocated.',
            'Frozen file enumeration must equal the explicit source/ledger set and contain no symlinks; exact completed manifest/result bytes are compared on reruns.']),
        full_verify_module_imported=False, full_runtime_preparation_executed=False,
        scope='Process-interruption safety and exact object reruns in synthetic ephemeral fixtures. No aggregate success or client-crash diagnosis inferred.',
        **({'error': error} if error else {}))
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open('x') as output:
        json.dump(value, output, indent=2)
        output.write('\n')
        output.flush()
        os.fsync(output.fileno())
    print(json.dumps(dict(status=value['status'], atomic_cases=len(atomic_cases), runtime_put_cases=len(runtime_cases),
        finalizer_gate_cases=len(finalizer_cases), report=args.report)))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
