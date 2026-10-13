"""Isolated data-flow/failure fixtures for the Source91 runtime helpers.

Every helper executes against a temporary synthetic root. Lean execution, GitHub
responses and HTTP responses are synthetic inputs; no canonical source, native
Lean evidence, owner ledger or publication repository is changed by this test.
"""
from contextlib import redirect_stdout
from datetime import datetime, timezone
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'reports/solution-review/source91-runtime-delivery-fixture-results-v1.json'
PRIOR = 'reports/full-coverage/runtime-checkpoint-35-source90-v1'
HISTORY = ROOT / 'reports/solution-review/source-history'
SOURCE_NAMES = [
    'book/solutions/prepare_solution_runtime.py',
    'book/solutions/export_solution_audit.py',
    'book/solutions/verify_solution_delivery.py',
    'book/solutions/solution_release.py',
    'book/solutions/solution_review.py',
    'book/inventory_claims.py',
    'book/validate.py',
]
SOURCES = {n: (ROOT / n).read_bytes() for n in SOURCE_NAMES}
PRIOR_REPORT = json.loads((ROOT / PRIOR / 'reports/lean-verification/verification.json').read_bytes())
OLD_SOURCES = {
    n: (HISTORY / (Path(n).stem + '-before-independent-runtime-fixes-v1.py')).read_bytes()
    for n in SOURCE_NAMES[:2]
}
MODULE_NAMES = [Path(n).stem for n in PRIOR_REPORT['proof_sha256']]
SITE_NAMES = list(PRIOR_REPORT['source_sha256'])
PROJECT_NAMES = list(PRIOR_REPORT['project_sha256'])
IMPORTED_NAMES = ['solution_review', 'solution_release', 'prepare_solution_runtime',
                  'export_solution_audit', 'verify_solution_delivery', 'validate']


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def json_write(path, value):
    write(path, (json.dumps(value, indent=2) + '\n').encode())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class Fixture:
    def __init__(self, old_prepare=False, old_export=False):
        self.old_prepare = old_prepare
        self.old_export = old_export

    def __enter__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='source91-independent-fixture-')
        self.root = Path(self.temp.name)
        self.previous = {n: sys.modules.get(n) for n in IMPORTED_NAMES}
        self.previous_path = sys.path[:]
        for n, raw in SOURCES.items():
            if (self.old_prepare and n.endswith('/prepare_solution_runtime.py')) or (
                    self.old_export and n.endswith('/export_solution_audit.py')):
                raw = OLD_SOURCES[n]
            write(self.root / n, raw)
        sys.path.insert(0, str(self.root / 'book/solutions'))
        sys.path.insert(0, str(self.root / 'book'))
        self.review = load('solution_review', self.root / 'book/solutions/solution_review.py')
        self.release = load('solution_release', self.root / 'book/solutions/solution_release.py')
        self.runtime = load('prepare_solution_runtime', self.root / 'book/solutions/prepare_solution_runtime.py')
        self.export = load('export_solution_audit', self.root / 'book/solutions/export_solution_audit.py')
        self.delivery = load('verify_solution_delivery', self.root / 'book/solutions/verify_solution_delivery.py')
        # A small synthetic site satisfies the inventory's actual 556-item scan.
        details = ''.join(
            '<details id="fixture-%d"><summary>Exercise %d — Easy: fixture</summary>'
            '<p>Compute a fixture sum.</p><details><summary>Hint</summary><p>Add.</p></details>'
            '<details><summary>Solution</summary><p>One plus one is two.</p></details></details>' % (i, i)
            for i in range(1, 557))
        html_index = 0
        for n in SITE_NAMES:
            if n.endswith('.html'):
                html_index += 1
                raw = ('<!doctype html><html><body><p>' + n + '</p>' +
                       (details if html_index == 1 else '') + '</body></html>').encode()
            else:
                raw = ('/* synthetic fixture ' + n + ' */\n').encode()
            write(self.root / n, raw)
        proof_hashes = {}
        for module in MODULE_NAMES:
            name = 'verification/lean/SafeLearning/' + module + '.lean'
            raw = ('import Mathlib\n-- Synthetic data-flow fixture: ' + module + '\n').encode()
            write(self.root / PRIOR / name, raw)
            proof_hashes[name] = sha(raw)
        project_hashes = {}
        for name in PROJECT_NAMES:
            if name.endswith('/SafeLearning.lean'):
                raw = ''.join('import SafeLearning.' + m + '\n' for m in MODULE_NAMES).encode()
            else:
                raw = (ROOT / PRIOR / name).read_bytes()
            write(self.root / PRIOR / name, raw)
            project_hashes[name] = sha(raw)
        write(self.root / PRIOR / 'book/coverage/lean_names.py',
              (ROOT / PRIOR / 'book/coverage/lean_names.py').read_bytes())
        self.prior = {
            'status': 'passed', 'proof_file_count': 1267, 'theorem_count': 11472,
            'proof_sha256': proof_hashes, 'project_sha256': project_hashes,
            'source_sha256': {n: sha((self.root / n).read_bytes()) for n in SITE_NAMES},
        }
        json_write(self.root / self.release.PRIOR_AUDIT, self.prior)
        self.plan = {
            'status': 'all556_independently_approved_ready_for_solution_installation',
            'selected_prior_proof_audit': self.review.ref(self.release.PRIOR_AUDIT),
            'site_source91_sha256': self.prior['source_sha256'],
        }
        json_write(self.root / self.release.PLAN, self.plan)
        self.plan_hash = self.review.ref(self.release.PLAN)['sha256']
        # Approval selection itself is independently audited in solution_release;
        # these fixtures isolate the helpers after the release-plan gate.
        def fixture_plan(fingerprint):
            assert fingerprint == self.plan_hash
            return self.plan
        self.release.load_plan = fixture_plan
        for n in ('packages', 'build'):
            (self.root / 'verification/lean/.lake' / n).mkdir(parents=True)
        return self

    def __exit__(self, *args):
        sys.path[:] = self.previous_path
        for n, prior in self.previous.items():
            if prior is None:
                sys.modules.pop(n, None)
            else:
                sys.modules[n] = prior
        self.temp.cleanup()

    def prepare(self):
        with patch.object(sys, 'argv', ['prepare_solution_runtime.py', '--plan-sha256', self.plan_hash]), redirect_stdout(io.StringIO()):
            self.runtime.main()
        return self.review.read(self.runtime.REPORT)

    def prepared_files(self):
        base = self.root / self.runtime.RUNTIME
        proofs = {p.relative_to(base).as_posix() for p in (base / 'verification/lean/SafeLearning').rglob('*.lean')}
        assets = {p.relative_to(base).as_posix() for p in (base / 'SafeLearning').iterdir() if p.suffix in {'.html', '.js', '.css'}}
        return proofs, assets

    def audit_inputs(self):
        self.prepare()
        directory = self.root / self.runtime.RUNTIME / 'reports/lean-verification'
        directory.mkdir(parents=True)
        prior_bytes = json.dumps(self.prior, indent=2).encode() + b'\n'
        write(directory / 'reused-verification-original.json', prior_bytes)
        checks = []
        for command, filename in ((['lean', '--version'], 'lean-version.txt'),
                                  (['lake', 'build'], 'build.log')):
            write(directory / filename, ('synthetic success: ' + filename + '\n').encode())
            checks.append({'command': command, 'exit_code': 0, 'elapsed_seconds': 0.1,
                           'output_file': 'reports/lean-verification/' + filename})
        historical_cwd = str(self.root / 'historical-checkpoint/verification/lean')
        for i, module in enumerate(MODULE_NAMES):
            full = 'SafeLearning.' + module
            filename = 'kernel-' + full.replace('.', '-') + '.log'
            raw = ('synthetic kernel fixture: ' + full + '\n').encode()
            write(directory / filename, raw)
            original = {'command': ['lake', 'env', 'leanchecker', '-v', full],
                        'exit_code': 0, 'elapsed_seconds': 0.1,
                        'output_file': 'reports/lean-verification/' + filename,
                        'module': full, 'log_sha256': sha(raw), 'actual_workdir': historical_cwd,
                        'evidence_mode': 'fresh_kernel_replay'}
            check = copy.deepcopy(original)
            if i:
                check.update(evidence_mode='reused_identical_module_and_transitive_local_imports',
                    reused_from={'report': 'reports/lean-verification/reused-verification-original.json',
                                 'report_sha256': sha(prior_bytes), 'actual_workdir': historical_cwd,
                                 'prior_report_workdir': str(self.root / PRIOR / 'verification/lean'),
                                 'original_check': original,
                                 'verified_local_import_sha256': {
                                     'verification/lean/SafeLearning/' + module + '.lean':
                                         self.prior['proof_sha256']['verification/lean/SafeLearning/' + module + '.lean']}})
            else:
                check['actual_workdir'] = str(self.root / self.runtime.RUNTIME / 'verification/lean')
            checks.append(check)
        write(directory / 'axioms.log', b'synthetic axiom-audit fixture\n')
        checks.append({'command': ['lake', 'env', 'lean', str(self.root / self.runtime.RUNTIME / 'verification/lean/AxiomAudit.lean')],
                       'exit_code': 0, 'elapsed_seconds': 0.1, 'output_file': 'reports/lean-verification/axioms.log'})
        self.audit = copy.deepcopy(self.prior)
        self.audit.update(verified_at_utc='2026-10-13T00:00:05+00:00', checks=checks,
                          axiom_dependencies={'Fixture.theorem_' + str(i): [] for i in range(11472)},
                          declarations=[{'name': 'Fixture.theorem_' + str(i)} for i in range(11472)])
        self.audit_name = self.runtime.RUNTIME + '/reports/lean-verification/verification.json'
        json_write(self.root / self.audit_name, self.audit)
        native_command = ['python3', '-B', 'verification/lean/verify.py', '--reuse-kernel-from',
                          str(self.root / PRIOR), '--output', str(directory)]
        inputs = [self.runtime.RUNTIME + '/verification/lean/' + n for n in
                  ['verify.py', 'SafeLearning.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
        inputs += [self.runtime.REPORT, self.release.PLAN, self.runtime.RUNTIME + '/book/coverage/lean_names.py']
        input_hashes = {n: self.review.ref(n)['sha256'] for n in inputs}
        self.started_name = self.export.NATIVE.replace('.json', '.started.json')
        started = {'status': 'started', 'actual_command': native_command,
                   'actual_workdir': str(self.root / self.runtime.RUNTIME),
                   'helper_sha256_before': input_hashes, 'started_at_utc': '2026-10-13T00:00:00+00:00'}
        json_write(self.root / self.started_name, started)
        native_log = self.export.NATIVE.replace('.json', '.log')
        write(self.root / native_log, b'synthetic native-execution record fixture; Lean was not executed\n')
        self.native = dict(started, status='passed', actual_exit_code=0, helper_sha256_after=input_hashes.copy(),
                           finished_at_utc='2026-10-13T00:00:10+00:00', started_receipt=self.started_name,
                           started_receipt_sha256=self.review.ref(self.started_name)['sha256'],
                           log=native_log, log_sha256=self.review.ref(native_log)['sha256'],
                           child_started=True, interruption_signal=None, binding_errors_after={}, recorder_exit_code=0)
        json_write(self.root / self.export.NATIVE, self.native)
        return directory

    def run_export(self):
        with redirect_stdout(io.StringIO()):
            self.export.main()

    def delivery_attempt(self, *, bad_asset=False, bad_remote=False, bad_build=False,
                         bad_run=False, bad_job=False, missing_job=False):
        commit = 'a' * 40
        jobs = [{'id': i, 'name': n, 'run_id': 7, 'status': 'completed', 'conclusion': 'success'}
                for i, n in enumerate(['build', 'report-build-status', 'deploy'], 1)]
        if bad_job:
            jobs[-1]['conclusion'] = 'failure'
        if missing_job:
            jobs.pop()
        run = {'id': 7, 'head_sha': commit, 'name': 'pages build and deployment',
               'status': 'completed', 'conclusion': 'failure' if bad_run else 'success'}
        def process(command, **kwargs):
            if command[0] == 'git':
                raw = (('b' * 40 if bad_remote else commit) + '\trefs/heads/main\n').encode()
            elif command[-1].endswith('/pages/builds/latest'):
                raw = json.dumps({'status': 'built', 'commit': 'b' * 40 if bad_build else commit}).encode()
            elif '/actions/runs?' in command[-1]:
                raw = json.dumps({'workflow_runs': [run]}).encode()
            else:
                assert command[-1].endswith('/actions/runs/7/jobs')
                raw = json.dumps({'jobs': jobs}).encode()
            return subprocess.CompletedProcess(command, 0, stdout=raw, stderr=b'')
        class Response:
            status = 200
            def __init__(self, raw):
                self.raw = raw
            def __enter__(self):
                return self
            def __exit__(self, *args):
                return False
            def read(self):
                return self.raw
        first_asset = sorted(SITE_NAMES)[0]
        def response(request, timeout):
            name = unquote(urlsplit(request.full_url).path).lstrip('/')
            assert request.headers.get('Cache-control') == 'no-cache'
            raw = (self.root / name).read_bytes()
            if bad_asset and name == first_asset:
                raw += b'changed'
            return Response(raw)
        argv = ['verify_solution_delivery.py', '--plan-sha256', self.plan_hash,
                '--commit', commit, '--phase', 'content', '--attempt', '1']
        with patch.object(sys, 'argv', argv), patch.object(self.delivery.subprocess, 'run', process), \
             patch.object(self.delivery.urllib.request, 'urlopen', response), redirect_stdout(io.StringIO()):
            code = self.delivery.main()
        report = self.review.read('reports/solution-review/source91-content-delivery-attempt1.json')
        return code, report


def expect_exception(function, kind=AssertionError):
    try:
        function()
    except kind as exc:
        return {'exception': type(exc).__name__, 'message': str(exc)}
    raise AssertionError('Expected ' + kind.__name__ + ' was not raised')


RESULTS = []


def case(name, function):
    try:
        detail = function()
        RESULTS.append({'case': name, 'verdict': 'passed', 'detail': detail})
    except Exception as exc:
        RESULTS.append({'case': name, 'verdict': 'failed', 'exception': type(exc).__name__, 'message': str(exc)})


def clean_prepare():
    with Fixture() as f:
        report = f.prepare()
        proof_set, site_set = f.prepared_files()
        assert proof_set == set(f.prior['proof_sha256']) and len(proof_set) == 1267
        assert site_set == set(SITE_NAMES) and len(site_set) == 31
        first = (f.root / f.runtime.REPORT).read_bytes()
        f.prepare()
        assert (f.root / f.runtime.REPORT).read_bytes() == first
        assert len(report['source_objects']) == 1304
        for row in report['source_objects']:
            obj = f.root / row['object']
            target = f.root / row['runtime_file']
            assert obj.stat().st_ino == target.stat().st_ino
            assert target.stat().st_mode & 0o222 == 0
            assert sha(target.read_bytes()) == row['sha256']
        assert not (f.root / 'book/coverage/inventory.json').exists()
        assert report['new_inventory_counts']['exercises'] == 556
        return {'selected_proofs': 1267, 'site_files': 31, 'source_object_links': 1304,
                'resumption_same_receipt_bytes': True, 'source90_inventory_written': False}


def extra_file(old=False, kind='proof'):
    with Fixture(old_prepare=old) as f:
        f.prepare()
        relative = ('verification/lean/SafeLearning/UnselectedCanonicalAddition.lean' if kind == 'proof'
                    else 'SafeLearning/unselected-extra.html')
        write(f.root / f.runtime.RUNTIME / relative, b'-- synthetic unexpected source\n')
        if old:
            report = f.prepare()
            proofs, assets = f.prepared_files()
            assert report['unselected_proof_sources_added'] == 0
            assert (len(proofs) == 1268 if kind == 'proof' else len(assets) == 32)
            return {'old_helper_accepted_extra_source': True, 'actual_proofs': len(proofs), 'actual_assets': len(assets)}
        return expect_exception(f.prepare)


def partial_inventory(old=False):
    with Fixture(old_prepare=old) as f:
        original = Path.write_text
        def interrupted(path, text, *args, **kwargs):
            if path.name == 'inventory.json':
                original(path, text[:113], *args, **kwargs)
                raise RuntimeError('Injected interruption after partial temporary inventory write')
            return original(path, text, *args, **kwargs)
        with patch.object(Path, 'write_text', interrupted):
            first = expect_exception(f.prepare, RuntimeError)
        name = f.release.RELEASE + '/source91-inventory/inventory.json'
        if old:
            assert (f.root / name).exists()
            resumed = expect_exception(f.prepare, json.JSONDecodeError)
            return {'first_failure': first, 'partial_final_inventory_exists': True, 'resumption': resumed}
        assert not (f.root / name).exists()
        report = f.prepare()
        assert report['new_inventory_counts']['exercises'] == 556
        return {'first_failure': first, 'partial_final_inventory_exists': False, 'resumption': 'succeeded'}


def export_provenance():
    with Fixture() as f:
        f.audit_inputs()
        original = (f.root / f.audit_name).read_bytes()
        f.run_export()
        output = f.root / f.export.OUTPUT
        assert (output / 'verification-original.json').read_bytes() == original
        exported = json.loads((output / 'verification.json').read_bytes())
        for before, after in zip(f.audit['checks'], exported['checks']):
            assert before['command'] == after['command']
            assert before.get('actual_workdir') == after.get('actual_workdir')
            assert after['output_file'] == f.export.OUTPUT + '/' + Path(before['output_file']).name
            if 'reused_from' in before:
                assert after['reused_from']['original_check'] == before['reused_from']['original_check']
                assert after['reused_from']['actual_workdir'] == before['reused_from']['actual_workdir']
                assert after['reused_from']['report'] == f.export.OUTPUT + '/reused-verification-original.json'
        first = (output / 'verification.json').read_bytes()
        f.run_export()
        assert (output / 'verification.json').read_bytes() == first
        evidence = f.review.read('reports/solution-review/source91-lean-audit-export-v1.json')
        assert evidence['fresh_kernel_modules'] == 1 and evidence['reused_identical_kernel_modules'] == 1266
        assert evidence['coverage_complete'] is False
        return {'module_checks': 1267, 'fresh_fixture_modules': 1, 'reused_fixture_modules': 1266,
                'original_report_bytes_preserved': True, 'historical_command_cwd_ancestry_preserved': True,
                'export_resumption_same_receipt_bytes': True}


def export_refusal(field):
    with Fixture() as f:
        f.audit_inputs()
        if field == 'command':
            f.native['actual_command'] = ['python3', '-c', 'pass']
        elif field == 'workdir':
            f.native['actual_workdir'] = str(f.root)
        elif field == 'input':
            f.native['helper_sha256_before'].pop(f.release.PLAN)
            f.native['helper_sha256_after'].pop(f.release.PLAN)
        elif field == 'started':
            with (f.root / f.started_name).open('ab') as output:
                output.write(b' ')
        elif field == 'stale':
            f.audit['verified_at_utc'] = '2026-10-12T00:00:00+00:00'
            json_write(f.root / f.audit_name, f.audit)
        elif field == 'native_exit':
            f.native['actual_exit_code'] = 1
        else:
            raise ValueError(field)
        json_write(f.root / f.export.NATIVE, f.native)
        refused = expect_exception(f.run_export)
        assert not (f.root / f.export.OUTPUT).exists()
        return dict(refused, immutable_export_directory_created=False)


def old_unrelated_native():
    with Fixture(old_export=True) as f:
        f.audit_inputs()
        f.native['actual_command'] = ['python3', '-c', 'pass']
        f.native['actual_workdir'] = str(f.root)
        f.native['helper_sha256_before'] = {}
        f.native['helper_sha256_after'] = {}
        json_write(f.root / f.export.NATIVE, f.native)
        f.run_export()
        return {'old_helper_accepted_unrelated_native_command_with_no_bound_inputs': True}


def corrupt_export_log():
    with Fixture() as f:
        directory = f.audit_inputs()
        check = next(c for c in f.audit['checks'] if 'module' in c)
        name = Path(check['output_file']).name
        original = (directory / name).read_bytes()
        write(directory / name, original + b'corrupted')
        first = expect_exception(f.run_export)
        target = f.root / f.export.OUTPUT / name
        poisoned = target.exists()
        write(directory / name, original)
        if poisoned:
            second = expect_exception(f.run_export)
            return {'corruption_refused': first, 'invalid_immutable_log_was_published': True,
                    'repaired_runtime_cannot_resume_same_export': second}
        f.run_export()
        return {'corruption_refused': first, 'invalid_immutable_log_was_published': False,
                'repaired_runtime_export_resumed': True}


def delivery(kind=None):
    with Fixture() as f:
        params = {kind: True} if kind else {}
        code, report = f.delivery_attempt(**params)
        assert code == (1 if kind else 0)
        assert len(report['assets']) == 31
        if not kind:
            assert all(x['matches'] for x in report['assets'])
            assert len(report['jobs']) == 3
            assert report['remote_main'] == report['expected_commit']
            assert report['Pages_build']['commit'] == report['expected_commit']
            assert report['selected_run']['head_sha'] == report['expected_commit']
        return {'actual_helper_exit_code': code, 'asset_rows': len(report['assets']),
                'successful_jobs': sum(j['conclusion'] == 'success' for j in report['jobs']),
                'status': report['status'], 'network_and_git_responses': 'synthetic_fixture'}


case('prepare_clean_exact_sets_readonly_objects_and_idempotent_resumption', clean_prepare)
case('old_prepare_extra_proof_false_zero_claim_reproduced', lambda: extra_file(old=True))
case('current_prepare_rejects_extra_proof', extra_file)
case('current_prepare_rejects_extra_site_asset', lambda: extra_file(kind='site'))
case('old_inventory_interruption_prevents_resumption_reproduced', lambda: partial_inventory(old=True))
case('current_inventory_interruption_does_not_publish_partial_receipt_and_resumes', partial_inventory)
case('old_export_unrelated_native_receipt_accepted_reproduced', old_unrelated_native)
case('current_export_preserves_raw_report_and_historical_provenance_and_resumes', export_provenance)
for field in ('command', 'workdir', 'input', 'started', 'stale', 'native_exit'):
    case('current_export_rejects_' + field + '_before_export_publication', lambda field=field: export_refusal(field))
case('current_export_corrupted_log_failure_and_repair_resumption', corrupt_export_log)
case('delivery_all31_assets_matching_commit_and_all3_jobs_pass', delivery)
for field in ('bad_asset', 'bad_remote', 'bad_build', 'bad_run', 'bad_job', 'missing_job'):
    case('delivery_rejects_' + field, lambda field=field: delivery(field))

changed = {n: {'tested_sha256': sha(raw), 'current_sha256': sha((ROOT / n).read_bytes())}
           for n, raw in SOURCES.items() if raw != (ROOT / n).read_bytes()}
report = {'status': 'passed_isolated_runtime_export_delivery_fixtures' if all(r['verdict'] == 'passed' for r in RESULTS) else 'fixture_failures',
          'generated_at_utc': datetime.now(timezone.utc).isoformat(),
          'fixture_driver': {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': sha(Path(__file__).read_bytes())},
          'helper_sha256_tested': {n: sha(raw) for n, raw in SOURCES.items()},
          'prior_helpers_tested': {n: sha(raw) for n, raw in OLD_SOURCES.items()},
          'helpers_changed_during_tests': changed, 'tests': RESULTS,
          'limits': ['Only helper data-flow and refusal/resumption behavior was executed; fixture Lean reports and native receipts are synthetic.',
                     'No Lean audit, live HTTP request, git publication or GitHub job ran in these fixtures.',
                     'The complete release approval-selection gate is not duplicated; the helper fixtures begin after that separately reviewed gate.',
                     'Canonical pages, proof sources, historical owner ledgers and prior reports were not changed.']}
json_write(OUTPUT, report)
print(json.dumps({'status': report['status'], 'passed_cases': sum(r['verdict'] == 'passed' for r in RESULTS),
                  'case_count': len(RESULTS), 'helpers_changed': bool(changed),
                  'failures': [r for r in RESULTS if r['verdict'] != 'passed'],
                  'corrupted_log_case': next(r for r in RESULTS if r['case'].endswith('repair_resumption')),
                  'report': OUTPUT.relative_to(ROOT).as_posix()}, indent=2))
raise SystemExit(0 if report['status'].startswith('passed') and not changed else 1)
