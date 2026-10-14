"""Small synthetic fixtures for export identity and exact axiom-namespace gates.

Receipts, audits and theorem names below are deliberately synthetic. This runs
no Lean compiler, kernel, correspondence review, canonical update or delivery.
"""
from contextlib import redirect_stdout
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import types
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
PIECE = 'book/coverage/source91-piece01'
sys.path.insert(0, str(ROOT / PIECE))
import common as c
import prepare_runtime as runtime
import export_audit as exporter
import finish_piece as finisher

HELPERS = [PIECE + '/' + n for n in ['common.py', 'prepare_runtime.py', 'export_audit.py', 'finish_piece.py']]
HELPER_BYTES = {n: (ROOT / n).read_bytes() for n in HELPERS}
PRIOR_AUDIT = json.loads((ROOT / runtime.AUDIT).read_bytes())
OUT = 'reports/full-coverage/source91-piece01/audit-completion-independent-fixtures-v3.json'
OLD_FINISH = 'reports/full-coverage/source91-piece01/history/finish_piece-before-cardinality-guard-v1.py.txt'
OLD_FINISH_BYTES = (ROOT / OLD_FINISH).read_bytes()
ACTUAL_PACKET_RAW = (ROOT / finisher.PACKET).read_bytes()
ACTUAL_REVIEW_RAW = (ROOT / finisher.REVIEW).read_bytes()
ACTUAL_PACKET = json.loads(ACTUAL_PACKET_RAW)
ACTUAL_BOUND_BYTES = {r['file']: (ROOT / r['file']).read_bytes() for r in
                      [ACTUAL_PACKET['reader_source'], ACTUAL_PACKET['inventory']] + ACTUAL_PACKET['proof_sources']}
assert all(sha == hashlib.sha256(ACTUAL_BOUND_BYTES[name]).hexdigest() for name, sha in
           ((r['file'], r['sha256']) for r in [ACTUAL_PACKET['reader_source'], ACTUAL_PACKET['inventory']] + ACTUAL_PACKET['proof_sources']))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


class Fixture:
    def __enter__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='piece01-audit-independent-')
        self.root = Path(self.temp.name)
        c.ROOT = self.root
        for name, raw in HELPER_BYTES.items():
            write(self.root / name, raw)
        proofs = sorted(PRIOR_AUDIT['proof_sha256']) + ['verification/lean/SafeLearning/' + n + '.lean' for n in runtime.ADDITIONS]
        sites = sorted(PRIOR_AUDIT['source_sha256'])
        projects = sorted(PRIOR_AUDIT['project_sha256'])
        files = []
        for name in proofs + sites + projects + [runtime.SUPPORT]:
            raw = ('Synthetic selected audit source: ' + name + '\n').encode()
            write(self.root / runtime.RUNTIME / name, raw)
            files.append({'target': name, 'sha256': sha(raw)})
        expected = {r['target']: r['sha256'] for r in files}
        self.plan = {'files': files, 'site_source91_sha256': {n: expected[n] for n in sites}}
        self.preparation = {'runtime_source_sha256': expected}
        write(self.root / runtime.PLAN, encoded(self.plan))
        write(self.root / runtime.REPORT, encoded(self.preparation))
        self.directory = self.root / runtime.RUNTIME / 'reports/lean-verification'
        self.original = self.directory / 'verification.json'
        self.reused = self.directory / 'reused-verification-original.json'
        write(self.reused, encoded({'status': 'synthetic_reused_report_fixture'}))
        prior_log = 'reports/lean-verification/kernel-prior-fixture.log'
        write(self.root / runtime.RUNTIME / prior_log, b'Synthetic reused check output\n')
        reused_ref = {'report': 'reports/lean-verification/reused-verification-original.json',
                      'report_sha256': sha(self.reused.read_bytes()),
                      'historical_origin': 'synthetic_fixture_ancestry_retained'}
        checks = []
        for name in sorted(PRIOR_AUDIT['proof_sha256']):
            checks.append({'module': 'SafeLearning.' + Path(name).stem, 'exit_code': 0,
                           'evidence_mode': 'reused_identical_module_and_transitive_local_imports',
                           'output_file': prior_log, 'log_sha256': c.ref(runtime.RUNTIME + '/' + prior_log)['sha256'],
                           'reused_from': dict(reused_ref), 'actual_command': ['synthetic', 'prior'],
                           'actual_workdir': 'synthetic_prior_workdir'})
        for name in runtime.ADDITIONS:
            log = 'reports/lean-verification/kernel-' + name + '.log'
            write(self.root / runtime.RUNTIME / log, ('Synthetic fresh check ' + name + '\n').encode())
            checks.append({'module': 'SafeLearning.' + name, 'exit_code': 0,
                           'evidence_mode': 'fresh_kernel_replay', 'output_file': log,
                           'log_sha256': c.ref(runtime.RUNTIME + '/' + log)['sha256'],
                           'actual_command': ['synthetic', name], 'actual_workdir': 'synthetic_fresh_workdir'})
        declarations = [{'name': 'Fixture.theorem_' + str(i)} for i in range(11508)]
        self.audit = {'status': 'passed', 'proof_file_count': 1271, 'theorem_count': 11508,
                      'verified_at_utc': '2026-10-14T00:00:01+00:00', 'checks': checks,
                      'declarations': declarations,
                      'axiom_dependencies': {r['name']: ['propext', 'Classical.choice', 'Quot.sound'] for r in declarations},
                      'proof_sha256': {n: expected[n] for n in proofs},
                      'source_sha256': {n: expected[n] for n in sites},
                      'project_sha256': {n: expected[n] for n in projects}}
        write(self.original, encoded(self.audit))
        native_log = 'reports/full-coverage/source91-piece01/synthetic-native.log'
        started = 'reports/full-coverage/source91-piece01/synthetic-native.started.json'
        write(self.root / native_log, b'Synthetic native receipt fixture\n')
        write(self.root / started, encoded({'status': 'synthetic_started_receipt'}))
        bound = [runtime.PLAN, runtime.REPORT] + [runtime.RUNTIME + '/' + n for n in
                 ['verification/lean/verify.py', runtime.AGGREGATE, 'verification/lean/lean-toolchain',
                  'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json', runtime.SUPPORT]]
        hashes = {n: c.ref(n)['sha256'] for n in bound}
        self.native = {'status': 'passed', 'actual_exit_code': 0,
                       'helper_sha256_before': hashes, 'helper_sha256_after': dict(hashes),
                       'log': native_log, 'log_sha256': c.ref(native_log)['sha256'],
                       'started_receipt': started, 'started_receipt_sha256': c.ref(started)['sha256'],
                       'actual_command': ['python3', '-B', 'verification/lean/verify.py', '--reuse-kernel-from',
                                          str(self.root / runtime.PRIOR), '--output', str(self.directory)],
                       'actual_workdir': str(self.root / runtime.RUNTIME),
                       'started_at_utc': '2026-10-14T00:00:00+00:00',
                       'finished_at_utc': '2026-10-14T00:00:02+00:00'}
        write(self.root / exporter.NATIVE, encoded(self.native))
        return self

    def __exit__(self, *args):
        c.ROOT = ROOT
        self.temp.cleanup()

    def export(self):
        with redirect_stdout(io.StringIO()):
            exporter.main()


def refusal(fn):
    try:
        fn()
    except AssertionError as exc:
        return {'exception': type(exc).__name__, 'message': str(exc)}
    raise AssertionError('Expected gate refusal was not raised')


def valid_export():
    with Fixture() as f:
        original = f.original.read_bytes()
        f.export()
        assert (f.root / exporter.OUTPUT / 'verification-original.json').read_bytes() == original
        relocated = c.read(exporter.OUTPUT + '/verification.json')
        for before, after in zip(f.audit['checks'], relocated['checks']):
            assert after['actual_command'] == before['actual_command']
            assert after['actual_workdir'] == before['actual_workdir']
            assert after['output_file'].startswith(exporter.OUTPUT + '/')
            if before.get('reused_from'):
                assert after['reused_from']['historical_origin'] == before['reused_from']['historical_origin']
                assert c.ref(after['reused_from']['report'])['sha256'] == before['reused_from']['report_sha256']
        first = (f.root / exporter.REPORT).read_bytes(); f.export()
        assert (f.root / exporter.REPORT).read_bytes() == first
        return {'synthetic_export_and_identical_rerun': 'passed', 'original_bytes_preserved': True,
                'relocation_preserves_commands_cwds_and_historical_ancestry': True,
                'fixture_does_not_constitute_native_audit': True}


def changed_on_stage(kind):
    with Fixture() as f:
        target = f.original if kind == 'verification' else f.reused
        threshold = 2 if kind == 'verification' else 1268
        real = Path.read_bytes; reads = 0
        def changed(path):
            nonlocal reads
            raw = real(path)
            if path == target:
                reads += 1
                if reads == threshold:
                    return raw + b' \n'
            return raw
        with patch.object(Path, 'read_bytes', changed):
            detail = refusal(f.export)
        assert reads == threshold and not (f.root / exporter.OUTPUT).exists()
        return {'refusal': detail, 'changed_reread_detected': kind, 'export_not_started': True}


def namespace_mismatch(which):
    with Fixture() as f:
        deps = f.audit['axiom_dependencies']
        deps['Fixture.foreign_name'] = deps.pop('Fixture.theorem_0')
        assert len(deps) == 11508
        write(f.original, encoded(f.audit))
        if which == 'export':
            detail = refusal(f.export)
            assert not (f.root / exporter.OUTPUT).exists()
        else:
            packet = {'inventory': {'file': 'fixture-inventory.json', 'sha256': '0' * 64}}
            write(f.root / finisher.PACKET, encoded(packet))
            review = {'status': 'approved', 'errors': [], 'claim_packet': c.ref(finisher.PACKET),
                      'inventory': packet['inventory'], 'whole_exercise_status_after_success': 'partial'}
            write(f.root / finisher.REVIEW, encoded(review))
            export = {'status': 'passed_actual_source91_piece01_selected_build_fresh4_kernel_and_all_axiom_audit_export',
                      'native_execution': c.ref(exporter.NATIVE),
                      'original_native_report': c.ref(runtime.RUNTIME + '/reports/lean-verification/verification.json'),
                      'runtime_plan': c.ref(runtime.PLAN), 'runtime_preparation': c.ref(runtime.REPORT)}
            write(f.root / exporter.REPORT, encoded(export))
            detail = refusal(finisher.main)
            assert not (f.root / finisher.LEDGER).exists() and not (f.root / finisher.REPORT).exists()
        return {'refusal': detail, 'axiom_count_preserved': 11508, 'namespace_mismatch_refused_before_publication': True}


class ReachedLedger(Exception):
    pass


def cardinality(kind=None, old=False):
    with Fixture() as f:
        packet = json.loads(ACTUAL_PACKET_RAW)
        review = json.loads(ACTUAL_REVIEW_RAW)
        if old:
            # The preserved helper also has an unrelated exact/normalized-text
            # mismatch. Control that field only in this synthetic old-code
            # duplicate fixture so it reaches its missing cardinality gate.
            normalized = {r['source_unit']['key']: r['text'] for r in packet['source_units']}
            for row in review['source_units']:
                row['exact_text'] = normalized[row['key']]
        for name, raw in ACTUAL_BOUND_BYTES.items():
            write(f.root / name, raw)
        write(f.root / finisher.PACKET, ACTUAL_PACKET_RAW)
        if kind:
            field = 'claims' if kind == 'claims' else 'source_units'
            review[field].append(dict(review[field][0]))
        write(f.root / finisher.REVIEW, encoded(review))
        needed = {name for row in review['claims'] + review['source_units'] for name in row['lean_declarations']}
        fillers = ['Fixture.cardinality_' + str(i) for i in range(11508 - len(needed))]
        declarations = sorted(needed) + fillers
        assert len(set(declarations)) == 11508
        f.audit['declarations'] = [{'name': name} for name in declarations]
        f.audit['axiom_dependencies'] = {name: ['propext', 'Classical.choice', 'Quot.sound'] for name in declarations}
        f.audit['source_sha256'][packet['reader_source']['file']] = packet['reader_source']['sha256']
        for binding in packet['proof_sources']:
            f.audit['proof_sha256'][binding['file']] = binding['sha256']
        write(f.original, encoded(f.audit))
        export = {'status': 'passed_actual_source91_piece01_selected_build_fresh4_kernel_and_all_axiom_audit_export',
                  'native_execution': c.ref(exporter.NATIVE),
                  'original_native_report': c.ref(runtime.RUNTIME + '/reports/lean-verification/verification.json'),
                  'runtime_plan': c.ref(runtime.PLAN), 'runtime_preparation': c.ref(runtime.REPORT)}
        write(f.root / exporter.REPORT, encoded(export))
        module = finisher
        if old:
            module = types.ModuleType('preserved_pre_cardinality_finisher')
            exec(compile(OLD_FINISH_BYTES, OLD_FINISH, 'exec'), module.__dict__)
        real_put = c.json_put
        def stop_at_ledger(name, value):
            if name == finisher.LEDGER:
                raise ReachedLedger('Reached first ledger publication boundary; no ledger written')
            return real_put(name, value)
        with patch.object(c, 'json_put', stop_at_ledger):
            try:
                module.main()
            except ReachedLedger:
                assert kind is None or old
                detail = {'reached_first_ledger_boundary_without_writing': True}
            except AssertionError as exc:
                assert kind is not None and not old, 'Unexpected refusal before first ledger boundary'
                detail = {'refusal': {'exception': type(exc).__name__, 'message': str(exc)},
                          'duplicate_list': kind, 'refused_before_first_ledger_write': True}
            else:
                raise AssertionError('Unexpected finish completion in a boundary-only fixture')
        assert not (f.root / finisher.LEDGER).exists() and not (f.root / finisher.REPORT).exists()
        return detail


def duplicate_cardinality(kind):
    return {'preserved_helper_gap_reproduced': cardinality(kind, old=True),
            'current_helper_duplicate_refusal': cardinality(kind)}


results = []
for name, fn in [
    ('synthetic_valid_export_preserves_original_and_provenance_and_resumes', valid_export),
    ('export_rejects_parsed_verification_json_reread_change_before_any_copy', lambda: changed_on_stage('verification')),
    ('export_rejects_verified_reused_report_reread_change_before_any_copy', lambda: changed_on_stage('reused')),
    ('export_rejects_same_size_wrong_axiom_namespace', lambda: namespace_mismatch('export')),
    ('finish_rejects_same_size_wrong_axiom_namespace_before_ledger_or_completion', lambda: namespace_mismatch('finish')),
    ('finish_exact_unique12_claims_and7_leaves_reach_first_ledger_boundary_without_mutation', cardinality),
    ('finish_duplicate_claim_list_refused_and_preserved_gap_reproduced', lambda: duplicate_cardinality('claims')),
    ('finish_duplicate_leaf_list_refused_and_preserved_gap_reproduced', lambda: duplicate_cardinality('units')),
]:
    try:
        results.append({'case': name, 'verdict': 'passed', 'detail': fn()})
    except Exception as exc:
        results.append({'case': name, 'verdict': 'failed', 'exception': type(exc).__name__, 'message': str(exc)})
    print(json.dumps({'case': name, 'verdict': results[-1]['verdict']}), flush=True)

changed = [n for n, raw in HELPER_BYTES.items() if (ROOT / n).read_bytes() != raw]
result = {'status': 'passed_bounded_independent_audit_completion_fixtures' if not changed and all(r['verdict'] == 'passed' for r in results) else 'fixture_failures',
          'generated_at_utc': datetime.now(timezone.utc).isoformat(),
          'helpers': [{'file': n, 'sha256': sha(raw)} for n, raw in HELPER_BYTES.items()],
          'driver': {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': sha(Path(__file__).read_bytes())},
          'preserved_finisher': {'file': OLD_FINISH, 'sha256': sha(OLD_FINISH_BYTES)},
          'cardinality_fixture_inputs': [{'file': finisher.PACKET, 'sha256': sha(ACTUAL_PACKET_RAW)},
                                        {'file': finisher.REVIEW, 'sha256': sha(ACTUAL_REVIEW_RAW)}],
          'helpers_changed_during_tests': changed, 'tests': results,
          'scope': 'Synthetic native receipts, audits and 11508 theorem names in isolated temporary roots. Final-helper cardinality fixtures copy actual packet/review/source bytes as protocol inputs and stop before any ledger write. Preserved-helper duplicate fixtures control only their exact_text field to the older normalized representation, isolating the missing cardinality gate. No original report is changed. Tests only exporter/finisher mechanics.',
          'compiler_or_kernel_executed': False, 'source_correspondence_approved_by_fixture': False,
          'canonical_sources_helpers_owner_ledgers_or_actual_audit_modified': False}
write(ROOT / OUT, encoded(result))
print(json.dumps({'status': result['status'], 'cases': len(results), 'report': OUT,
                  'failures': [r for r in results if r['verdict'] != 'passed']}, indent=2))
raise SystemExit(0 if result['status'].startswith('passed') else 1)
