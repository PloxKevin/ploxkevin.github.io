"""Exercise metadata/closure gates in a temporary synthetic checkout.

All Git, commit, push, HTTP, Pages and native-delivery observations below are
synthetic fixture inputs. No canonical document, site file or helper is edited.
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
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'reports/solution-review/source91-delivery-metadata-fixture-results-v1.json'
NAMES = ['book/solutions/prepare_solution_delivery_metadata.py',
         'book/solutions/close_solution_publication.py',
         'book/solutions/solution_review.py', 'book/solutions/solution_release.py',
         'book/solutions/verify_solution_delivery.py']
SOURCES = {n: (ROOT / n).read_bytes() for n in NAMES}
OLD_NAME = 'reports/solution-review/source-history/prepare_solution_delivery_metadata-before-independent-delivery-fixes-v1.py'
OLD = (ROOT / OLD_NAME).read_bytes()
SITE_NAMES = list(json.loads((ROOT / 'book/solutions/releases/source91-v1/plan.json').read_bytes())['site_source91_sha256'])
DOC_NAMES = ['README.md', 'book/coverage/progress.json', 'book/coverage/CONTINUATION.md',
             'reports/full-coverage/README.md', 'verification/lean/README.md', 'book/solutions/RELEASE.md']
TRACKER = 'book/solutions/baseline-source90/review-tracker.json'
MODULES = ['solution_review', 'solution_release', 'prepare_solution_delivery_metadata', 'close_solution_publication']
CONTENT = 'a' * 40
METADATA = 'b' * 40
PARENT = 'c' * 40


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def jwrite(path, value):
    write(path, (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class Fixture:
    def __init__(self, old=False):
        self.old = old

    def __enter__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='source91-metadata-independent-')
        self.root = Path(self.temp.name)
        self.previous = {n: sys.modules.get(n) for n in MODULES}
        self.previous_path = sys.path[:]
        for n, raw in SOURCES.items():
            if self.old and n == NAMES[0]:
                raw = OLD
            write(self.root / n, raw)
        sys.path.insert(0, str(self.root / 'book/solutions'))
        self.review = load('solution_review', self.root / NAMES[2])
        self.release = load('solution_release', self.root / NAMES[3])
        self.helper = load('prepare_solution_delivery_metadata', self.root / NAMES[0])
        self.close = load('close_solution_publication', self.root / NAMES[1])
        self.pub = self.helper.PUB
        self.git_head = CONTENT
        self.git_parent = PARENT
        self.git_remote = CONTENT
        self.git_branch = 'main'
        self.git_dirty = ''
        for name in SITE_NAMES:
            raw = ('Synthetic site fixture ' + name + '\n').encode()
            write(self.root / name, raw)
            write(self.pub / name, raw)
        self.progress = {
            'publication_status': 'source91_all556_solutions_ready_publication_pending',
            'live_delivery_status': 'Source91_publication_pending_previous_checkpoint35_delivery_retained',
            'last_published_commit': PARENT, 'last_published_content_commit': PARENT,
            'live_delivery_evidence': {'previous_checkpoint35': 'historical evidence kept'},
            'solution_depth_requirement': {'status': 'all556_independently_reviewed_installed_and_reader_QA_passed_publication_pending'},
            'verified_checkpoint': {'source_version': 'Source90', 'coverage_complete': False,
                                    'proof_files': 1267, 'theorems': 11472},
            'historical_exercise_coverage': {'complete': 539, 'partial': 6, 'pending': 11},
            'historical_material_coverage': {'reviewed': 4878, 'pending': 7896},
            'formal_source_correspondence': 'Source91 rewritten answers pending explicit rebase',
        }
        for name in DOC_NAMES:
            raw = (name + '\nFormal correspondence remains pending; Source90 counts are historical.\n').encode()
            if name == 'book/coverage/progress.json':
                raw = (json.dumps(self.progress, indent=2) + '\n').encode()
            elif name == 'book/coverage/CONTINUATION.md':
                raw += b'Source91 publication is pending its actual commit, push, Pages jobs and live hashes.\n'
            write(self.root / name, raw)
            write(self.pub / name, raw)
        self.originals = {n: (self.root / n).read_bytes() for n in DOC_NAMES}
        tracker = {'exercises': [{'inventory_key': 'fixture-' + str(i),
                                'status': 'independently_approved_draft_pending_adoption',
                                'selected_solution_sha256': sha(str(i).encode())} for i in range(556)],
                   'counts': {'independently_approved_draft_pending_adoption': 556},
                   'canonical_adoption_claimed': False}
        jwrite(self.root / TRACKER, tracker)
        self.originals[TRACKER] = (self.root / TRACKER).read_bytes()
        approved = self.release.RELEASE + '/independently-approved-tracker.json'
        write(self.root / approved, self.originals[TRACKER])
        self.plan = {'counts': {'exercises': 556, 'pages': 22, 'replace': 251, 'retain': 305},
                     'site_source91_sha256': {n: sha((self.root / n).read_bytes()) for n in SITE_NAMES},
                     'approved_tracker': self.review.ref(approved)}
        jwrite(self.root / self.release.PLAN, self.plan)
        fingerprint = self.review.ref(self.release.PLAN)['sha256']
        def plan_gate(expected):
            assert expected == fingerprint
            return self.plan
        self.release.load_plan = plan_gate
        self.documentation_name = 'reports/solution-review/source91-documentation-v1.json'
        jwrite(self.root / self.documentation_name,
               {'status': 'passed_source91_completed_local_checks_and_documentation',
                'documents': [self.review.ref(n) for n in DOC_NAMES]})
        jwrite(self.root / 'reports/solution-review/source91-content-publication-plan-v1.json',
               {'phase': 'content', 'expected_publication_head': PARENT})
        jwrite(self.root / 'reports/solution-review/release-source91-installation-v1.json',
               {'status': 'synthetic_fixture_installation', 'counts': self.plan['counts']})
        audit_name = 'reports/solution-review/source91-lean-audit-export-v1.json'
        jwrite(self.root / audit_name, {'status': 'passed_actual_source91_selected35_build_kernel_and_all_axiom_audit_export',
                                      'proof_files': 1267, 'public_theorems': 11472,
                                      'fresh_build_and_all_theorem_axiom_audit': True})
        self.local_ready_name = 'reports/solution-review/source91-release-ready-v1.json'
        jwrite(self.root / self.local_ready_name,
               {'status': 'passed_source91_all556_release_ready_for_publication',
                'evidence': [self.review.ref(audit_name)], 'counts': self.plan['counts']})
        self.delivery_names = {}; self.native_names = {}
        self.make_delivery('content', CONTENT)
        self.make_git_receipts('content')
        self.mock = patch.object(subprocess, 'run', self.subprocess)
        self.mock.start()
        return self

    def __exit__(self, *args):
        self.mock.stop()
        sys.path[:] = self.previous_path
        for n, old in self.previous.items():
            if old is None:
                sys.modules.pop(n, None)
            else:
                sys.modules[n] = old
        self.temp.cleanup()

    def subprocess(self, command, cwd, capture_output, text=False):
        assert Path(cwd) == self.pub and command[0] == 'git'
        args = command[1:]
        if args == ['symbolic-ref', '--short', 'HEAD']:
            result = self.git_branch
        elif args == ['rev-parse', 'HEAD']:
            result = self.git_head
        elif args == ['rev-parse', 'HEAD^']:
            result = self.git_parent
        elif args == ['rev-parse', CONTENT + '^']:
            result = PARENT if self.git_parent == PARENT else self.git_parent
        elif args == ['ls-remote', 'origin', 'refs/heads/main']:
            result = self.git_remote + '\trefs/heads/main'
        elif args == ['status', '--porcelain=v1', '--untracked-files=all']:
            result = self.git_dirty
        else:
            raise AssertionError('Unexpected fixture command ' + repr(command))
        raw = result + ('\n' if result else '')
        return subprocess.CompletedProcess(command, 0, stdout=raw if text else raw.encode(),
                                           stderr='' if text else b'')

    def receipt(self, name, command, cwd, log):
        log_name = name.replace('.json', '.log')
        started_name = name.replace('.json', '.started.json')
        write(self.root / log_name, log)
        hashes = {n: self.review.ref(n)['sha256'] for n in NAMES}
        initial = {'status': 'started', 'actual_command': command, 'actual_workdir': str(cwd),
                   'helper_sha256_before': hashes}
        jwrite(self.root / started_name, initial)
        value = dict(initial, status='passed', actual_exit_code=0, helper_sha256_after=hashes.copy(),
                     log=log_name, log_sha256=self.review.ref(log_name)['sha256'],
                     started_receipt=started_name, started_receipt_sha256=self.review.ref(started_name)['sha256'],
                     child_started=True, interruption_signal=None, binding_errors_after={}, recorder_exit_code=0)
        jwrite(self.root / name, value)

    def make_git_receipts(self, phase):
        for action in ['commit', 'push']:
            command = ['git', 'push', 'origin', 'main'] if action == 'push' else ['git', 'commit', '-m',
                'Expand 251 worked solutions and review all 556 exercises' if phase == 'content' else 'Record verified Source91 solution delivery']
            self.receipt('reports/solution-review/source91-' + phase + '-' + action + '-execution-v1.json',
                         command, self.pub, b'Synthetic Git success fixture; no Git mutation occurred\n')

    def make_delivery(self, phase, commit):
        name = 'reports/solution-review/source91-' + phase + '-delivery-attempt1.json'
        record = {'status': 'passed_source91_all31_live_assets_and_all3_Pages_jobs', 'phase': phase,
                  'plan': self.review.ref(self.release.PLAN), 'expected_commit': commit, 'remote_main': commit,
                  'helper': self.review.ref('book/solutions/verify_solution_delivery.py'),
                  'assets': [{'source': n, 'actual_sha256': h, 'expected_sha256': h,
                              'matches': True, 'http_status': 200} for n, h in self.plan['site_source91_sha256'].items()],
                  'Pages_build': {'commit': commit, 'status': 'built'},
                  'selected_run': {'id': 42, 'head_sha': commit, 'name': 'pages build and deployment',
                                   'status': 'completed', 'conclusion': 'success'},
                  'jobs': [{'name': n, 'run_id': 42, 'status': 'completed', 'conclusion': 'success'}
                           for n in ['build', 'report-build-status', 'deploy']]}
        for label in ['remote_observation', 'Pages_build_observation', 'actions_runs_observation', 'actions_jobs_observation']:
            log_name = name.replace('.json', '-' + label + '.log')
            write(self.root / log_name, b'Synthetic observation fixture\n')
            record[label] = {'actual_exit_code': 0, 'actual_workdir': str(self.pub), 'log': self.review.ref(log_name)}
        jwrite(self.root / name, record)
        native_name = 'reports/solution-review/source91-' + phase + '-delivery-execution-v1.json'
        command = ['python3', '-B', 'book/solutions/verify_solution_delivery.py', '--plan-sha256',
                   self.review.ref(self.release.PLAN)['sha256'], '--commit', commit, '--phase', phase, '--attempt', '1']
        self.receipt(native_name, command, self.root,
                     (json.dumps({'status': record['status'], 'report': self.review.ref(name)}) + '\n').encode())
        self.delivery_names[phase] = name; self.native_names[phase] = native_name

    def metadata(self, alias=None):
        argv = ['prepare_solution_delivery_metadata.py', '--delivery', alias or self.delivery_names['content'],
                '--native', self.native_names['content'],
                '--commit-receipt', 'reports/solution-review/source91-content-commit-execution-v1.json',
                '--push-receipt', 'reports/solution-review/source91-content-push-execution-v1.json']
        with patch.object(sys, 'argv', argv), redirect_stdout(io.StringIO()):
            self.helper.main()

    def closing_inputs(self):
        self.metadata()
        ready = self.review.read(self.helper.READY)
        for binding in ready['documents']:
            write(self.pub / binding['file'], (self.root / binding['file']).read_bytes())
        self.make_delivery('metadata', METADATA)
        self.make_git_receipts('metadata')
        self.git_head = self.git_remote = METADATA
        self.git_parent = CONTENT
        return ready

    def closing(self):
        argv = ['close_solution_publication.py', '--content-delivery', self.delivery_names['content'],
                '--content-native', self.native_names['content'], '--metadata-delivery', self.delivery_names['metadata'],
                '--metadata-native', self.native_names['metadata']]
        with patch.object(sys, 'argv', argv), redirect_stdout(io.StringIO()):
            self.close.main()


def refuses(function, kind=AssertionError):
    try:
        function()
    except kind as exc:
        return {'exception': type(exc).__name__, 'message': str(exc)}
    raise AssertionError('Expected refusal was not raised')


RESULTS = []


def case(name, function):
    try:
        RESULTS.append({'case': name, 'verdict': 'passed', 'detail': function()})
    except Exception as exc:
        RESULTS.append({'case': name, 'verdict': 'failed', 'exception': type(exc).__name__, 'message': str(exc)})


def positive_metadata():
    with Fixture() as f:
        f.metadata()
        ready = f.review.read(f.helper.READY)
        before = (f.root / f.helper.READY).read_bytes()
        for n, raw in f.originals.items():
            assert (f.root / f.helper.HISTORY / n).read_bytes() == raw
        tracker = f.review.read(TRACKER)
        assert len(tracker['exercises']) == 556
        assert all(r['status'] == 'independently_approved_installed_and_content_delivered' for r in tracker['exercises'])
        assert tracker['formal_coverage_changed'] is False
        progress = f.review.read('book/coverage/progress.json')
        for n in ['verified_checkpoint', 'historical_exercise_coverage', 'historical_material_coverage', 'formal_source_correspondence']:
            assert progress[n] == f.progress[n]
        assert progress['live_delivery_evidence']['metadata_push_and_metadata_live_check_pending'] is True
        assert ready['metadata_delivery_claimed'] is False and ready['formal_coverage_promoted'] is False
        assert b'will be committed' in (f.root / 'book/solutions/RELEASE.md').read_bytes()
        f.metadata()
        assert (f.root / f.helper.READY).read_bytes() == before
        return {'preserved_originals': 7, 'tracker_rows': 556, 'same_ready_receipt_on_rerun': True,
                'historical_formal_fields_unchanged': True, 'metadata_delivery_pending': True}


def alias(old=False):
    with Fixture(old=old) as f:
        other = 'reports/solution-review/copied-content-attempt1.json'
        write(f.root / other, (f.root / f.delivery_names['content']).read_bytes())
        if old:
            f.metadata(alias=other)
            return {'old_helper_accepted_unproduced_report_path': True}
        result = refuses(lambda: f.metadata(alias=other))
        assert not (f.root / f.helper.HISTORY).exists()
        return result


def original_snapshot_race(old=False):
    with Fixture(old=old) as f:
        original = f.originals['README.md']; real_sha = f.review.sha; fired = False
        def racing_sha(raw):
            nonlocal fired
            if raw == original and not fired:
                fired = True
                write(f.root / 'README.md', original + b'Late fixture edit\n')
            return real_sha(raw)
        with patch.object(f.review, 'sha', racing_sha):
            first = refuses(f.metadata)
        assert fired
        saved = f.root / f.helper.HISTORY / 'README.md'
        assert saved.exists()
        poisoned = saved.read_bytes() != original
        write(f.root / 'README.md', original)
        if old:
            assert poisoned
            return {'first_refusal': first, 'immutable_original_poisoned': True,
                    'corrected_resumption': refuses(f.metadata)}
        assert not poisoned
        f.metadata()
        return {'first_refusal': first, 'immutable_original_poisoned': False, 'corrected_resumption': 'passed'}


def interrupted_metadata():
    with Fixture() as f:
        real = f.release.atomic_copy
        def interrupted(destination, data):
            if destination == f.root / TRACKER:
                raise RuntimeError('Injected metadata interruption after progress installation')
            return real(destination, data)
        with patch.object(f.release, 'atomic_copy', interrupted):
            failure = refuses(f.metadata, RuntimeError)
        assert not (f.root / f.helper.READY).exists()
        assert (f.root / TRACKER).read_bytes() == f.originals[TRACKER]
        f.metadata()
        return {'failure': failure, 'resumption': 'passed', 'ready_published_only_after_complete_documents': True}


def late_document():
    with Fixture() as f:
        real = f.release.atomic_copy
        def edited(destination, data):
            result = real(destination, data)
            if destination == f.root / 'book/coverage/progress.json':
                write(f.root / 'README.md', b'Unexpected late user edit\n')
            return result
        with patch.object(f.release, 'atomic_copy', edited):
            result = refuses(f.metadata)
        assert (f.root / 'README.md').read_bytes() == b'Unexpected late user edit\n'
        assert not (f.root / f.helper.READY).exists()
        write(f.root / 'README.md', f.originals['README.md']); f.metadata()
        return {'refusal': result, 'unexpected_edit_preserved': True, 'restored_resumption': 'passed'}


def delivery_refusal(field, closure=False):
    with Fixture() as f:
        if closure:
            f.closing_inputs()
        phase = 'metadata' if closure else 'content'
        n = f.delivery_names[phase]; d = f.review.read(n)
        if field == 'asset': d['assets'][0]['actual_sha256'] = '0' * 64
        elif field == 'phase': d['phase'] = 'content' if closure else 'metadata'
        elif field == 'jobs': d['jobs'][0]['conclusion'] = 'failure'
        elif field == 'workflow': d['selected_run']['name'] = 'unrelated workflow'
        elif field == 'helper': d['helper']['sha256'] = '0' * 64
        elif field == 'native_binding':
            v = f.review.read(f.native_names[phase])
            v['helper_sha256_before']['book/solutions/verify_solution_delivery.py'] = '0' * 64
            v['helper_sha256_after']['book/solutions/verify_solution_delivery.py'] = '0' * 64
            jwrite(f.root / f.native_names[phase], v)
        elif field == 'report_ref': pass
        else: raise ValueError(field)
        jwrite(f.root / n, d)
        # A report-ref negative keeps the native log pointing at an obsolete SHA.
        # Other fixtures refresh that transport binding to isolate the requested gate.
        if field != 'report_ref':
            v = f.review.read(f.native_names[phase]); log = v['log']
            jwrite(f.root / log, {'status': d['status'], 'report': f.review.ref(n)})
            v['log_sha256'] = f.review.ref(log)['sha256']; jwrite(f.root / f.native_names[phase], v)
        else:
            with (f.root / n).open('ab') as output: output.write(b' ')
        result = refuses(f.closing if closure else f.metadata)
        return result


def git_refusal(kind, closure=False):
    with Fixture() as f:
        if closure: f.closing_inputs()
        if kind == 'parent': f.git_parent = 'd' * 40
        elif kind == 'head': f.git_head = 'd' * 40
        elif kind == 'remote': f.git_remote = 'd' * 40
        elif kind == 'dirty': f.git_dirty = ' M unrelated.txt\n'
        elif kind == 'branch': f.git_branch = 'other'
        return refuses(f.closing if closure else f.metadata)


def closure_positive_and_resume():
    with Fixture() as f:
        readiness = f.closing_inputs()
        published_progress = (f.pub / 'book/coverage/progress.json').read_bytes()
        f.closing()
        final = f.review.read(f.close.FINAL); first = (f.root / f.close.FINAL).read_bytes()
        progress = f.review.read('book/coverage/progress.json')
        assert final['formal_coverage_complete'] is False
        assert final['formal_source_correspondence_for_rewritten_answers'] == 'pending_explicit_rebase'
        assert progress['last_published_commit'] == METADATA
        assert progress['live_delivery_evidence']['metadata_push_and_metadata_live_check_pending'] is False
        assert progress['solution_depth_requirement']['publication_metadata_pending'] is False
        assert (f.pub / 'book/coverage/progress.json').read_bytes() == published_progress
        for n in ['verified_checkpoint', 'historical_exercise_coverage', 'historical_material_coverage', 'formal_source_correspondence']:
            assert progress[n] == f.progress[n]
        f.closing()
        assert (f.root / f.close.FINAL).read_bytes() == first
        return {'same_final_receipt_on_rerun': True, 'local_progress_closed': True,
                'publication_checkout_not_mutated_by_closure': True, 'formal_scope_not_promoted': True}


def closure_history_corrupt():
    with Fixture() as f:
        f.closing_inputs(); f.closing()
        history = f.root / 'reports/solution-review/source-history/before-source91-final-local-closure-v1/progress.json'
        original = history.read_bytes(); write(history, original + b' ')
        failure = refuses(f.closing)
        write(history, original); f.closing()
        return {'refusal': failure, 'restored_resumption': 'passed'}


def closure_interrupted():
    with Fixture() as f:
        f.closing_inputs(); real = f.release.atomic_copy
        def interrupted(destination, data):
            if destination == f.root / 'book/coverage/progress.json':
                raise RuntimeError('Injected final local progress interruption')
            return real(destination, data)
        with patch.object(f.release, 'atomic_copy', interrupted):
            failure = refuses(f.closing, RuntimeError)
        receipt = (f.root / f.close.FINAL).read_bytes()
        f.closing()
        assert (f.root / f.close.FINAL).read_bytes() == receipt
        return {'failure': failure, 'immutable_publication_receipt_preserved': True, 'local_progress_resumption': 'passed'}


case('metadata_positive_originals_556_tracker_formal_scope_and_completed_rerun', positive_metadata)
case('old_metadata_unbound_report_alias_acceptance_reproduced', lambda: alias(old=True))
case('current_metadata_rejects_unproduced_report_alias', alias)
case('old_metadata_snapshot_read_race_poisoned_resumption_reproduced', lambda: original_snapshot_race(old=True))
case('current_metadata_snapshot_read_race_preserves_original_and_resumes', original_snapshot_race)
case('metadata_interrupted_partial_install_resumes', interrupted_metadata)
case('metadata_late_document_edit_is_preserved_and_refused', late_document)
for field in ['asset', 'phase', 'jobs', 'workflow', 'helper', 'native_binding', 'report_ref']:
    case('metadata_rejects_' + field, lambda field=field: delivery_refusal(field))
for kind in ['parent', 'head', 'remote', 'dirty', 'branch']:
    case('metadata_rejects_git_' + kind, lambda kind=kind: git_refusal(kind))
case('closure_positive_local_only_formal_scope_and_completed_rerun', closure_positive_and_resume)
case('closure_rejects_corrupt_existing_history_and_restored_run_passes', closure_history_corrupt)
case('closure_final_progress_interruption_resumes_without_new_receipt', closure_interrupted)
for field in ['asset', 'phase', 'jobs', 'workflow', 'helper', 'native_binding', 'report_ref']:
    case('closure_rejects_' + field, lambda field=field: delivery_refusal(field, closure=True))
for kind in ['parent', 'head', 'remote', 'dirty', 'branch']:
    case('closure_rejects_git_' + kind, lambda kind=kind: git_refusal(kind, closure=True))

changed = {n: {'tested': sha(raw), 'current': sha((ROOT / n).read_bytes())}
           for n, raw in SOURCES.items() if raw != (ROOT / n).read_bytes()}
report = {'status': 'passed_isolated_delivery_metadata_and_closure_fixtures' if all(r['verdict'] == 'passed' for r in RESULTS) else 'fixture_failures',
          'generated_at_utc': datetime.now(timezone.utc).isoformat(),
          'driver': {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': sha(Path(__file__).read_bytes())},
          'helper_sha256_tested': {n: sha(raw) for n, raw in SOURCES.items()},
          'preserved_initial_metadata_helper': {'file': OLD_NAME, 'sha256': sha(OLD)},
          'helpers_changed_during_tests': changed, 'tests': RESULTS,
          'limits': ['All receipts, live/Pages responses and Git observations are synthetic fixture inputs.',
                     'Actual canonical documents/site/helpers and the publication repository were not changed.',
                     'The already independently reviewed release approval gate is substituted by an exact fixture-plan gate; these tests isolate the new downstream helpers.',
                     'No actual commit, push, live HTTP request or Pages job was executed.']}
jwrite(OUT, report)
print(json.dumps({'status': report['status'], 'case_count': len(RESULTS),
                  'passed': sum(r['verdict'] == 'passed' for r in RESULTS),
                  'failures': [r for r in RESULTS if r['verdict'] != 'passed'],
                  'helpers_changed': changed, 'report': OUT.relative_to(ROOT).as_posix()}, indent=2))
raise SystemExit(0 if report['status'].startswith('passed') and not changed else 1)
