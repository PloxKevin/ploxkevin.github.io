"""Fault-test the real publication planner/stager in synthetic roots only."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import tempfile
import traceback
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
HELPER = HERE / 'prepare_publication35.py'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def tree(root):
    return {p.relative_to(root).as_posix(): digest(p) for p in root.rglob('*') if p.is_file()}


class Fixture:
    def __init__(self, root):
        self.root = root
        spec = importlib.util.spec_from_file_location('publication35_fixture', HELPER)
        self.m = m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        m.ROOT, m.PUB = root, root / 'reports/book/publication-repo'
        m.PUB.mkdir(parents=True)
        m.SELF = root / 'book/coverage/checks/checkpoint35-root/prepare_publication35.py'
        m.SELF.parent.mkdir(parents=True)
        m.SELF.write_bytes(HELPER.read_bytes())
        self.events = []

        def put(name, data):
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
            return p

        def write(name, value):
            put(name, (json.dumps(value) + '\n').encode())
            return m.ref(name)

        selected, baseline, frozen = {}, {}, {}
        for i in range(1267):
            n = 'verification/lean/SafeLearning/Synthetic' + str(i) + '.lean'
            source = put('reports/full-coverage/checkpoint-35/' + n, ('-- synthetic source ' + str(i) + '\n').encode())
            selected[n] = {'sha256': digest(source)}
            frozen[n] = digest(source)
            if i < 1264:
                baseline[n] = selected[n]
                put('reports/book/publication-repo/' + n, source.read_bytes())
        n = 'verification/lean/SafeLearning.lean'
        source = put('reports/full-coverage/checkpoint-35/' + n, b'-- synthetic selected aggregate\n')
        frozen[n] = digest(source)
        for i in range(31):
            n = 'SafeLearning/asset' + str(i) + '.html'
            source = put('reports/full-coverage/checkpoint-35/' + n, ('synthetic site ' + str(i)).encode())
            put(n, source.read_bytes())
            put('reports/book/publication-repo/' + n, source.read_bytes())
            frozen[n] = digest(source)
        n = 'book/coverage/applied.json'
        source = put('reports/full-coverage/checkpoint-35/' + n, b'{"frozen_pruned_fixture":true}\n')
        frozen[n] = digest(source)
        put(n, b'{"unselected_working_metadata_fixture":true}\n')
        put('reports/book/publication-repo/' + n, b'{"baseline_fixture":true}\n')
        put('reports/book/publication-repo/unrelated.txt', b'original unrelated sentinel\n')
        put('.ignore', b'reports/full-coverage/runtime-checkpoint-*/\n')
        base = write('reports/full-coverage/checkpoint-34-selection.json', {'proof_files': baseline})
        selection = write(m.SELECTION, {'proof_files': selected, 'baseline_selection': base})
        manifest = write(m.MANIFEST, dict(status='formal_verification_passed_partial_coverage', source_only_snapshot=True,
            old_snapshot_or_lake_tree_copied=False, snapshot='reports/full-coverage/checkpoint-35', coverage_complete=False,
            selection_sha256=selection['sha256'], frozen_inputs_sha256=frozen))
        audit = write(m.EXPORT + '/verification-original.json', {'synthetic_fixture_only': True})
        log = put('reports/full-coverage/synthetic35-execution-v1.log', b'actual synthetic failed-command bytes\n')
        started = write('reports/full-coverage/synthetic35-execution-v1.started.json', {'status': 'started'})
        native = write('reports/full-coverage/synthetic35-execution-v1.json', dict(status='failed', actual_exit_code=9,
            actual_command=['synthetic-never-executed-fixture-command'], log=log.relative_to(root).as_posix(), log_sha256=digest(log),
            started_receipt=started['file'], started_receipt_sha256=started['sha256']))
        owner = write('reports/full-coverage/owner35-integration-v1.json', {'synthetic_fixture_only': True})
        working = write('reports/full-coverage/ledger35-working-v1.json', {'synthetic_fixture_only': True})
        ledger = write('reports/full-coverage/ledger35-frozen-source-only-v1.json', {'synthetic_fixture_only': True})
        final = write(m.FINAL, dict(status='passed_checkpoint35_actual_audit_export_and_source_only_freeze',
            manifest=manifest, selection=selection, audit=audit, native_execution=native, owner_integration=owner,
            working_ledger=working, frozen_ledger=ledger, proof_files=1267, public_theorems=11472))
        originals, documents = {}, {}
        for n in m.DOCS:
            put('reports/book/publication-repo/' + n, b'baseline synthetic documentation\n')
            originals[n] = m.ref(put('reports/full-coverage/source-history/documentation34-before-checkpoint35-v1/' + n,
                b'original synthetic documentation\n').relative_to(root).as_posix())
            documents[n] = digest(put(n, b'new synthetic documentation\n'))
        remaining = write('book/coverage/remaining-exercises35.json', {'synthetic_fixture_only': True})
        self.docs = 'reports/full-coverage/checkpoint35-documentation-v1.json'
        write(self.docs, dict(status='passed_synthetic_documentation_fixture', coverage_complete=False, finalization=final,
            document_sha256=documents, preserved_original_documents=originals, remaining_exercises=remaining))
        for folder in m.EVIDENCE + m.HISTORIES:
            (root / folder).mkdir(parents=True, exist_ok=True)
        put('reports/full-coverage/source-history/verification-before-checkpoint35-v1/verification/lean/verify.py', b'# old synthetic verifier\n')
        put('reports/full-coverage/source-history/owners34-before-checkpoint35-v1/core.json', b'{"old_owner_fixture":true}\n')
        put('reports/full-coverage/source-history/checkpoint35-failed-helper-inputs-v1/fixture-hash/old.py', b'# reconstructed synthetic failed helper\n')
        put('book/coverage/checks/checkpoint35-proofs/source-snapshots/fixture-hash/Synthetic.lean', b'-- preserved synthetic source\n')
        write('reports/full-coverage/live35-execution-v1.started.json', {'status': 'started'})
        put('reports/full-coverage/live35-execution-v1.log', b'incomplete output excluded from protected inputs\n')
        self.baseline = tree(m.PUB)

        def git(args, data=None):
            self.events.append(['git', *args])
            if args[:1] == ['symbolic-ref']:
                return b'main\n'
            if args[:1] == ['rev-parse']:
                return (m.BASELINE + '\n').encode()
            if args[:1] == ['status']:
                current = tree(m.PUB)
                assert set(self.baseline) <= set(current)
                return b''.join(((' M' if n in self.baseline else '??') + ' ' + n).encode() + b'\0'
                    for n in sorted(current) if current[n] != self.baseline.get(n))
            raise AssertionError('Unexpected Git command in synthetic fixture: ' + str(args))

        def ignored(args, **kwargs):
            self.events.append(args)
            assert args == ['git', 'check-ignore', '--stdin', '-z']
            return SimpleNamespace(returncode=0, stdout=b''.join(n + b'\0' for n in kwargs['input'].split(b'\0') if n.endswith(b'.log')))

        m.git, m.subprocess = git, SimpleNamespace(run=ignored)
        self.plan_name = m.PLAN

    def plan(self):
        value = self.m.build_plan(self.plan_name, self.docs)
        self.m.json_new(self.root / self.plan_name, value)
        self.plan_hash = digest(self.root / self.plan_name)
        self.value = value
        return value

    def interrupted(self):
        actual = self.m.copy_exact
        calls = [0]

        def copy(source, target, fingerprint, **kwargs):
            calls[0] += 1
            if calls[0] == 3:
                raise OSError('injected interruption before next atomic destination install')
            return actual(source, target, fingerprint, **kwargs)

        self.m.copy_exact = copy
        try:
            self.m.apply(self.value, self.plan_name, self.plan_hash)
            raise RuntimeError('Staging interruption was not injected')
        except OSError as error:
            assert str(error).startswith('injected interruption')
        finally:
            self.m.copy_exact = actual
        assert calls[0] == 3


def no_checkout_writes(f):
    value = f.plan()
    assert tree(f.m.PUB) == f.baseline
    entries = {r['destination']: r for r in value['files']}
    assert entries['book/coverage/applied.json']['source'].startswith('reports/full-coverage/checkpoint-35/')
    assert '.ignore' in entries
    assert {'reports/full-coverage/synthetic35-execution-v1' + suffix for suffix in ['.json', '.started.json', '.log']} <= set(entries)
    assert not any(n.startswith('reports/full-coverage/live35') for n in entries)
    assert not any('.lake' in Path(n).parts or 'runtime-checkpoint-' in n for n in entries)
    assert len(value['selected_proof_sha256']) == 1267 and len(value['unchanged_site_sha256']) == 31


def interruption_and_exact_retry(f):
    f.plan()
    f.interrupted()
    name, reused = f.m.apply(f.value, f.plan_name, f.plan_hash)
    assert reused is False
    receipt = (f.root / name).read_bytes()
    assert f.m.apply(f.value, f.plan_name, f.plan_hash) == (name, True)
    assert (f.root / name).read_bytes() == receipt
    assert (f.m.PUB / f.plan_name).read_bytes() == (f.root / f.plan_name).read_bytes()
    assert (f.m.PUB / 'book/coverage/applied.json').read_bytes() == b'{"frozen_pruned_fixture":true}\n'
    saved = json.loads(receipt)
    assert saved['ignored_paths_requiring_git_add_force'] and saved['git_index_mutated'] is False
    assert not list(f.m.PUB.rglob('.*-*'))


def corrupt_destination_rejected(f):
    f.plan()
    f.interrupted()
    row = next(r for r in reversed(f.value['files']) if r['destination_sha256_before'] is not None and r['destination_sha256_before'] != r['sha256'])
    destination = f.m.PUB / row['destination']
    destination.write_bytes(b'injected unreviewed destination bytes\n')
    before = tree(f.m.PUB)
    try:
        f.m.apply(f.value, f.plan_name, f.plan_hash)
        raise RuntimeError('Corrupted destination was accepted')
    except AssertionError:
        pass
    assert tree(f.m.PUB) == before


def corrupt_source_and_unrelated_dirty_rejected(f):
    f.plan()
    f.interrupted()
    source = f.root / next(r['source'] for r in f.value['files'] if r['destination'] == '.ignore')
    original = source.read_bytes()
    source.write_bytes(b'injected changed protected source\n')
    before = tree(f.m.PUB)
    try:
        f.m.apply(f.value, f.plan_name, f.plan_hash)
        raise RuntimeError('Changed protected source was accepted')
    except AssertionError:
        pass
    assert tree(f.m.PUB) == before
    source.write_bytes(original)
    sentinel = f.m.PUB / 'unrelated.txt'
    sentinel.write_bytes(b'unexpected concurrent checkout change\n')
    before = tree(f.m.PUB)
    try:
        f.m.apply(f.value, f.plan_name, f.plan_hash)
        raise RuntimeError('Unrelated dirty checkout path was accepted')
    except AssertionError:
        pass
    assert tree(f.m.PUB) == before


def abandoned_partial_write_recovered(f):
    f.plan()
    f.interrupted()
    row = f.value['files'][-1]
    temporary = f.m.scratch(row, f.plan_hash)
    temporary.parent.mkdir(parents=True, exist_ok=True)
    temporary.write_bytes(b'partial interrupted atomic copy, not a complete destination\n')
    name, reused = f.m.apply(f.value, f.plan_name, f.plan_hash)
    assert reused is False and not temporary.exists()
    assert (f.root / name).exists()
    unrelated = f.m.PUB / '.unrelated-temporary'
    unrelated.write_bytes(b'not owned by this stage\n')
    try:
        f.m.apply(f.value, f.plan_name, f.plan_hash)
        raise RuntimeError('Unrelated temporary checkout file was accepted')
    except AssertionError:
        pass
    assert unrelated.read_bytes() == b'not owned by this stage\n'


CASES = (no_checkout_writes, interruption_and_exact_retry, corrupt_destination_rejected,
         corrupt_source_and_unrelated_dirty_rejected, abandoned_partial_write_recovered)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    report = Path(args.report)
    before = {p.name: digest(p) for p in [HELPER, Path(__file__).resolve()]}
    cases = []
    for case in CASES:
        error, events = None, []
        with tempfile.TemporaryDirectory(prefix='checkpoint35-publication-fixture-') as temporary:
            try:
                f = Fixture(Path(temporary))
                case(f)
                events = f.events
            except Exception:
                error = traceback.format_exc()
        cases.append(dict(case=case.__name__, status='passed' if error is None else 'failed',
            simulated_read_only_git_requests=events, **({'error': error} if error else {})))
    after = {p.name: digest(p) for p in [HELPER, Path(__file__).resolve()]}
    code = 0 if before == after and all(c['status'] == 'passed' for c in cases) else 1
    value = dict(status='passed' if code == 0 else 'failed', actual_exit_code=code,
        helper_sha256_before=before, helper_sha256_after=after, cases=cases,
        scope='Actual planner/stager functions in isolated synthetic roots; Git metadata reads are simulated. All proof/native/math fields are synthetic bookkeeping fixtures.',
        production_publication_checkout_written=False, actual_git_commit_or_push_executed=False)
    with report.open('x') as output:
        json.dump(value, output, indent=2)
        output.write('\n')
        output.flush()
        os.fsync(output.fileno())
    print(json.dumps(dict(status=value['status'], cases=len(cases), failed_cases=[c['case'] for c in cases if c['status'] != 'passed'], report=str(report))))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
