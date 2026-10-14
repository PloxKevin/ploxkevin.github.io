"""Bounded independent runtime selection/refusal fixtures, never a Lean audit.

The prior audit/site/packet data is synthetic inside temporary roots. The four
candidate source bytes and pinned declaration extractor are copied read-only
as inputs; these fixtures exercise preparation, not theorem correctness.
"""
from contextlib import redirect_stdout
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
HELPER = 'book/coverage/source91-piece01/prepare_runtime.py'
OLD_HELPER = 'book/coverage/source91-piece01/source-history/prepare-runtime-before-hardlink-identity-v1.py'
OUT = 'reports/full-coverage/source91-piece01/runtime-independent-fixtures-v1.json'
SOURCE = (ROOT / HELPER).read_bytes()
OLD_SOURCE = (ROOT / OLD_HELPER).read_bytes()
PRIOR = 'reports/solution-review/runtime-source91-selected35-v1'
AUDIT = json.loads((ROOT / PRIOR / 'reports/lean-verification/verification.json').read_bytes())
PACKET = json.loads((ROOT / 'book/coverage/source91-piece01/claims-v2.json').read_bytes())
ADDITION_FILES = ['verification/lean/SafeLearning/' + n + '.lean' for n in PACKET['candidate_additions']]
ADDITION_BYTES = {n: (ROOT / n).read_bytes() for n in ADDITION_FILES}
SUPPORT_BYTES = (ROOT / PRIOR / 'book/coverage/lean_names.py').read_bytes()
EXCLUDED = sorted({p.relative_to(ROOT).as_posix() for p in (ROOT / 'verification/lean/SafeLearning').glob('*.lean')}
                  - set(AUDIT['proof_sha256']) - set(ADDITION_FILES))


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def jwrite(path, value):
    write(path, (json.dumps(value, indent=2) + '\n').encode())


class Fixture:
    def __init__(self, old=False):
        self.old = old

    def __enter__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='piece01-runtime-independent-')
        self.root = Path(self.temp.name)
        raw = OLD_SOURCE if self.old else SOURCE
        write(self.root / HELPER, raw)
        name = 'independent_piece01_runtime_fixture'
        spec = importlib.util.spec_from_file_location(name, self.root / HELPER)
        self.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.module)
        m = self.module
        proofs = {}
        for n in AUDIT['proof_sha256']:
            raw = b'-- Synthetic baseline source used only for runtime selection fixtures\n'
            write(self.root / PRIOR / n, raw)
            proofs[n] = sha(raw)
        projects = {}
        for n in AUDIT['project_sha256']:
            raw = (m.aggregate(proofs) if n == m.AGGREGATE else (ROOT / PRIOR / n).read_bytes())
            write(self.root / PRIOR / n, raw)
            projects[n] = sha(raw)
        assets = {}
        for n in AUDIT['source_sha256']:
            raw = ('Synthetic Source91 asset fixture: ' + n + '\n').encode()
            write(self.root / PRIOR / n, raw)
            write(self.root / n, raw)
            assets[n] = sha(raw)
        write(self.root / PRIOR / m.SUPPORT, SUPPORT_BYTES)
        audit = {'status': 'passed', 'proof_file_count': 1267, 'theorem_count': 11472,
                 'proof_sha256': proofs, 'project_sha256': projects, 'source_sha256': assets}
        jwrite(self.root / m.AUDIT, audit)
        m.AUDIT_SHA256 = sha((self.root / m.AUDIT).read_bytes())
        preparation = {'runtime': PRIOR, 'proof_files': 1267, 'all31_site_source91_sha256': assets,
                       'source_objects': [{'runtime_file': PRIOR + '/' + m.SUPPORT, 'sha256': sha(SUPPORT_BYTES)}]}
        jwrite(self.root / m.PRIOR_PREPARATION, preparation)
        m.PRIOR_PREPARATION_SHA256 = sha((self.root / m.PRIOR_PREPARATION).read_bytes())
        for n, raw in ADDITION_BYTES.items():
            write(self.root / n, raw)
        packet_sources = []
        for source in PACKET['proof_sources']:
            n = source['file']
            if n not in ADDITION_FILES:
                write(self.root / n, (self.root / PRIOR / n).read_bytes())
            packet_sources.append(m.ref(n))
        for n in EXCLUDED:
            write(self.root / n, ('-- Unselected canonical fixture: ' + n + '\n').encode())
        inventory = 'book/solutions/releases/source91-v1/source91-inventory/inventory.json'
        jwrite(self.root / inventory, {'status': 'synthetic_inventory_fixture', 'counts': {'exercises': 556}})
        packet = {'candidate_additions': list(m.ADDITIONS),
                  'reader_source': {'file': 'SafeLearning/landscape.html', 'sha256': assets['SafeLearning/landscape.html']},
                  'inventory': m.ref(inventory), 'proof_sources': packet_sources}
        jwrite(self.root / m.CLAIMS, packet)
        self.claim_sha = sha((self.root / m.CLAIMS).read_bytes())
        for n in ('packages', 'build'):
            canonical = self.root / 'verification/lean/.lake' / n
            canonical.mkdir(parents=True)
            link = self.root / PRIOR / 'verification/lean/.lake' / n
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(canonical, target_is_directory=True)
        return self

    def __exit__(self, *args):
        self.temp.cleanup()

    def plan(self):
        self.selection = self.module.make_plan(self.module.PLAN, self.module.CLAIMS, self.claim_sha)
        self.plan_sha = self.module.ref(self.module.PLAN)['sha256']
        return self.selection

    def apply(self):
        return self.module.apply(self.module.PLAN, self.plan_sha)


def refuses(fn, kind=AssertionError):
    try:
        fn()
    except kind as exc:
        return {'exception': type(exc).__name__, 'message': str(exc)}
    raise AssertionError('Expected refusal was not raised')


RESULTS = []


def case(name, fn):
    try:
        RESULTS.append({'case': name, 'verdict': 'passed', 'detail': fn()})
    except Exception as exc:
        RESULTS.append({'case': name, 'verdict': 'failed', 'exception': type(exc).__name__, 'message': str(exc)})
    print(json.dumps({'case': name, 'verdict': RESULTS[-1]['verdict']}), flush=True)


def complete_and_resume():
    with Fixture() as f:
        m = f.module; plan = f.plan()
        assert len(plan['files']) == 1308
        proof_rows = [r for r in plan['files'] if r['kind'] in {'baseline_proof', 'candidate_proof'}]
        assert len(proof_rows) == 1271 and not set(EXCLUDED).intersection(r['target'] for r in proof_rows)
        assert len([r for r in plan['files'] if r['kind'] == 'site']) == 31
        assert sum(plan['candidate_source_public_theorem_counts'].values()) == 36
        report, reused = f.apply(); assert reused is False
        assert report['native_aggregate_audit_claimed'] is False
        assert report['source_correspondence_approval_claimed'] is False and report['coverage_complete'] is False
        for row in plan['files']:
            obj = m.path(row['object']); target = m.path(m.RUNTIME + '/' + row['target'])
            assert obj.samefile(target) and obj.stat().st_mode & 0o222 == target.stat().st_mode & 0o222 == 0
        first = m.path(m.REPORT).read_bytes(); f.plan(); second, reused = f.apply()
        assert reused is True and m.path(m.REPORT).read_bytes() == first
        return {'sources': 1308, 'proofs': 1271, 'site_assets': 31, 'excluded_canonical_modules': len(EXCLUDED),
                'aggregate_imports': len(m.path(m.RUNTIME + '/' + m.AGGREGATE).read_text().splitlines()),
                'hardlinks_read_only': True, 'identical_completed_rerun': True,
                'native_audit_and_correspondence_not_claimed': True}


def independent_copy(old=False):
    with Fixture(old=old) as f:
        m = f.module; plan = f.plan()
        row = next(r for r in plan['files'] if r['kind'] == 'candidate_proof')
        target = m.path(m.RUNTIME + '/' + row['target'])
        write(target, m.path(row['object']).read_bytes()); target.chmod(0o444)
        assert not target.samefile(m.path(row['object']))
        if old:
            result, _ = f.apply()
            assert result['immutable_source_object_hardlinks'] is True
            return {'old_helper_claimed_all_hardlinks_for_independent_matching_copy': True}
        return refuses(f.apply)


def archive(old=False):
    with Fixture(old=old) as f:
        m = f.module; f.plan(); f.apply()
        path = m.path(m.RUNTIME + '/reports/archive/unselected.lean')
        write(path, b'-- unselected archive payload fixture\n')
        if old:
            f.apply()
            return {'old_helper_accepted_archive_inside_reports_exception': True}
        return refuses(f.apply)


def interruption():
    with Fixture() as f:
        m = f.module; f.plan(); real = m.link_source; count = 0
        def interrupted(row):
            nonlocal count
            count += 1
            if count == 24:
                raise RuntimeError('Injected interruption after23 exact source links')
            return real(row)
        with patch.object(m, 'link_source', interrupted):
            failure = refuses(f.apply, RuntimeError)
        assert not m.path(m.REPORT).exists()
        report, _ = f.apply()
        assert report['proof_files'] == 1271
        return {'failure': failure, 'incomplete_receipt_not_published': True, 'resumption': 'passed'}


def other_boundaries():
    details = []
    for kind in ['extra_proof', 'lake_archive', 'writable_object']:
        with Fixture() as f:
            m = f.module; plan = f.plan(); f.apply()
            if kind == 'extra_proof':
                write(m.path(m.RUNTIME + '/' + EXCLUDED[0]), b'-- excluded proof fixture\n')
            elif kind == 'lake_archive':
                write(m.path(m.RUNTIME + '/verification/lean') / '.lake/archive/unselected.lean', b'-- excluded payload\n')
            else:
                m.path(plan['files'][0]['object']).chmod(0o644)
            details.append({'boundary': kind, 'refusal': refuses(f.apply)})
    return details


def late_input():
    with Fixture() as f:
        m = f.module; plan = f.plan(); real = m.link_source; last = plan['files'][-1]['target']
        changed = ADDITION_FILES[0]; original = m.path(changed).read_bytes()
        def edited(row):
            result = real(row)
            if row['target'] == last:
                write(m.path(changed), original + b'-- injected late source change\n')
            return result
        with patch.object(m, 'link_source', edited):
            failure = refuses(f.apply)
        assert not m.path(m.REPORT).exists()
        assert m.path(changed).read_bytes() != original
        write(m.path(changed), original); f.apply()
        return {'failure': failure, 'late_source_edit_preserved': True, 'report_not_published_before_refusal': True,
                'restored_input_resumption': 'passed'}


def packet_mismatch():
    with Fixture() as f:
        m = f.module; f.plan(); packet = m.read(m.CLAIMS)
        packet['proof_sources'][0]['sha256'] = '0' * 64
        jwrite(m.path(m.CLAIMS), packet)
        failure = refuses(f.apply)
        assert not m.path(m.RUNTIME).exists()
        return {'failure': failure, 'runtime_not_staged_for_changed_packet': True}


case('current_exact_selection_read_only_hardlinks_and_completed_resumption', complete_and_resume)
case('current_rejects_matching_independent_copy', independent_copy)
case('current_interrupted_source_links_resume_without_false_receipt', interruption)
case('current_late_candidate_edit_refused_and_restored_resumption_passes', late_input)

changed = SOURCE != (ROOT / HELPER).read_bytes()
result = {'status': 'passed_bounded_independent_runtime_fixtures' if all(r['verdict'] == 'passed' for r in RESULTS) and not changed else 'fixture_failures',
          'generated_at_utc': datetime.now(timezone.utc).isoformat(),
          'helper_tested': {'file': HELPER, 'sha256': sha(SOURCE)},
          'driver': {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': sha(Path(__file__).read_bytes())},
          'helper_changed_during_tests': changed, 'tests': RESULTS,
          'limits': ['Audit, Source91 site and claim packet identities are synthetic fixture inputs under temporary roots; the 1267 baseline proof paths share a synthetic source body.',
                     'The four candidate source files and declaration extractor are actual bytes copied for source-index testing only.',
                     'No Lean compilation, kernel replay, axiom audit or semantic correspondence approval was performed by these fixtures.',
                     'No canonical source/helper, owner ledger, actual runtime or prior report was modified.']}
jwrite(ROOT / OUT, result)
print(json.dumps({'status': result['status'], 'cases': len(RESULTS),
                  'failures': [r for r in RESULTS if r['verdict'] != 'passed'],
                  'helper_changed': changed, 'helper_sha256': sha(SOURCE), 'report': OUT}, indent=2))
raise SystemExit(0 if result['status'].startswith('passed') else 1)
