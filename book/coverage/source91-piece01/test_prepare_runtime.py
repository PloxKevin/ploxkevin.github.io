"""Exercise the real preparer with full-size source-only temporary fixtures.

The seeded audit metadata is synthetic and the Lean files are never compiled.
These tests check selection, integrity and recovery, not formal correctness or
correspondence. All actual project, reader and proof bytes remain untouched.
"""
import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/source91-piece01/test_prepare_runtime.py'
spec = importlib.util.spec_from_file_location('piece01_runtime_preparer', Path(__file__).with_name('prepare_runtime.py'))
preparer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preparer)


def write(name, data):
    target = preparer.path(name)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)


def seed(helper_raw, names_raw):
    proofs = {}
    for i in range(1267):
        name = 'verification/lean/SafeLearning/FixtureBaseline' + str(i).zfill(4) + '.lean'
        raw = ('-- source-only test fixture\nnamespace FixtureBaseline' + str(i) + '\ntheorem ok : True := by trivial\nend FixtureBaseline' + str(i) + '\n').encode()
        write(preparer.PRIOR + '/' + name, raw)
        proofs[name] = preparer.sha(raw)
        if i < 4:
            write(name, raw)
    project = {}
    for name in sorted(preparer.PROJECT | {preparer.AGGREGATE}):
        raw = preparer.aggregate(proofs) if name == preparer.AGGREGATE else ('pinned fixture project: ' + name + '\n').encode()
        write(preparer.PRIOR + '/' + name, raw)
        project[name] = preparer.sha(raw)
    write(preparer.PRIOR + '/' + preparer.SUPPORT, names_raw)
    assets = {}
    for leaf in [*(f'fixture{i:02}.html' for i in range(29)), 'components.js', 'style.css']:
        name = 'SafeLearning/' + leaf
        raw = ('exact unchanged fixture asset: ' + name + '\n').encode()
        write(preparer.PRIOR + '/' + name, raw)
        write(name, raw)
        assets[name] = preparer.sha(raw)
    audit = {'status': 'passed', 'proof_file_count': 1267, 'theorem_count': 11472,
             'proof_sha256': proofs, 'project_sha256': project, 'source_sha256': assets}
    write(preparer.AUDIT, preparer.encode(audit))
    preparation = {'runtime': preparer.PRIOR, 'proof_files': 1267, 'all31_site_source91_sha256': assets,
                   'source_objects': [{'runtime_file': preparer.PRIOR + '/' + preparer.SUPPORT, 'sha256': preparer.sha(names_raw)}]}
    write(preparer.PRIOR_PREPARATION, preparer.encode(preparation))
    preparer.AUDIT_SHA256 = preparer.ref(preparer.AUDIT)['sha256']
    preparer.PRIOR_PREPARATION_SHA256 = preparer.ref(preparer.PRIOR_PREPARATION)['sha256']
    for part in ('packages', 'build'):
        original = preparer.ROOT / 'verification/lean/.lake' / part
        original.mkdir(parents=True)
        (original / 'cache-must-never-be-copied').write_bytes(b'cache marker\n')
        alias = preparer.ROOT / preparer.PRIOR / 'verification/lean/.lake' / part
        alias.parent.mkdir(exist_ok=True)
        alias.symlink_to(original, target_is_directory=True)
    write(preparer.SELF, helper_raw)
    proof_sources = []
    for module, count in zip(preparer.ADDITIONS, [8, 8, 9, 11]):
        name = 'verification/lean/SafeLearning/' + module + '.lean'
        text = 'namespace ' + module + '\n' + ''.join('theorem fixture' + str(i) + ' : True := by trivial\n' for i in range(count)) + 'end ' + module + '\n'
        write(name, text.encode())
        proof_sources.append(preparer.ref(name))
    for name in list(proofs)[:4]:
        proof_sources.append(preparer.ref(name))
    inventory = 'book/solutions/releases/source91-v1/source91-inventory/inventory.json'
    write(inventory, preparer.encode({'status': 'synthetic_fixture_inventory_not_coverage'}))
    packet = {'candidate_additions': list(preparer.ADDITIONS), 'reader_source': preparer.ref('SafeLearning/fixture00.html'),
              'inventory': preparer.ref(inventory), 'proof_sources': proof_sources,
              'whole_exercise_completion_claimed': False, 'formal_coverage_complete': False}
    write(preparer.CLAIMS, preparer.encode(packet))
    for i in range(8):
        write('verification/lean/SafeLearning/UnselectedWorking' + str(i) + '.lean', b'-- excluded working source\n')
    write(preparer.PRIOR + '/reports/archive-not-an-input', b'never copied\n')
    return preparer.ref(preparer.CLAIMS)['sha256']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    actual_root = preparer.ROOT
    audit_pin, preparation_pin = preparer.AUDIT_SHA256, preparer.PRIOR_PREPARATION_SHA256
    original_put, original_link = preparer.put, preparer.link_source
    helper_raw = (ROOT / preparer.SELF).read_bytes()
    names_raw = (ROOT / preparer.PRIOR / preparer.SUPPORT).read_bytes()
    protected = {n: preparer.ref(n)['sha256'] for n in [preparer.SELF, SELF, 'SafeLearning/landscape.html', preparer.CLAIMS]}
    cases = []
    try:
        for case in ['normal_complete_rerun', 'interrupted_plan_resume', 'interrupted_runtime_resume',
                     'source_changed_after_plan', 'corrupted_source_object', 'extra_runtime_proof',
                     'late_unvisited_runtime_edit', 'late_installed_runtime_edit', 'late_live_input_edit']:
            with tempfile.TemporaryDirectory(prefix='source91-piece01-runtime-test-') as temporary:
                preparer.ROOT = Path(temporary)
                claims_sha = seed(helper_raw, names_raw)
                plan = None
                error = None
                if case == 'interrupted_plan_resume':
                    count = 0

                    def stop_object(name, raw):
                        nonlocal count
                        if name.startswith(preparer.OBJECTS + '/'):
                            count += 1
                            if count == 3:
                                raise OSError('injected interruption during third source snapshot')
                        original_put(name, raw)

                    preparer.put = stop_object
                    try:
                        preparer.make_plan(preparer.PLAN, preparer.CLAIMS, claims_sha)
                    except OSError as exc:
                        error = str(exc)
                        assert not preparer.path(preparer.PLAN).exists() and not preparer.path(preparer.RUNTIME).exists()
                    else:
                        raise AssertionError('Interrupted snapshot unexpectedly completed')
                    preparer.put = original_put
                plan = preparer.make_plan(preparer.PLAN, preparer.CLAIMS, claims_sha)
                assert not preparer.path(preparer.RUNTIME).exists()
                assert len(plan['files']) == 1308 and plan['proof_count'] == 1271
                assert plan['expected_public_theorems_pending_actual_native_audit'] == 11508
                assert not plan['native_audit_claimed'] and not plan['correspondence_approval_claimed']
                plan_sha = preparer.ref(preparer.PLAN)['sha256']
                changed = b'unplanned fixture edit must be preserved\n'
                second_target = preparer.RUNTIME + '/' + plan['files'][1]['target']
                first_target = preparer.RUNTIME + '/' + plan['files'][0]['target']
                if case == 'source_changed_after_plan':
                    write('verification/lean/SafeLearning/' + preparer.ADDITIONS[-1] + '.lean', changed)
                if case == 'corrupted_source_object':
                    blob = preparer.path(plan['files'][0]['object'])
                    blob.unlink()
                    blob.write_bytes(changed)
                if case == 'extra_runtime_proof':
                    write(preparer.RUNTIME + '/verification/lean/SafeLearning/UnselectedExtra.lean', changed)
                count = 0

                def link(row):
                    nonlocal count
                    count += 1
                    if case == 'interrupted_runtime_resume' and count == 3:
                        raise OSError('injected interruption before third runtime link')
                    original_link(row)
                    if case == 'late_unvisited_runtime_edit' and count == 1:
                        write(second_target, changed)
                    if case == 'late_installed_runtime_edit' and count == 2:
                        preparer.path(first_target).unlink()
                        write(first_target, changed)
                    if case == 'late_live_input_edit' and count == 2:
                        write('SafeLearning/fixture00.html', changed)

                preparer.link_source = link
                try:
                    result, reused = preparer.apply(preparer.PLAN, plan_sha)
                except AssertionError as exc:
                    error = str(exc)
                except OSError as exc:
                    error = str(exc)
                else:
                    assert case in {'normal_complete_rerun', 'interrupted_plan_resume'}
                    assert not reused and result['proof_files'] == 1271
                preparer.link_source = original_link
                if case == 'interrupted_runtime_resume':
                    assert error and not preparer.path(preparer.REPORT).exists()
                    assert preparer.path(first_target).exists() and preparer.path(second_target).exists()
                    assert not preparer.path(preparer.RUNTIME + '/' + plan['files'][2]['target']).exists()
                    result, reused = preparer.apply(preparer.PLAN, plan_sha)
                    assert not reused
                if case in {'normal_complete_rerun', 'interrupted_plan_resume', 'interrupted_runtime_resume'}:
                    receipt = preparer.path(preparer.REPORT).read_bytes()
                    result, reused = preparer.apply(preparer.PLAN, plan_sha)
                    assert reused and preparer.path(preparer.REPORT).read_bytes() == receipt
                    proof_dir = preparer.path(preparer.RUNTIME + '/verification/lean/SafeLearning')
                    assert len(list(proof_dir.iterdir())) == 1271
                    assert not any(p.name.startswith('UnselectedWorking') for p in proof_dir.iterdir())
                    imports = preparer.path(preparer.RUNTIME + '/' + preparer.AGGREGATE).read_text().splitlines()
                    assert len(imports) == len(set(imports)) == 1271
                    assert not preparer.path(preparer.RUNTIME + '/reports').exists()
                    for row in plan['files']:
                        assert preparer.path(preparer.RUNTIME + '/' + row['target']).stat().st_ino == preparer.path(row['object']).stat().st_ino
                    for part in ['packages', 'build']:
                        alias = preparer.ROOT / preparer.RUNTIME / 'verification/lean/.lake' / part
                        assert alias.is_symlink() and alias.resolve() == (preparer.ROOT / 'verification/lean/.lake' / part).resolve()
                else:
                    assert error and not preparer.path(preparer.REPORT).exists()
                    if case in {'source_changed_after_plan', 'corrupted_source_object'}:
                        assert not preparer.path(preparer.RUNTIME).exists()
                    if case == 'extra_runtime_proof':
                        assert not preparer.path(first_target).exists()
                    if case == 'late_unvisited_runtime_edit':
                        assert preparer.path(second_target).read_bytes() == changed
                    if case == 'late_installed_runtime_edit':
                        assert preparer.path(first_target).read_bytes() == changed
                    if case == 'late_live_input_edit':
                        assert preparer.path('SafeLearning/fixture00.html').read_bytes() == changed
                cases.append({'case': case, 'status': 'passed', 'observed_injected_failure': error,
                              'fixture_baseline_proofs': 1267, 'fixture_selected_proofs': 1271,
                              'formal_compilation_or_correspondence_claimed': False})
                preparer.put, preparer.link_source = original_put, original_link
    finally:
        preparer.ROOT = actual_root
        preparer.AUDIT_SHA256, preparer.PRIOR_PREPARATION_SHA256 = audit_pin, preparation_pin
        preparer.put, preparer.link_source = original_put, original_link
    assert protected == {n: preparer.ref(n)['sha256'] for n in protected}
    report = {'status': 'passed_source91_piece01_runtime_integrity_and_recovery_fixtures',
              'helper': preparer.ref(preparer.SELF), 'test_helper': preparer.ref(SELF),
              'actual_command': sys.argv, 'cwd': str(Path.cwd()), 'cases': cases,
              'protected_before': protected, 'protected_after': {n: preparer.ref(n)['sha256'] for n in protected},
              'real_runtime_prepared': False, 'real_compiler_executed': False,
              'canonical_or_site_or_owner_files_modified': False,
              'scope': 'Full-size synthetic source-only temporary roots retain production cardinalities. Only the synthetic audit/preparation SHA pins are substituted; actual preparer functions, immutable writes, hash checks, hardlinks, exact import aggregation and cache links execute unchanged.'}
    preparer.put(args.report, preparer.encode(report))
    print(json.dumps({'status': report['status'], 'cases': len(cases), 'report': preparer.ref(args.report)}))


if __name__ == '__main__':
    main()
