"""Check the hardened object identity and native-output boundaries in one fixture."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_prepare_runtime as fixture_source

p = fixture_source.preparer
ROOT = p.ROOT
SELF = p.PIECE + '/test_runtime_boundaries_v2.py'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    helper_raw = (ROOT / p.SELF).read_bytes()
    names_raw = (ROOT / p.PRIOR / p.SUPPORT).read_bytes()
    original_pins = p.AUDIT_SHA256, p.PRIOR_PREPARATION_SHA256
    protected = {n: p.ref(n)['sha256'] for n in [p.SELF, SELF, p.CLAIMS, 'SafeLearning/landscape.html']}
    cases = []

    def refuses(name, function, text):
        try:
            function()
        except AssertionError as exc:
            assert text in str(exc), str(exc)
            cases.append({'case': name, 'status': 'passed', 'actual_refusal': str(exc)})
        else:
            raise AssertionError('Boundary accepted: ' + name)

    try:
        with tempfile.TemporaryDirectory(prefix='source91-piece01-boundaries-') as temporary:
            p.ROOT = Path(temporary)
            claims_sha = fixture_source.seed(helper_raw, names_raw)
            plan = p.make_plan(p.PLAN, p.CLAIMS, claims_sha)
            row = plan['files'][0]
            blob = p.path(row['object'])
            target = p.path(p.RUNTIME + '/' + row['target'])
            target.parent.mkdir(parents=True)
            target.write_bytes(blob.read_bytes())
            target.chmod(0o444)
            refuses('byte_identical_independent_copy_refused', lambda: p.check_runtime(plan), 'not its planned object')
            assert target.read_bytes() == blob.read_bytes() and not target.samefile(blob)
            target.unlink()
            blob.chmod(0o644)
            refuses('writable_existing_object_refused', lambda: p.validate_objects(plan), 'Writable source object')
            refuses('writable_object_not_silently_repaired', lambda: p.put(row['object'], blob.read_bytes(), readonly=True), 'Writable source object')
            assert blob.stat().st_mode & 0o222
            blob.chmod(0o444)
            p.link_source(row)
            target.chmod(0o644)
            refuses('writable_hardlinked_runtime_target_refused', lambda: p.check_runtime(plan), 'Writable runtime source')
            assert target.samefile(blob) and target.stat().st_mode & 0o222
            target.chmod(0o444)
            assert not p.path(p.REPORT).exists()
            fingerprint = p.ref(p.PLAN)['sha256']
            result, reused = p.apply(p.PLAN, fingerprint)
            assert not reused and result['proof_files'] == 1271
            receipt = p.path(p.REPORT).read_bytes()
            for item in plan['files']:
                installed = p.path(p.RUNTIME + '/' + item['target'])
                assert installed.samefile(p.path(item['object'])) and not installed.stat().st_mode & 0o222
            result, reused = p.apply(p.PLAN, fingerprint)
            assert reused and p.path(p.REPORT).read_bytes() == receipt
            cases.append({'case': 'full1308_sources_readonly_hardlinked_and_completed_rerun_exact', 'status': 'passed',
                          'proofs': 1271, 'expected_theorems_pending_native_audit': 11508})
            archive = p.path(p.RUNTIME + '/reports/archive')
            archive.mkdir(parents=True)
            (archive / 'unselected.lean').write_bytes(b'-- must not be accepted\n')
            refuses('hidden_report_archive_refused', lambda: p.check_runtime(plan, complete=True), 'Unexpected native report directory')
            (archive / 'unselected.lean').unlink()
            archive.rmdir()
            lake = p.path(p.RUNTIME + '/verification/lean') / '.lake'
            hidden = lake / 'config/1/archive'
            hidden.mkdir(parents=True)
            (hidden / 'unselected.lean').write_bytes(b'-- must not be accepted\n')
            refuses('hidden_config_archive_refused', lambda: p.check_runtime(plan, complete=True), '')
            (hidden / 'unselected.lean').unlink()
            hidden.rmdir()
            config = lake / 'config/1'
            for leaf in ['lakefile.olean', 'lakefile.olean.trace']:
                (config / leaf).write_bytes(b'generated native config fixture\n')
            output = p.path(p.RUNTIME + '/reports/lean-verification')
            output.mkdir()
            for leaf in ['lean-version.txt', 'build.log', 'axioms.log', 'verification.json',
                         'kernel-progress.json', 'reused-verification-original.json',
                         '.kernel-progress.json-fixture01', '.verification.json-fixture02',
                         'kernel-SafeLearning-FixtureBaseline0000.log']:
                (output / leaf).write_bytes(b'generated native report fixture\n')
            p.path(p.RUNTIME + '/verification/lean/AxiomAudit.lean').write_bytes(b'-- generated native audit fixture\n')
            result, reused = p.apply(p.PLAN, fingerprint)
            assert reused and p.path(p.REPORT).read_bytes() == receipt
            cases.append({'case': 'bounded_real_native_output_names_config_and_partial_json_temporaries_accepted',
                          'status': 'passed', 'native_audit_claimed': False})
    finally:
        p.ROOT = ROOT
        p.AUDIT_SHA256, p.PRIOR_PREPARATION_SHA256 = original_pins
    after = {n: p.ref(n)['sha256'] for n in protected}
    assert protected == after
    report = {'status': 'passed_hardened_runtime_identity_and_native_output_boundaries',
              'helper': p.ref(p.SELF), 'test_helper': p.ref(SELF), 'fixture_seed_helper': p.ref(fixture_source.SELF),
              'actual_command': sys.argv, 'cwd': str(Path.cwd()), 'cases': cases,
              'protected_before': protected, 'protected_after': after,
              'prior_nine_case_tests': p.ref(p.PIECE + '/runtime-tests-v1.json'),
              'prior_test_revision_scope': 'Nine integrity/interruption cases remain bound to the preserved pre-hardening helper; these fresh cases exercise the final identity/output changes and complete full-size apply/reruns.',
              'actual_production_runtime_prepared': False, 'compiler_executed': False,
              'formal_source_correspondence_or_coverage_approval_claimed': False,
              'scope': 'Actual helper functions with a synthetic full-size temporary fixture: 1267 baseline sources, four candidates, 1308 staged sources. The source-only fixture seed substitutes only its own audit/preparation fingerprints. No canonical/site/proof/owner file is modified.'}
    p.put(args.report, p.encode(report))
    print(json.dumps({'status': report['status'], 'cases': len(cases), 'report': p.ref(args.report)}))


if __name__ == '__main__':
    main()
