"""Install the exact reviewed polygonal component and prepare an isolated ledger."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/recovery32-core/polygonal14-component-v1'
CANONICAL = 'verification/lean/SafeLearning/CompleteCoreFilippovPolygonal32.lean'
MODULE = Path(CANONICAL).stem
PEER = 'book/coverage/checks/future32-applied/polygonal14-independent-v1/polygonal14-all-bodies-actual-Euler-component-independent-applied32-closed-peer-v1.json'
REQUEST = 'book/coverage/checks/future32-core/filippov-polygonal14-author-v1/filippov-polygonal14-full-source-actual-Euler-component-independent-review-request32-v1.json'
CONTEXT = Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CONTEXT_SHA = '0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
SOURCE_SHA = '868e7f57c4259095bb0621f2aa00b2868e31e1a2aa5cc236b66c2f0e520a65c9'
HELPERS = {
    'standalone': ('book/coverage/check_core_standalone.py', '124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'),
    'named': ('book/coverage/check_core_named_build.py', '605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069'),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def locate(name):
    return Path(name) if Path(name).is_absolute() else ROOT / name


def ref(path):
    path = locate(path)
    return {'file': path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path),
            'sha256': sha(path), 'bytes': path.stat().st_size}


def read(name):
    return json.loads(locate(name).read_bytes())


def new(path, data):
    assert path.is_relative_to(ROOT) and not path.exists() and not path.is_symlink()
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as output:
        output.write(data)


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def main():
    assert not BASE.exists() and not (ROOT / CANONICAL).exists()
    assert sha(CONTEXT) == CONTEXT_SHA
    context = read(CONTEXT)
    assert context['status'] == 'actual_source81_installed_owner31_selected31_audited_TMP_context_only'
    protected = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
    assert len(context['owners_sha256']) == 5
    peer = read(PEER)
    request = read(REQUEST)
    assert peer['status'] == 'passed_independent_full_polygonal14_actual_Euler_component_math_body_domain_closed_peer'
    assert peer['errors'] == [] and peer['all14_components_mathematically_approved'] is True
    assert peer['current_whole_Exercise16_or_generic_Filippov_existence_approved'] is False
    assert peer['source']['sha256'] == SOURCE_SHA and peer['public_theorem_count'] == 14
    source = locate(request['all_original_byte_aliases']['/tmp/CompleteCoreFilippovPolygonalConstruction32-draft-v3.lean']['file']) if 'all_original_byte_aliases' in request else locate(peer['all_original_byte_aliases']['/tmp/CompleteCoreFilippovPolygonalConstruction32-draft-v3.lean']['file'])
    assert sha(source) == SOURCE_SHA
    trial = read('/tmp/root-filippov-polygonal14-installed-owner31-trial3.json')
    assert trial['actual_exit_code'] == trial['actual_runner_exit_code'] == 0
    assert trial['source_sha256_before'] == trial['source_sha256_after'] == trial['source_snapshot_sha256'] == SOURCE_SHA
    for name, digest in peer['required_evidence_artifacts_sha256'].items():
        assert sha(locate(name)) == digest, name
    for name, digest in HELPERS.values():
        assert sha(ROOT / name) == digest
        protected[name] = digest
    for name in [PEER, REQUEST, 'book/coverage/validate.py', 'book/coverage/lean_names.py', str(Path(__file__))]:
        protected[name] = sha(locate(name))

    spec = importlib.util.spec_from_file_location('polygonal32_names', ROOT / 'book/coverage/lean_names.py')
    names = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(names)
    declarations = names.declarations(source.read_text())
    theorem_names = [row['name'] for row in declarations if row['kind'] in ['theorem', 'lemma']]
    assert len(theorem_names) == 14 and len(declarations) == 16
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(source.read_text()))
    audit = read(context['actual_audit']['file'])
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1248
    old_names = {r['name'] for name in audit['proof_sha256'] for r in names.declarations((ROOT / name).read_text())}
    assert not old_names.intersection(row['name'] for row in declarations)

    def guard():
        assert sha(CONTEXT) == CONTEXT_SHA
        for name, digest in protected.items():
            assert sha(locate(name)) == digest, name
        if (ROOT / CANONICAL).exists():
            assert sha(ROOT / CANONICAL) == SOURCE_SHA

    guard()
    BASE.mkdir(parents=True)
    originals = {}
    original_inputs = {str(CONTEXT): CONTEXT_SHA, PEER: sha(ROOT / PEER), REQUEST: sha(ROOT / REQUEST),
                       'book/coverage/core.json': sha(ROOT / 'book/coverage/core.json')}
    original_inputs.update(peer['required_evidence_artifacts_sha256'])
    for name, digest in original_inputs.items():
        path = locate(name)
        assert sha(path) == digest
        target = BASE / 'exact-original-by-sha256' / digest / path.name
        if target.exists():
            assert sha(target) == digest
        else:
            new(target, path.read_bytes())
        originals[name] = ref(target)
    new(ROOT / CANONICAL, source.read_bytes())
    snapshot = BASE / 'source-snapshot' / Path(CANONICAL).name
    new(snapshot, source.read_bytes())
    guard()
    pairs = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONHOME', None)
    for kind, suffix in [('standalone', '-standalone.json'), ('named', '-named-build.json')]:
        name = 'book/coverage/checks/' + MODULE + suffix
        log_name = 'book/coverage/checks/' + MODULE + ('.log' if kind == 'standalone' else '-named-build.log')
        assert not (ROOT / name).exists() and not (ROOT / log_name).exists()
        invocation_log = BASE / (kind + '-helper-invocation.log')
        command = ['python3', HELPERS[kind][0], MODULE]
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        with invocation_log.open('xb') as output:
            result = subprocess.run(command, cwd=ROOT, env=environment, stdout=output, stderr=subprocess.STDOUT)
        finished = datetime.now(timezone.utc).isoformat()
        elapsed = time.monotonic() - tick
        guard()
        record = read(name)
        actual_command = ['lake', 'env', 'lean', 'SafeLearning/' + MODULE + '.lean'] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + MODULE]
        assert record['command'] == actual_command and record['actual_workdir'] == str(ROOT / 'verification/lean')
        assert record['source_sha256_before'] == record['source_sha256_after'] == SOURCE_SHA
        assert record['exit_code'] == result.returncode and sha(ROOT / record['log']) == record['log_sha256']
        native = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
                  'actual_command': command, 'actual_workdir': str(ROOT), 'started_at_utc': started,
                  'finished_at_utc': finished, 'elapsed_seconds': elapsed, 'helper': ref(HELPERS[kind][0]),
                  'log': ref(invocation_log), 'actual_compiler_record': ref(name), 'protection_errors': [],
                  'canonical_source': ref(CANONICAL), 'aggregate_kernel_axiom_or_full_coverage_claimed': False}
        native_path = BASE / (kind + '-actual-execution-v1.json')
        new(native_path, encode(native))
        assert result.returncode == 0 and record['status'] == 'passed'
        pairs.append({'kind': kind, 'source': ref(CANONICAL), 'actual_record': ref(name),
                      'raw_log': ref(record['log']), 'source_snapshot': ref(snapshot),
                      'actual_exit_code': result.returncode, 'actual_helper_execution': ref(native_path)})

    old = read('book/coverage/core.json')
    candidate = copy.deepcopy(old)
    exercise = next(row for row in candidate['exercises'] if row['inventory_key'] == 'barriers.html::exercise-16')
    assert exercise['status'] == 'partial'
    remaining = next(row for row in exercise['claims'] if row['status'] == 'pending')
    before_remaining = copy.deepcopy(remaining)
    component_id = 'barriers.html::exercise-16::actual-polygonal-global-bound-component32'
    assert not any(row['id'] == component_id for row in exercise['claims'])
    exercise['claims'].append({
        'id': component_id,
        'statement_in_prose': 'Component toward the locally bounded Filippov existence clause: for an actual globally bounded field, finite ramp sums at actual recursively constructed Euler nodes define a continuous polygonal path starting at x₀. Its radius is at most tM and its increment norm is at most (t−s)M for 0≤s≤t, uniformly in the finite node count and nonnegative step size.',
        'kind': 'reviewed_mathematical_component_toward_pending_Filippov_local_existence',
        'status': 'proved', 'lean_declarations': [row['name'] for row in declarations],
        'hypotheses': peer['assumptions_and_domains'],
        'correspondence': 'The exact source clause is the universal local-existence assertion in Exercise 10.1(c), not a printed polygonal estimate. This proves only a construction component under the stronger explicit global pointwise bound ‖F z‖≤M. The actual selected essential velocity set and actual recursive Euler nodes come from the unchanged Euler24 import. Scalar ramps telescope and produce min(nh,t); the triangle inequality and true chosen-velocity norm bound derive both estimates, with M≥0 derived at z=0. No estimate, equicontinuity, selector measurability, derivative inclusion, or existence conclusion is assumed. This adds no completed exercise or reviewed enclosing source unit.',
        'remaining_gaps': [], 'source_review': {'peer': ref(PEER), 'request': ref(REQUEST),
            'exact_exercise_text_sha256': exercise['text_sha256'],
            'whole_exercise_or_enclosing_material_approved': False},
        'component_scope_limits': peer['remaining_whole_existence_gaps'],
    })
    assert remaining == before_remaining and exercise['status'] == 'partial'
    assert candidate['material_claims'] == old['material_claims']
    evidence = {}
    for pair in pairs:
        for key in ['actual_record', 'raw_log', 'source_snapshot', 'actual_helper_execution']:
            evidence[pair[key]['file']] = pair[key]['sha256']
    candidate['proof_files'][CANONICAL] = {
        'sha256': SOURCE_SHA, 'theorem_count': 14, 'public_theorem_names': theorem_names,
        'public_names': [row['name'] for row in declarations], 'actual_pair': pairs,
        'evidence_sha256': evidence, 'original_math_peers': [ref(PEER)],
        'component_only_source_association': {'exercise': exercise['inventory_key'], 'whole_exercise_approved': False,
            'scope': 'Finite continuous polygonal family and two uniform estimates under ProperSpace/full-support/global pointwise bounded-field assumptions. General local existence and whole source units remain pending.'},
        'scope': 'Exact approved source bytes and two actual compiler commands. Aggregate build, fresh kernel replay and standard-axiom audit remain required before batch selection.'}
    candidate['future32_actual_polygonal_component_binding'] = {
        'status': 'reviewed_actual_canonical_compilation_component_only_candidate_not_installed',
        'canonical_source': ref(CANONICAL), 'original_core_ledger': originals['book/coverage/core.json'],
        'original_math_peer': ref(PEER), 'component_id': component_id,
        'whole_exercise_status': 'partial', 'enclosing_material_status_unchanged': True,
        'coverage_complete': False}
    candidate_path = BASE / 'core-candidate.json'
    new(candidate_path, encode(candidate))

    isolated = BASE / 'isolated-ledger-root'
    coverage = isolated / 'book/coverage'
    coverage.mkdir(parents=True)
    for name in ['validate.py', 'lean_names.py']:
        new(coverage / name, (ROOT / 'book/coverage' / name).read_bytes())
    for name in ['inventory.json', 'foundations.json', 'applied.json', 'modules.json']:
        (coverage / name).symlink_to(ROOT / 'book/coverage' / name)
    (coverage / 'core.json').symlink_to(candidate_path)
    (isolated / 'SafeLearning').symlink_to(ROOT / 'SafeLearning', target_is_directory=True)
    (isolated / 'verification').mkdir()
    (isolated / 'verification/lean').symlink_to(ROOT / 'verification/lean', target_is_directory=True)
    report_path = BASE / 'ledger-candidate-integrity-v1.json'
    command = ['python3', str(coverage / 'validate.py'), '--output', str(report_path)]
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    validation_log = BASE / 'ledger-candidate-validation-v1.log'
    with validation_log.open('xb') as output:
        result = subprocess.run(command, cwd=isolated, env=environment, stdout=output, stderr=subprocess.STDOUT)
    validation_native = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
                         'actual_command': command, 'actual_workdir': str(isolated), 'started_at_utc': started,
                         'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
                         'log': ref(validation_log), 'report': ref(report_path), 'candidate': ref(candidate_path),
                         'other_owner_ledgers_unchanged': True, 'coverage_complete': False}
    validation_native_path = BASE / 'ledger-candidate-validation-actual-v1.json'
    new(validation_native_path, encode(validation_native))
    validation = read(report_path)
    assert result.returncode == 0 and validation['integrity_status'] == 'passed' and validation['errors'] == []
    assert validation['mathematical_coverage_complete'] is False
    assert validation['counts']['statuses']['exercise:complete_math'] == 536
    assert validation['counts']['statuses']['exercise:partial'] == 8 and validation['counts']['statuses']['exercise:pending'] == 12
    assert validation['counts']['material_review_statuses'] == {'reviewed': 4835, 'pending': 7939}
    guard()
    readiness = {'status': 'passed_exact_reviewed_polygonal14_canonical_pair_component_candidate32', 'errors': [],
                 'created_at_utc': datetime.now(timezone.utc).isoformat(), 'canonical_source': ref(CANONICAL),
                 'source_snapshot': ref(snapshot), 'public_theorem_count': 14, 'public_name_count': 16,
                 'actual_compiler_command_count': 2, 'actual_paired_records': pairs,
                 'original_math_peer': ref(PEER), 'original_review_request': ref(REQUEST),
                 'exact_original_byte_aliases': originals, 'protected_inputs_sha256': protected,
                 'candidate': ref(candidate_path), 'candidate_validation': ref(validation_native_path),
                 'candidate_integrity': ref(report_path), 'whole_exercise_and_material_status_unchanged': True,
                 'aggregate_kernel_axiom_owner_installation_or_publication_claimed': False,
                 'coverage_complete': False}
    output_path = BASE / 'polygonal14-readiness-v1.json'
    new(output_path, encode(readiness))
    print(json.dumps({'status': readiness['status'], 'canonical_source': ref(CANONICAL),
                      'candidate': ref(candidate_path), 'readiness': ref(output_path),
                      'actual_compiler_command_count': 2, 'coverage_complete': False}))


if __name__ == '__main__':
    main()
