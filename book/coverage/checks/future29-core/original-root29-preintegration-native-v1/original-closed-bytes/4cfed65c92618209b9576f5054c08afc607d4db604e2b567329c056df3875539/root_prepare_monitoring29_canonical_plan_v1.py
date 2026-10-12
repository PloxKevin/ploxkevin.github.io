"""Prepare a separate actual compiler plan after the reviewed ten-file batch."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'book/coverage/checks/future29-core/monitoring29-canonical-plan-v1'
CONTEXT = Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
CONTEXT_SHA = '10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
RUNNER = 'book/coverage/checks/run_root29_reviewed_canonical_pairs_v1.py'
RUNNER_SHA = 'd1d4358d68e183ad3d4fee48735d2bd99572a5c640c8be5d9ea753abc61af141'
PAIR = 'book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json'
NATIVE = 'reports/full-coverage/current65-canonical-pairs10-application29-execution-v1.json'
REQUEST = 'book/coverage/checks/future29-core/monitoring-fixed-selector29-v1/core-monitoring-fixed-selector29-full-semantic-review-request-v1.json'
REQUEST_SHA = '298fa499667b537f2e95c0655f4854e4870303baeba756f36066b75f2f4bfff4'
PEER = 'book/coverage/checks/future29-applied/monitoring-fixed-selector29-full-independent-v1/monitoring-fixed-selector29-full-source-independent-applied29-peer-v1.json'
PEER_SHA = '72df0b38c651812d6d985810ed460f08ebd24434b02f029af8554a22422c4229'

def path(n):
    p = Path(n) if Path(n).is_absolute() else ROOT / n
    assert '..' not in p.parts and not p.is_symlink()
    assert p.resolve().is_relative_to(ROOT) or p == CONTEXT
    return p

def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n): return json.loads(path(n).read_bytes())
def ref(n): return {'file': str(n), 'sha256': sha(n)}
def checked(r):
    assert sha(r['file']) == r['sha256']
    return read(r['file'])

def write(p, d):
    assert p.resolve().is_relative_to(ROOT) and not p.exists()
    assert all(not q.is_symlink() for q in [p, *p.parents] if q.is_relative_to(ROOT))
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write((json.dumps(d, indent=2) + '\n').encode())

def main():
    assert not BASE.exists() and sha(CONTEXT) == CONTEXT_SHA and sha(RUNNER) == RUNNER_SHA
    assert sha(REQUEST) == REQUEST_SHA and sha(PEER) == PEER_SHA
    request, peer, pairs, native = [read(n) for n in [REQUEST, PEER, PAIR, NATIVE]]
    assert peer['errors'] == [] and peer['status'].startswith('passed_')
    assert peer['request'] == ref(REQUEST) and peer['proof_source'] == request['final_actual_source']
    assert all(r['approved'] and r['missing_clauses'] == [] for r in peer['components'])
    assert peer['whole_exercise21_or_node1141_approved'] is False
    assert pairs['status'] == 'passed_actual_reviewed29_canonical_standalone_and_named_pairs_unselected'
    assert pairs['errors'] == [] and pairs['source_count'] == 10 and pairs['public_theorem_count'] == 202
    assert pairs['actual_compiler_command_count'] == len(pairs['actual_paired_records']) == 20
    assert native['status'] == 'passed' and type(native['actual_exit_code']) is int and native['actual_exit_code'] == 0
    assert native['actual_workdir'] == str(ROOT)
    assert native['actual_command'] == ['python3', RUNNER, '--plan', 'book/coverage/checks/future29-core/current65-canonical-plan10-v1.json', '--plan-sha256', 'c52479b0decac7ad29160ec198e4c6ebce8c42948603939c55080ce71bbdb49b', '--apply']
    assert native['helper_sha256_before'] == native['helper_sha256_after'] == {RUNNER: RUNNER_SHA}
    assert sha(native['log']) == native['log_sha256']
    context = read(CONTEXT)
    protected = {**context['pins_sha256'], **context['held_current_source_sha256']}
    for n, h in protected.items(): assert sha(n) == h, n
    additions = {PAIR: sha(PAIR), NATIVE: sha(NATIVE), native['log']: native['log_sha256'], RUNNER: RUNNER_SHA, REQUEST: REQUEST_SHA, PEER: PEER_SHA}
    for r in pairs['sources']:
        additions[r['canonical_source']] = r['original_tmp_source']['sha256']
    for r in pairs['actual_paired_records']:
        assert type(r['actual_exit_code']) is int and r['actual_exit_code'] == 0
        actual = checked(r['actual_record'])
        assert type(actual['exit_code']) is int and actual['exit_code'] == 0
        assert actual['source_sha256_before'] == actual['source_sha256_after'] == r['source']['sha256']
        for k in ['actual_record', 'raw_log', 'source_snapshot']:
            additions[r[k]['file']] = r[k]['sha256']
    for n, h in additions.items():
        assert sha(n) == h and (n not in protected or protected[n] == h)
    source = request['final_actual_source']
    trial = request['original_actual_trial']
    checked(trial)
    assert sha(source['file']) == source['sha256']
    spec = importlib.util.spec_from_file_location('monitoring29_names', ROOT/'book/coverage/lean_names.py')
    names = importlib.util.module_from_spec(spec); spec.loader.exec_module(names)
    declarations = names.declarations(path(source['file']).read_text())
    assert declarations == request['source_level_public_declarations']
    count = sum(r['kind'] in ['theorem', 'lemma'] for r in declarations)
    assert count == 16 and len(declarations) == 29
    supplemental = dict(context)
    supplemental['pins_sha256'] = {**context['pins_sha256'], **additions}
    supplemental['original_source65_context'] = {'file': str(CONTEXT), 'sha256': CONTEXT_SHA}
    supplemental['prepared_at_utc'] = datetime.now(timezone.utc).isoformat()
    supplemental['scope'] = 'Current65 owner28 plus ten genuinely compiled unselected canonical sources and their twenty actual compiler records. This separate context authorizes one new compiler pair and changes no coverage or owners.'
    context_target = BASE/'supplemental-current65-context-v1.json'
    write(context_target, supplemental)
    row = {'owner': 'core', 'canonical_source': 'verification/lean/SafeLearning/CompleteCoreMonitoringFixedSelector29.lean',
           'original_tmp_source': source, 'original_actual_tmp_trial': trial,
           'independent_source_peers': [ref(PEER)], 'public_declarations': declarations,
           'public_theorem_count': count, 'original_review_time_and_TMP_command_cwd_status_retained': True,
           'fresh_canonical_records_pending': True}
    plan = {'status': 'exact_reviewed_new_canonical_pair_plan29_only', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
            'helper': ref(Path(__file__).relative_to(ROOT).as_posix()),
            'context': ref(context_target.relative_to(ROOT).as_posix()),
            'source_count': 1, 'public_theorem_count': count, 'public_name_count': len(declarations),
            'sources': [row], 'original_scope_plans': [ref(REQUEST)],
            'result_directory': 'book/coverage/checks/future29-core/current65-monitoring29-canonical-pair-v1',
            'coverage_complete': False, 'canonical_owner_selection_aggregate_or_publication_claimed': False}
    target = BASE/'monitoring29-canonical-plan-v1.json'; write(target, plan)
    for n, h in {**protected, **additions}.items(): assert sha(n) == h
    print(json.dumps({'status': plan['status'], 'plan': ref(target.relative_to(ROOT).as_posix()), 'sources': 1, 'public_names': 29, 'theorem_lemma_count': 16}))

if __name__ == '__main__': main()
