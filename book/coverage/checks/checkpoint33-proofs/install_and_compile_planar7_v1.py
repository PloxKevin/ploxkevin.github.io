"""A separate immutable seventh phase after the original six compiler pairs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, subprocess, time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
PAIR6 = BASE / 'actual-reviewed33-canonical-paired-readiness-v1.json'
PEER = 'book/coverage/checks/checkpoint33-root/planar7-full-source-mathematical-review-v1.json'
PEER_SHA = 'b3e0305ecaf40d8fa621e7fb339f8b927d44a203c65cb86c5b410e640c293b3b'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def path(n):
    p = Path(n)
    return p if p.is_absolute() else ROOT / p

def ref(p):
    p = path(p) if isinstance(p, str) else p
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
            'sha256': sha(p), 'bytes': p.stat().st_size}

def checked(r):
    p = path(r['file'])
    assert p.is_file() and not p.is_symlink() and sha(p) == r['sha256'], str(p)
    if 'bytes' in r:
        assert p.stat().st_size == r['bytes']
    return p

def read(r):
    return json.loads(checked(r).read_bytes())

def new(p, data):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as out:
        out.write(data)
    p.chmod(0o444)

def write_json(p, data):
    new(p, (json.dumps(data, indent=2) + '\n').encode())

def main():
    helper = ref(Path(__file__))
    six_ref = ref(PAIR6)
    six = read(six_ref)
    assert six['status'] == 'passed_actual_reviewed33_canonical_standalone_and_named_pairs_unselected'
    assert six['errors'] == [] and six['source_count'] == 6 and six['public_theorem_count'] == 71
    assert six['actual_compiler_command_count'] == 12
    index_ref = ref('book/coverage/checks/recovery32/next-batch-source-qualification-index-v1.json')
    index = read(index_ref)
    original = index['outstanding_correspondence'][0]
    assert original['family'] == 'PlanarQuadratic7'
    assert original['source']['sha256'] == 'b168e4d1767af536d4a4e050070c13407cf12bc5f94d7e13607f3d5786525bec'
    peer_ref = {'file': PEER, 'sha256': PEER_SHA}
    peer = read(peer_ref)
    assert peer['status'] == 'passed_independent_Root_full_planar7_mathematical_prospective_correspondence'
    assert peer['errors'] == [] and peer['prospective_whole529_mathematically_approved'] is True
    assert peer['source']['sha256'] == original['source']['sha256']
    selection = read(six['baseline_selection'])
    protected = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(protected) == 1254
    originals = {r['file']: r['sha256'] for r in [helper, six_ref, index_ref, peer_ref, six['baseline_selection']]}
    for r in [original['source'], original['author_request'], *peer['entire3_selected_import_sources_read']]:
        checked(r)
        originals[r['file']] = r['sha256']
    for source in six['sources']:
        protected[source['canonical_source']] = source['original_tmp_source']['sha256']
    for pair in six['actual_paired_records']:
        assert pair['actual_exit_code'] == 0
        for k in ['actual_record', 'raw_log', 'source_snapshot']:
            checked(pair[k])
            originals[pair[k]['file']] = pair[k]['sha256']
    names_ref = ref('book/coverage/lean_names.py')
    originals[names_ref['file']] = names_ref['sha256']
    spec = importlib.util.spec_from_file_location('checkpoint33_phase7_names', checked(names_ref))
    names = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(names)
    selected_names = {d['name'] for n in protected for d in names.declarations(path(n).read_text())}
    source = checked(original['source'])
    text = source.read_text()
    declarations = names.declarations(text)
    assert len(declarations) == 10 and sum(d['kind'] in {'theorem', 'lemma'} for d in declarations) == 7
    assert not selected_names.intersection(d['name'] for d in declarations)
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(text))
    assert all(d['name'].startswith('SafeLearning.CompleteFoundationsPlanarQuadraticLevelSets32.') for d in declarations)
    assert {d['name'] for d in declarations if d['kind'] in {'theorem', 'lemma'}} == {d['lean_declaration'] for d in peer['per_theorem_assessment']}
    assert all(d['approved'] for d in peer['per_theorem_assessment'])
    native_closure = []
    for original_native in original['actual_source_and_axiom_natives']:
        native = read(original_native['record'])
        assert native['actual_exit_code'] == native['actual_runner_exit_code'] == 0
        assert native['source_sha256_before'] == native['source_sha256_after'] == native['source_snapshot_sha256']
        assert native['protection_errors'] == []
        if original_native['role'] == 'passed_source_v3':
            assert native['source_sha256_before'] == original['source']['sha256']
        originals[original_native['record']['file']] = original_native['record']['sha256']
        closure = {'role': original_native['role'], 'original_record': original_native['record']}
        for k, hk in [('source_snapshot', 'source_snapshot_sha256'), ('raw_log', 'raw_log_sha256')]:
            r = {'file': native[k], 'sha256': native[hk]}
            checked(r)
            originals[r['file']] = r['sha256']
            closure[k] = r
        native_closure.append(closure)
    name = 'CompleteFoundationsPlanarQuadraticLevelSets33'
    canonical_name = 'verification/lean/SafeLearning/' + name + '.lean'
    canonical = ROOT / canonical_name
    assert not canonical.exists()
    snapshot = BASE / 'source-snapshots' / canonical.name
    row = {'family': original['family'], 'canonical_source': canonical_name,
           'original_tmp_source': original['source'],
           'original_namespaces': ['SafeLearning.CompleteFoundationsPlanarQuadraticLevelSets32'],
           'public_declarations': declarations, 'public_theorem_count': 7, 'public_name_count': 10,
           'original_actual_source_and_axiom_natives': native_closure,
           'independent_source_peers': [peer_ref], 'original_author_request': original['author_request'],
           'conditionally_approved_whole_material': [original['target']],
           'exact_replacements': peer['exact_replacements'],
           'independent_narrow_wording_and_parser_peer': None,
           'whole_qualification_still_requires_exact_source_application_and_narrow_cumulative_parser': True,
           'additional_scope_limits': peer['hypotheses']}
    def guard():
        for n, h in {**protected, **originals}.items():
            assert sha(path(n)) == h, n
    guard()
    write_json(BASE / 'exact-reviewed-planar7-canonical33-plan-v1.json',
               {'status': 'separate_actual_planar7_canonical33_plan_after_original6',
                'compiler_recorder': helper, 'original_six_readiness': six_ref,
                'sources': [row], 'source_count': 1, 'public_theorem_count': 7, 'public_name_count': 10,
                'checked_original_evidence_sha256': originals,
                'coverage_complete': False, 'narrow_cumulative_parser_still_required_for_whole_promotion': True})
    new(canonical, source.read_bytes())
    new(snapshot, source.read_bytes())
    protected[canonical_name] = original['source']['sha256']
    snapshots = {canonical_name: ref(snapshot)}
    pairs = []
    for kind in ['standalone', 'named']:
        guard()
        command = ['lake', 'env', 'lean', 'SafeLearning/' + name + '.lean'] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + name]
        log = BASE / (name + '-' + kind + '-actual-v1.log')
        record_path = BASE / (name + '-' + kind + '-actual-v1.json')
        started = datetime.now(timezone.utc).isoformat()
        start = time.monotonic()
        before = sha(canonical)
        with log.open('xb') as raw:
            result = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=raw, stderr=subprocess.STDOUT, check=False)
        elapsed = time.monotonic() - start
        finished = datetime.now(timezone.utc).isoformat()
        log.chmod(0o444)
        record = {'status': 'passed' if result.returncode == 0 else 'failed', 'kind': kind,
                  'command': command, 'actual_command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
                  'exit_code': result.returncode, 'actual_exit_code': result.returncode,
                  'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
                  'source': canonical_name, 'source_sha256_before': before, 'source_sha256_after': sha(canonical),
                  'source_snapshot': ref(snapshot), 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                  'compiler_recorder': helper, 'compiler_recorder_sha256_after': sha(Path(__file__)),
                  'source_unchanged': before == sha(canonical), 'baseline_selection': six['baseline_selection'],
                  'immutable_actual_command_record_no_relabeling': True, 'coverage_complete': False}
        write_json(record_path, record)
        guard()
        assert result.returncode == 0, str(record_path)
        pairs.append({'kind': kind, 'source': ref(canonical), 'actual_record': ref(record_path),
                      'raw_log': ref(log), 'source_snapshot': ref(snapshot), 'actual_exit_code': result.returncode})
        print(json.dumps({'phase': 'Planar7', 'completed_actual_commands': len(pairs), 'kind': kind,
                          'actual_exit_code': result.returncode}), flush=True)
    report = {'status': 'passed_actual_reviewed33_planar7_canonical_standalone_and_named_pairs_unselected',
              'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(),
              'source_count': 1, 'public_theorem_count': 7, 'public_name_count': 10,
              'actual_compiler_command_count': 2, 'sources': [row], 'actual_paired_records': pairs,
              'source_snapshots': snapshots, 'compiler_recorder': helper,
              'original_six_readiness': six_ref,
              'plan': ref(BASE / 'exact-reviewed-planar7-canonical33-plan-v1.json'),
              'baseline_selection': six['baseline_selection'], 'selected32_source_and_public_name_protection_passed': True,
              'source_qualifiers_narrow_parser_owner_promotion_and_aggregate_still_separate': True,
              'prior_snapshot_tree_or_build_cache_copied': False, 'coverage_complete': False,
              'selection_aggregate_owner_or_publication_claimed': False}
    target = BASE / 'actual-reviewed33-planar7-canonical-paired-readiness-v1.json'
    write_json(target, report)
    print(json.dumps({'status': report['status'], 'readiness': ref(target), 'actual_commands': 2,
                      'public_theorems': 7, 'coverage_complete': False}), flush=True)

if __name__ == '__main__':
    main()
