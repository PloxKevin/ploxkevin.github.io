"""Preflight or integrate five exact independently reviewed Source79 owner30 bytes.

This helper never compiles Lean or infers mathematical scope. It requires the
real Root45/90 paired records, final candidate mapping peers, and its own code
peer. Default mode writes only a fresh isolated integrity report. --apply first
preserves the five raw owner29 originals, then installs exact candidate bytes.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, re, sys, tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_integrate_owner30_candidates_v1.py'
INVENTORY_SHA = '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
SELECTION = 'reports/full-coverage/checkpoint-29-selection.json'
SELECTION_SHA = 'ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9'
PAIR_HELPER = 'book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py'
PAIR_HELPER_SHA = 'ec15d8df2c473174489cc412868db434e483dafc862d649334edf2d3512c4e2c'
PRIMARY = 'reports/full-coverage/current79-canonical-pairs45-application30-execution-v1.json'
PRIMARY_SHA = '8e3e384891e52794a493d078350abe282c8d215ff7f883eae6a3861c4eda77ee'
READINESS = 'book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json'
READINESS_SHA = '4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e'
PLAN = 'book/coverage/checks/future30-core/current79-canonical-plan45-v2.json'
PLAN_SHA = '4a2c2ab8e877d098f243562adc2112c116aa93062b40757c2d5e0cd57f90b09d'
OLD = {
    'core': 'a3db11195cef10593b1e5fc21cf6b6b5a037f106dde09d247efc96277dd249b6',
    'foundations': '67889e85ad190d150ec888b803cfcc4d2c80dc48aa096d1969ddfbf90cda5f07',
    'applied': '75c51c798ec0edf7fada80387e078d5fc6d383bcc76edb203fd9f30df4c52d1d',
    'modules': '13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d',
    'applied-promotions': '03d4343c000b1954a6cb6e0a2e3061ad2b5a585db906a67bcec8122421874b53',
}
EXPECTED = {'core': (1, 58), 'foundations': (27, 370), 'applied': (2, 34), 'modules': (15, 504)}
ARCHIVE = 'reports/full-coverage/owner29-originals-before-owner30-integration-v1'
RESULT = 'reports/full-coverage/owner30-reviewed-candidate-integration-v1.json'


def safe(n, require_file=True):
    assert type(n) is str and n and '\0' not in n and '\n' not in n and '\r' not in n
    p = Path(n)
    assert not p.is_absolute() and p.as_posix() == n and '..' not in p.parts
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT.resolve()) and not p.is_symlink()
    for q in [p, *p.parents]:
        if q.is_relative_to(ROOT):
            assert not q.is_symlink()
            if q != p and q.exists():
                assert q.is_dir()
    if require_file:
        assert p.is_file()
    return p


def sha(n):
    return hashlib.sha256(safe(n).read_bytes()).hexdigest()


def read(n):
    return json.loads(safe(n).read_bytes())


def checked(r, parse=True):
    assert type(r) is dict and {'file', 'sha256'} <= set(r) <= {'file', 'sha256', 'bytes'}
    assert type(r['sha256']) is str and re.fullmatch('[0-9a-f]{64}', r['sha256'])
    p = safe(r['file'])
    assert sha(r['file']) == r['sha256'], r['file']
    if 'bytes' in r:
        assert type(r['bytes']) is int and r['bytes'] == p.stat().st_size
    return read(r['file']) if parse else p


def pointer(d, keys):
    assert type(keys) is list and keys
    for k in keys:
        assert type(k) in (str, int)
        d = d[k]
    return d


def zero(d):
    codes = [d[k] for k in ('actual_exit_code', 'exit_code', 'actual_runner_exit_code') if k in d]
    assert codes and all(type(c) is int and c == 0 for c in codes)
    assert d.get('protection_errors', []) == []


def exact(table):
    assert type(table) is dict
    for n, h in table.items():
        assert type(h) is str and re.fullmatch('[0-9a-f]{64}', h) and sha(n) == h, n


def new(n, data):
    p = safe(n, False)
    assert not p.exists() and not p.is_symlink()
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write(data)


def native_actual(r, specification, aliases, immutable):
    d = checked(r)
    zero(d)
    assert d['status'] == specification['status']
    commands = [d[k] for k in ('actual_command', 'command') if k in d]
    locations = [d[k] for k in ('actual_workdir', 'working_directory', 'workdir', 'cwd') if k in d]
    assert commands and all(c == specification['command'] for c in commands)
    assert locations and all(n == specification['workdir'] for n in locations)
    assert d['helper_sha256_before'] == d['helper_sha256_after'] == specification['helpers_sha256']
    lf = specification['log_fields']
    assert type(lf) is list and len(lf) == 2
    originals = {**specification['helpers_sha256'], d[lf[0]]: d[lf[1]]}
    assert set(aliases) == {n for n in originals if Path(n).is_absolute()}
    for n, h in originals.items():
        if Path(n).is_absolute():
            p = Path(n)
            assert p.is_relative_to('/tmp') and '..' not in p.parts and p.as_posix() == n
            a = aliases[n]
            assert a['sha256'] == h
            checked(a, False)
            immutable[a['file']] = a['sha256']
        else:
            assert sha(n) == h
            immutable[n] = h
    immutable[r['file']] = r['sha256']
    return d


def proof_hash(value):
    return value['sha256'] if type(value) is dict else value


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--binding', required=True)
    ap.add_argument('--binding-sha256', required=True)
    ap.add_argument('--preflight-output', required=True)
    ap.add_argument('--apply', action='store_true')
    args = ap.parse_args()
    assert Path(__file__).resolve() == ROOT / SELF
    binding_ref = {'file': args.binding, 'sha256': args.binding_sha256}
    binding = checked(binding_ref)
    assert binding['status'] == 'four_final_Source79_owner30_domains_and_applied_promotions_actual90_and_mapping_peers_bound_for_Root'
    helper = {'file': SELF, 'sha256': sha(SELF)}
    assert binding['helper'] == helper
    code_peer = checked(binding['independent_helper_review'])
    assert code_peer['status'] == binding['expected_independent_helper_review_status']
    assert code_peer['errors'] == [] and code_peer['helper'] == helper and code_peer['full_code_read'] is True
    immutable = {SELF: helper['sha256'], args.binding: args.binding_sha256,
                 binding['independent_helper_review']['file']: binding['independent_helper_review']['sha256']}
    native_actual(binding['helper_review_actual_native'], binding['helper_review_native_specification'],
                  binding['helper_review_original_TMP_aliases'], immutable)
    assert pointer(code_peer, binding['helper_review_native_pointer']) == binding['helper_review_actual_native']
    assert binding['inventory'] == {'file': 'book/coverage/inventory-after-correction79.json', 'sha256': INVENTORY_SHA}
    assert sha('book/coverage/inventory.json') == sha(binding['inventory']['file']) == INVENTORY_SHA
    inventory = checked(binding['inventory'])
    assert inventory['counts']['exercises'] == 556 and inventory['counts']['material_source_units'] == 12774
    assert binding['baseline29_selection'] == {'file': SELECTION, 'sha256': SELECTION_SHA}
    old_selection = checked(binding['baseline29_selection'])
    assert len(old_selection['proof_files']) == 1197
    protected = {n: r['sha256'] for n, r in old_selection['proof_files'].items()}
    assets = binding['exact_current79_safelearning_assets_sha256']
    assert len(assets) == 31 and sum(n.endswith('.html') for n in assets) == 29
    assert inventory['source_sha256'] == {n: h for n, h in assets.items() if n.endswith('.html')}
    protected.update(assets)
    for n in ['book/coverage/inventory.json', binding['inventory']['file'],
              'book/coverage/material-corrections.json', SELECTION, 'book/coverage/validate.py', 'book/coverage/lean_names.py']:
        protected[n] = sha(n)
    assert len(read('book/coverage/material-corrections.json')['corrections']) == 79
    assert binding['canonical_readiness'] == {'file': READINESS, 'sha256': READINESS_SHA}
    assert binding['canonical_actual_execution'] == {'file': PRIMARY, 'sha256': PRIMARY_SHA}
    ready = checked(binding['canonical_readiness'])
    actual = checked(binding['canonical_actual_execution'])
    zero(actual)
    assert actual['status'] == 'passed'
    assert actual['actual_command'] == ['python3', PAIR_HELPER, '--plan', PLAN, '--plan-sha256', PLAN_SHA, '--apply']
    assert actual['actual_workdir'] == str(ROOT)
    assert actual['helper_sha256_before'] == actual['helper_sha256_after'] == {PAIR_HELPER: PAIR_HELPER_SHA}
    assert actual['selection29_before'] == actual['selection29_after'] == binding['baseline29_selection']
    checked({'file': actual['log'], 'sha256': actual['log_sha256']}, False)
    assert sha(PAIR_HELPER) == PAIR_HELPER_SHA and sha(PLAN) == PLAN_SHA
    immutable.update({READINESS: READINESS_SHA, PRIMARY: PRIMARY_SHA, actual['log']: actual['log_sha256'], PAIR_HELPER: PAIR_HELPER_SHA, PLAN: PLAN_SHA})
    assert ready['status'] == 'passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected' and ready['errors'] == []
    assert ready['source_count'] == len(ready['sources']) == 45
    assert ready['public_theorem_count'] == 966 and ready['actual_compiler_command_count'] == len(ready['actual_paired_records']) == 90
    sources = {r['canonical_source']: r for r in ready['sources']}
    assert len(sources) == 45 and not set(sources) & set(protected)
    assert {o: sum(r['owner'] == o for r in ready['sources']) for o in EXPECTED} == {o: v[0] for o, v in EXPECTED.items()}
    assert {o: sum(r['public_theorem_count'] for r in ready['sources'] if r['owner'] == o) for o in EXPECTED} == {o: v[1] for o, v in EXPECTED.items()}
    for n, row in sources.items():
        assert Path(n).parent == Path('verification/lean/SafeLearning') and Path(n).suffix == '.lean'
        protected[n] = row['original_tmp_source']['sha256']
    assert len({n for n in protected if n.startswith('verification/lean/SafeLearning/')}) == 1242
    pairs = ready['actual_paired_records']
    for p in pairs:
        n = p['source']['file']; h = p['source']['sha256']; stem = Path(n).stem
        assert sources[n]['original_tmp_source']['sha256'] == h and type(p['actual_exit_code']) is int and p['actual_exit_code'] == 0
        d = checked(p['actual_record']); zero(d)
        assert d['status'] == 'passed' and p['kind'] in {'standalone', 'named'}
        expected = ['lake', 'env', 'lean', 'SafeLearning/' + stem + '.lean'] if p['kind'] == 'standalone' else ['lake', 'build', 'SafeLearning.' + stem]
        assert d['command'] == expected and d['actual_workdir'] == str(ROOT / 'verification/lean')
        assert d['source'] == n and d['source_sha256_before'] == d['source_sha256_after'] == h
        assert p['raw_log'] == {'file': d['log'], 'sha256': d['log_sha256']} and p['source_snapshot']['sha256'] == h
        for k in ['actual_record', 'raw_log', 'source_snapshot']:
            checked(p[k], False); immutable[p[k]['file']] = p[k]['sha256']
    assert set(binding['owners']) == set(EXPECTED)
    replacements = []; offered = set(); candidates = {}
    for owner, (new_count, theorem_count) in EXPECTED.items():
        spec = binding['owners'][owner]; dest = 'book/coverage/' + owner + '.json'
        assert spec['destination'] == dest and spec['installed29_sha256'] == OLD[owner] and sha(dest) == OLD[owner]
        candidate = checked(spec['candidate']); offer = checked(spec['reviewed_offer']); peer = checked(spec['final_mapping_peer'])
        assert peer['status'] == spec['expected_final_mapping_peer_status'] and peer['errors'] == []
        assert pointer(peer, spec['peer_candidate_pointer']) == pointer(offer, spec['offer_candidate_pointer']) == spec['candidate']
        for keys in spec['peer_approved_mapping_pointers']:
            assert pointer(peer, keys) is True
        assert spec['peer_approved_mapping_pointers']
        assert pointer(peer, spec['peer_actual_native_pointer']) == spec['actual_mapping_native']
        native_actual(spec['actual_mapping_native'], spec['mapping_native_specification'], spec['mapping_original_TMP_aliases'], immutable)
        assert pointer(offer, spec['offer_inventory_pointer'])['sha256'] == INVENTORY_SHA
        closure = pointer(offer, spec['offer_evidence_sha256_pointer']); assert closure
        exact(closure)
        for n, h in closure.items():
            assert n not in immutable or immutable[n] == h
            immutable[n] = h
        for r in [spec['candidate'], spec['reviewed_offer'], spec['final_mapping_peer']]:
            immutable[r['file']] = r['sha256']
        for r in spec['additional_exact_original_evidence']:
            checked(r, False); immutable[r['file']] = r['sha256']
        old = read(dest); assert candidate['scope_pages'] == old['scope_pages']
        for n, h in candidate['source_sha256'].items():
            assert sha(n) == h
            assert h == (assets[n] if n.startswith('SafeLearning/') else old['source_sha256'][n])
        proof_rows = pointer(offer, spec['offer_new_proof_rows_pointer'])
        assert len(proof_rows) == new_count and set(proof_rows) == set(spec['new_sources'])
        op = old['proof_files']; cp = candidate['proof_files']
        assert type(op) is type(cp) and set(cp) == set(op) | set(proof_rows)
        if type(op) is dict:
            assert all(cp[n] == value for n, value in op.items())
        else:
            assert cp[:len(op)] == op and len(cp) == len(op) + new_count
        if 'proof_sha256' in old:
            assert all(candidate['proof_sha256'][n] == h for n, h in old['proof_sha256'].items())
        total = 0
        for n, meta in proof_rows.items():
            assert n in sources and n not in offered and sources[n]['owner'] == owner
            offered.add(n); h = sources[n]['original_tmp_source']['sha256']; assert meta['sha256'] == h
            expected_names = [d['name'] for d in sources[n]['public_declarations'] if d['kind'] in {'theorem', 'lemma'}]
            assert meta['public_theorem_names'] == meta['mapped_named_declarations'] == expected_names
            assert meta['theorem_count'] == len(expected_names) == len(set(expected_names)); total += len(expected_names)
            pp = [p for p in pairs if p['source']['file'] == n]
            assert len(pp) == 2 and {p['kind'] for p in pp} == {'standalone', 'named'} and meta['actual_pair'] == pp
            expected_evidence = {p[k]['file']: p[k]['sha256'] for p in pp for k in ['actual_record', 'raw_log', 'source_snapshot']}
            assert type(meta['evidence_sha256']) is dict and all(meta['evidence_sha256'].get(n) == h for n, h in expected_evidence.items())
            exact(meta['evidence_sha256'])
            assert all(closure.get(n) == h for n, h in expected_evidence.items())
            if type(cp) is dict:
                assert proof_hash(cp[n]) == h
            else:
                assert candidate['proof_sha256'][n] == h
        assert total == theorem_count
        candidates[owner] = candidate
        replacements.append({'destination': dest, 'before_sha256': OLD[owner], 'candidate': spec['candidate']})
        companion = spec['companion_candidates']; assert len(companion) == (1 if owner == 'applied' else 0)
        for c in companion:
            assert c['destination'] == 'book/coverage/applied-promotions.json' and sha(c['destination']) == OLD['applied-promotions']
            checked(c['candidate'])
            assert pointer(offer, c['offer_candidate_pointer']) == pointer(peer, c['peer_candidate_pointer']) == c['candidate']
            immutable[c['candidate']['file']] = c['candidate']['sha256']
            replacements.append({'destination': c['destination'], 'before_sha256': OLD['applied-promotions'], 'candidate': c['candidate']})
    assert offered == set(sources) and len(replacements) == 5
    for r in binding['additional_immutable_inputs']:
        checked(r, False); immutable[r['file']] = r['sha256']
    assert not set(immutable) & {r['destination'] for r in replacements}
    assert not safe(ARCHIVE, False).exists() and not safe(RESULT, False).exists()
    assert args.preflight_output.startswith('reports/full-coverage/') and args.preflight_output.endswith('.json')
    assert args.preflight_output not in protected and args.preflight_output not in immutable
    assert not safe(args.preflight_output, False).exists()
    def guard():
        exact(protected); exact(immutable); assert sha(SELF) == helper['sha256']
    guard()
    with tempfile.TemporaryDirectory(prefix='root-owner30-actual-candidates-preflight-') as tmp:
        ctx = Path(tmp); (ctx / 'book/coverage').mkdir(parents=True); (ctx / 'verification').mkdir()
        (ctx / 'SafeLearning').symlink_to(ROOT / 'SafeLearning', target_is_directory=True)
        (ctx / 'verification/lean').symlink_to(ROOT / 'verification/lean', target_is_directory=True)
        (ctx / 'book/coverage/inventory.json').symlink_to(safe('book/coverage/inventory.json'))
        for r in replacements:
            (ctx / r['destination']).symlink_to(safe(r['candidate']['file']))
        sys.path.insert(0, str(ROOT / 'book/coverage'))
        s = importlib.util.spec_from_file_location('isolated_actual_owner30_integrity', safe('book/coverage/validate.py'))
        v = importlib.util.module_from_spec(s); s.loader.exec_module(v); v.ROOT = ctx
        report = v.validate()
    guard()
    assert report['integrity_status'] == 'passed' and report['errors'] == []
    assert report['mathematical_coverage_complete'] is False
    assert report['counts']['exercises'] == 556 and report['counts']['material_source_units'] == 12774
    if binding.get('expected_isolated_preflight_counts') is not None:
        assert report['counts'] == binding['expected_isolated_preflight_counts']
    new(args.preflight_output, (json.dumps(report, indent=2, ensure_ascii=False) + '\n').encode())
    guard()
    if not args.apply:
        print(json.dumps({'status': 'passed_actual_isolated_Source79_owner30_candidate_preflight_no_live_owner_writes',
                          'counts': report['counts'], 'preflight': {'file': args.preflight_output, 'sha256': sha(args.preflight_output)},
                          'candidate_count': 5, 'new_sources': 45, 'new_theorems': 966, 'coverage_complete': False})); return
    for r in replacements:
        assert sha(r['destination']) == r['before_sha256']
    for r in replacements:
        archive = ARCHIVE + '/' + Path(r['destination']).name
        new(archive, safe(r['destination']).read_bytes())
        assert sha(archive) == r['before_sha256']; r['original29_byte_copy'] = {'file': archive, 'sha256': r['before_sha256']}
    guard()
    for r in replacements:
        assert sha(r['destination']) == r['before_sha256']
        with safe(r['destination']).open('wb') as f:
            f.write(safe(r['candidate']['file']).read_bytes())
        assert sha(r['destination']) == r['candidate']['sha256']
    guard()
    assert all(sha(r['destination']) == r['candidate']['sha256'] for r in replacements)
    result = {'status': 'five_exact_reviewed_Source79_owner30_candidates_integrated_pending_separate_fresh_global_and_aggregate_receipts',
              'applied': True, 'installed_at_utc': datetime.now(timezone.utc).isoformat(), 'actual_helper': helper,
              'binding': binding_ref, 'inventory_sha256': INVENTORY_SHA, 'baseline29_selection': binding['baseline29_selection'],
              'actual_root45_readiness': binding['canonical_readiness'], 'actual_root90_primary_execution': binding['canonical_actual_execution'],
              'exact_replacements': replacements, 'protected_actual_proof_source_count': 1242, 'new_canonical_source_count': 45,
              'new_public_theorem_count': 966, 'exact_current79_asset_count': 31,
              'actual_isolated_preflight': {'file': args.preflight_output, 'sha256': sha(args.preflight_output)},
              'isolated_candidate_counts': report['counts'], 'coverage_complete': False,
              'kernel_axiom_aggregate_selection_freeze_or_publication_success_claimed_by_this_helper': False,
              'old_snapshot_or_lake_tree_copied': False}
    new(RESULT, (json.dumps(result, indent=2, ensure_ascii=False) + '\n').encode())
    print(json.dumps({'status': result['status'], 'owners': 5, 'new_sources': 45,
                      'result': {'file': RESULT, 'sha256': sha(RESULT)}, 'counts': report['counts'], 'coverage_complete': False}))


if __name__ == '__main__':
    main()
