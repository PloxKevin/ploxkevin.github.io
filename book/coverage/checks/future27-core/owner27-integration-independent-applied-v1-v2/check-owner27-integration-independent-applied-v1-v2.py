from pathlib import Path
import ast, copy, hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
OLD = ROOT / 'book/coverage/checks/root_integrate_owner27_candidates_v1.py'
NEW = ROOT / 'book/coverage/checks/root_integrate_owner27_candidates_v2.py'
OUT = Path('/tmp/owner27-integration-independent-applied-check-result-v2.json')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
def functions(p):
    tree = ast.parse(p.read_text())
    ns = {'Path': Path, 'ROOT': ROOT, 'hashlib': hashlib, 'json': json}
    exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n, ast.FunctionDef)], type_ignores=[]), str(p), 'exec'), ns)
    return ns, tree
old, oldtree = functions(OLD)
new, newtree = functions(NEW)
fixtures = []
def accept(name, action):
    action(); fixtures.append({'fixture': name, 'disposition': 'accepted'})
def reject(name, action):
    try: action()
    except (AssertionError, KeyError, TypeError, ValueError, FileNotFoundError):
        fixtures.append({'fixture': name, 'disposition': 'rejected'}); return
    raise AssertionError('unexpected acceptance: ' + name)
def asserts_using(tree, name):
    return [n for n in ast.walk(tree) if isinstance(n, ast.Assert) and name in {a.id for a in ast.walk(n.test) if isinstance(a, ast.Name)}]
def run_asserts(nodes, env):
    exec(compile(ast.Module(body=copy.deepcopy(nodes), type_ignores=[]), '<exact-extracted-guard>', 'exec'), env)

# Original guards are exercised exactly, preserving the requires-changes finding.
def old_peer(peer):
    nodes = [n for n in asserts_using(oldtree, 'peer') if "'passed'" in ast.unparse(n)]
    run_asserts(nodes, {'peer': peer})
old_peer({'status': 'not_passed'})
old_peer({'status': 'passed'})
original_findings = [
    'Original final-mapping guard accepts not_passed and accepts an absent errors field.',
    'Original Applied companion has no equality to an offer or peer promotion candidate.',
    'Original finalizer gate has no equality to the peer/offer finalizer or expected command/helper routing.'
]
def final_peer(peer, row):
    nodes = [n for n in asserts_using(newtree, 'peer') if 'expected_final_mapping_peer_status' in ast.unparse(n)]
    assert len(nodes) == 1
    run_asserts(nodes, {'peer': peer, 'row': row})
expected = 'passed_independent_fixture_mapping'
accept('explicit expected peer status and explicit errors', lambda: final_peer({'status': expected, 'errors': []}, {'expected_final_mapping_peer_status': expected}))
for label, peer in [('missing-errors', {'status': expected}), ('misleading-status', {'status': 'not_passed', 'errors': []}), ('reported-error', {'status': expected, 'errors': ['drift']})]:
    reject(label, lambda p=peer: final_peer(p, {'expected_final_mapping_peer_status': expected}))
accept('strict integer-zero aliases', lambda: new['zero']({'actual_exit_code': 0, 'exit_code': 0}))
for label, body in [('false-bool', {'actual_exit_code': False}), ('true-bool', {'actual_exit_code': True}), ('float-zero', {'actual_exit_code': 0.0}), ('missing-code', {}), ('conflicting-code', {'actual_exit_code': 0, 'exit_code': 1}), ('null-code', {'actual_exit_code': None})]:
    reject(label, lambda b=body: new['zero'](b))
accept('safe relative canonical path', lambda: new['safe']('book/coverage/inventory.json'))
for name in ['/tmp/absolute.json', '../outside.json', 'book/../outside.json', 'book//coverage/inventory.json', '']:
    reject('unsafe-path-' + repr(name), lambda n=name: new['safe'](n))

finalizer_nodes = [n for n in ast.walk(newtree) if isinstance(n, ast.Assert) and any(x in ast.unparse(n) for x in ['peer_actual_finalizer_pointer', 'expected_actual_finalizer_command', 'expected_actual_finalizer_helpers_sha256'])]
assert len(finalizer_nodes) == 3
fref = {'file': 'reports/full-coverage/genuine-fixture.json', 'sha256': 'a' * 64}
helper_map = {'book/coverage/checks/fixture.py': 'b' * 64}
native = {'actual_command': ['python3', 'book/coverage/checks/fixture.py', '--apply'], 'helper_sha256_before': helper_map}
row = {'peer_actual_finalizer_pointer': ['actual'], 'actual_finalizer': fref, 'expected_actual_finalizer_command': native['actual_command'], 'expected_actual_finalizer_helpers_sha256': helper_map}
def routing(peer, record, entry): run_asserts(finalizer_nodes, {'peer': peer, 'finalizer': record, 'row': entry, 'pointer': new['pointer']})
accept('finalizer exact peer and command/helper routing', lambda: routing({'actual': fref}, native, row))
reject('unrelated genuine-zero finalizer reference', lambda: routing({'actual': {**fref, 'sha256': 'c' * 64}}, native, row))
reject('wrong finalizer command', lambda: routing({'actual': fref}, {**native, 'actual_command': ['python3', 'unrelated.py']}, row))
reject('wrong finalizer helper map', lambda: routing({'actual': fref}, {**native, 'helper_sha256_before': {'other.py': 'd' * 64}}, row))

companion_nodes = [n for n in ast.walk(newtree) if isinstance(n, ast.Assert) and any(x in ast.unparse(n) for x in ['offer_typed_candidate_pointer', 'peer_typed_candidate_pointer'])]
assert len(companion_nodes) == 2
c = {'candidate': fref, 'offer_typed_candidate_pointer': ['promotions'], 'peer_typed_candidate_pointer': ['promotions']}
def companion(o, p): run_asserts(companion_nodes, {'offer': o, 'peer': p, 'c': c, 'pointer': new['pointer']})
accept('Applied companion exact offer and peer candidate', lambda: companion({'promotions': fref}, {'promotions': fref}))
reject('unreviewed companion digest', lambda: companion({'promotions': {**fref, 'sha256': 'e' * 64}}, {'promotions': fref}))
reject('unreviewed companion peer digest', lambda: companion({'promotions': fref}, {'promotions': {**fref, 'sha256': 'e' * 64}}))
reject('missing companion peer mapping', lambda: companion({'promotions': fref}, {}))
pair_nodes = [n for n in ast.walk(newtree) if isinstance(n, ast.Assert) and "{p['kind'] for p in original_pairs}" in ast.unparse(n)]
assert len(pair_nodes) == 1
accept('one standalone and one named', lambda: run_asserts(pair_nodes, {'original_pairs': [{'kind': 'standalone'}, {'kind': 'named'}]}))
reject('duplicate standalone is not pair', lambda: run_asserts(pair_nodes, {'original_pairs': [{'kind': 'standalone'}, {'kind': 'standalone'}]}))
reject('missing named is not pair', lambda: run_asserts(pair_nodes, {'original_pairs': [{'kind': 'standalone'}]}))

# Read every real native command; this does not execute the integrator or validator.
ready_ref = {'file': 'book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json', 'sha256': '74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'}
ready = new['checked'](ready_ref)
assert ready['source_count'] == 8 and ready['public_theorem_count'] == 141 and len(ready['actual_paired_records']) == 16
seen = set(); actual_records = []
for p in ready['actual_paired_records']:
    record = new['checked'](p['actual_record']); new['zero'](record)
    source = p['source']['file']; h = p['source']['sha256']; kind = p['kind']
    assert (source, kind) not in seen; seen.add((source, kind))
    expected_command = ['lake', 'env', 'lean', 'SafeLearning/' + Path(source).name] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + Path(source).stem]
    assert record['command'] == expected_command and record['actual_workdir'] == str(ROOT / 'verification/lean')
    assert record['source'] == source and record['source_sha256_before'] == record['source_sha256_after'] == h
    assert new['sha'](source) == h
    assert new['sha'](p['source_snapshot']['file']) == p['source_snapshot']['sha256'] == h
    assert p['raw_log'] == {'file': record['log'], 'sha256': record['log_sha256']} and new['sha'](record['log']) == record['log_sha256']
    actual_records.append({'kind': kind, 'native_record': p['actual_record'], 'command': record['command']})
assert seen == {(r['canonical_source'], kind) for r in ready['sources'] for kind in ['standalone', 'named']}
selection = read(ROOT / 'reports/full-coverage/checkpoint-26-selection.json')
assert len(selection['proof_files']) == 1167
for n, row in selection['proof_files'].items(): assert new['sha'](n) == row['sha256']
inventory = read(ROOT / 'book/coverage/inventory.json')
for n, h in inventory['source_sha256'].items(): assert new['sha'](n) == h
assert len(inventory['source_sha256']) == 29
assert new['sha']('book/coverage/inventory.json') == new['sha']('book/coverage/inventory-after-correction55.json') == '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'

# The mutation blocks and comprehensive prewrite validator are byte-exact ASTs.
old_tail = oldtree.body[next(i for i, n in enumerate(oldtree.body) if isinstance(n, ast.Assert) and 'offered == set(new_sources)' in ast.unparse(n)):]
new_tail = newtree.body[next(i for i, n in enumerate(newtree.body) if isinstance(n, ast.Assert) and 'offered == set(new_sources)' in ast.unparse(n)):]
assert ast.dump(ast.Module(body=old_tail, type_ignores=[]), include_attributes=False) == ast.dump(ast.Module(body=new_tail, type_ignores=[]), include_attributes=False)
assert not (ROOT / 'reports/full-coverage/owner26-originals-before-owner27-integration-v1').exists()
assert not (ROOT / 'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json').exists()
result = {'status': 'passed_read_only_owner27_integrator2_exact_guard_and_native_fixture_checker', 'errors': [], 'original_requires_changes_findings': original_findings, 'fixtures': fixtures, 'fixture_count': len(fixtures), 'real_canonical_sources': 8, 'real_native_commands': actual_records, 'baseline_protected_source_count': 1167, 'current_inventory': {'file': 'book/coverage/inventory.json', 'sha256': new['sha']('book/coverage/inventory.json')}, 'original_helper': {'file': str(OLD.relative_to(ROOT)), 'sha256': digest(OLD)}, 'helper': {'file': str(NEW.relative_to(ROOT)), 'sha256': digest(NEW)}, 'prewrite_validator_and_archive_copy_result_blocks_exact': True, 'producer_or_validator_executed': False, 'binding_manifest_reviewed': False}
with OUT.open('x') as f: f.write(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'fixtures': len(fixtures), 'native_commands': 16, 'result': str(OUT), 'sha256': digest(OUT)}))
