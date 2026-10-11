"""Independent output reader; never imports or executes a selection/freeze producer."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, importlib.util, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
BASELINE = 'reports/full-coverage/checkpoint-27-selection.json'
BASELINE_SHA = 'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
BASE_MANIFEST = 'reports/full-coverage/checkpoint-27-manifest.json'
BASE_MANIFEST_SHA = '196700f9fd69a0a7610f4a2b3d6bad20cfcb34688faa53f5f2fb8b688c085044'
BASE_AUDIT = 'reports/full-coverage/lean-checkpoint-27/verification-original.json'
BASE_AUDIT_SHA = 'fdd431eea1137c48032d20cdb31270b8d76a4ca715f19715167a1ec67cff194f'
SELECTION = 'reports/full-coverage/checkpoint-28-selection.json'
CONTENT = 'book/coverage/checks/frozen27-input-content-bindings28-v1.json'
INVENTORY = 'book/coverage/inventory-after-correction60.json'
INVENTORY_SHA = '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
REGISTRY = 'book/coverage/material-corrections.json'
REGISTRY_SHA = '90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81'
SELECTOR = 'book/coverage/prepare_checkpoint28_selection_v4.py'
FREEZER = 'book/coverage/freeze_checkpoint28_v1.py'
HASHES = {}
RECHECK = {}

def path(n):
    assert type(n) is str and n, ('path type', n)
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == n, n
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink(), n
    return p

def sha(n, fresh=False):
    if not fresh and n in HASHES:
        return HASHES[n]
    p = path(n)
    assert p.is_file(), n
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    HASHES[n] = h.hexdigest()
    return HASHES[n]

def read(n):
    return json.loads(path(n).read_bytes())

def ref(n):
    return {'file': n, 'sha256': sha(n)}

def checked(r, track=True):
    assert type(r) is dict and set(r) == {'file', 'sha256'}, r
    assert re.fullmatch('[0-9a-f]{64}', r['sha256']) and sha(r['file']) == r['sha256'], r
    if track:
        RECHECK[r['file']] = r['sha256']
    return read(r['file'])

def add(target, n, h):
    assert type(h) is str and re.fullmatch('[0-9a-f]{64}', h), (n, h)
    assert n not in target or target[n] == h, ('conflicting hash', n)
    assert sha(n) == h, n
    target[n] = h

def exact(mapping):
    assert type(mapping) is dict
    for n, h in mapping.items():
        assert sha(n) == h, n

def zero(d):
    codes = [d[k] for k in ('actual_exit_code', 'exit_code', 'actual_runner_exit_code') if k in d]
    assert codes and all(type(v) is int and v == 0 for v in codes), codes

def native(d, command, cwd, status='passed', helper_map=None, aliases=None):
    zero(d)
    assert d.get('status') == status, d.get('status')
    commands = [d[k] for k in ('actual_command', 'command') if k in d]
    locations = [d[k] for k in ('actual_workdir', 'working_directory', 'workdir', 'cwd') if k in d]
    assert commands and all(type(v) is list and v == command for v in commands), commands
    assert locations and all(type(v) is str and v == cwd for v in locations), locations
    assert d['helper_sha256_before'] == d['helper_sha256_after'], 'changed native helpers'
    if helper_map is not None:
        assert d['helper_sha256_before'] == helper_map
    aliases = aliases or {}
    for n, h in d['helper_sha256_before'].items():
        if Path(n).is_absolute():
            r = aliases[n]
            assert r['sha256'] == h
            assert sha(r['file']) == h
        else:
            assert sha(n) == h
            RECHECK[n] = h
    log = d['log']
    if Path(log).is_absolute():
        r = aliases[log]
        assert r['sha256'] == d['log_sha256'] and sha(r['file']) == r['sha256']
    else:
        assert sha(log) == d['log_sha256']
        RECHECK[log] = d['log_sha256']

def typed_pointer(d, keys):
    for key in keys:
        d = d[key]
    assert type(d) is dict and set(d) == {'file', 'sha256'}
    return d

parser = argparse.ArgumentParser()
parser.add_argument('--selection-execution', required=True)
parser.add_argument('--freeze-execution')
parser.add_argument('--manifest')
parser.add_argument('--out', required=True)
args = parser.parse_args()
assert bool(args.freeze_execution) == bool(args.manifest)
OUT = Path(args.out)
assert OUT.is_absolute() and OUT.is_relative_to('/tmp') and not OUT.exists()
started = datetime.now(timezone.utc).isoformat()
for n, h in [(BASELINE, BASELINE_SHA), (BASE_MANIFEST, BASE_MANIFEST_SHA),
             (BASE_AUDIT, BASE_AUDIT_SHA), (INVENTORY, INVENTORY_SHA),
             ('book/coverage/inventory.json', INVENTORY_SHA), (REGISTRY, REGISTRY_SHA)]:
    assert sha(n) == h, n
    RECHECK[n] = h
selection = read(SELECTION)
RECHECK[SELECTION] = sha(SELECTION)
plan = checked({'file': selection['selection_plan'], 'sha256': selection['selection_plan_sha256']})
assert plan['status'] == 'exact_current60_owner28_and_eleven_sources_explicit_selection_plan'
assert selection['status'] == 'explicit_current60_source_matched_selection_requires_fresh_aggregate_audit'
assert selection['coverage_complete'] is False and selection['deliberate_baseline_source_revisions'] == {}
assert selection['proof_file_count'] == len(selection['proof_files']) == 1186 and selection['new_file_count'] == 11
assert selection['baseline_selection'] == BASELINE and selection['baseline_selection_sha256'] == BASELINE_SHA
assert selection['actual_passing_baseline_audit'] == BASE_AUDIT and selection['actual_passing_baseline_audit_sha256'] == BASE_AUDIT_SHA
assert selection['current_inventory'] == INVENTORY and selection['current_inventory_sha256'] == INVENTORY_SHA
assert plan['baseline_selection'] == {'file': BASELINE, 'sha256': BASELINE_SHA}
assert plan['baseline_manifest'] == {'file': BASE_MANIFEST, 'sha256': BASE_MANIFEST_SHA}
assert plan['baseline_audit'] == {'file': BASE_AUDIT, 'sha256': BASE_AUDIT_SHA}
assert plan['inventory'] == {'file': INVENTORY, 'sha256': INVENTORY_SHA}
helper_peer = checked(plan['independent_selection_helper_review'])
assert helper_peer['status'] == plan['expected_independent_selection_helper_review_status'] and helper_peer['errors'] == []
assert helper_peer['helper'] == ref(SELECTOR)
assert helper_peer['reviewed_helpers_sha256'] == plan['helpers_sha256']
exact(plan['helpers_sha256'])
selection_actual = read(args.selection_execution)
native(selection_actual, ['python3', SELECTOR, '--plan', selection['selection_plan'], '--plan-sha256', selection['selection_plan_sha256'], '--apply'], str(ROOT), helper_map=plan['helpers_sha256'])
RECHECK[args.selection_execution] = sha(args.selection_execution)
baseline, base_manifest, audit = read(BASELINE), read(BASE_MANIFEST), read(BASE_AUDIT)
assert len(baseline['proof_files']) == audit['proof_file_count'] == 1175 and audit['theorem_count'] == 9644 and audit['status'] == 'passed'
assert audit['proof_sha256'] == {n: r['sha256'] for n, r in baseline['proof_files'].items()}
for record in audit['checks']:
    zero(record)
assert base_manifest['status'] == 'formal_verification_passed_partial_coverage'
assert base_manifest['proof_files'] == baseline['proof_files'] and len(base_manifest['frozen_inputs_sha256']) == 48662
integration = checked(plan['integration_result'])
installation = checked(plan['actual_integration_execution'])
assert integration['applied'] is True and integration['coverage_complete'] is False
assert integration['status'] == 'four_exact_reviewed_owner28_candidate_bytes_integrated_pending_fresh_current60_global_integrity_and_aggregate28_audit'
assert integration['inventory_sha256'] == INVENTORY_SHA
binding_ref = {'file': integration['binding_manifest'], 'sha256': integration['binding_manifest_sha256']}
binding = checked(binding_ref)
assert binding['helper'] == integration['actual_helper']
native(installation, ['python3', binding['helper']['file'], '--binding', binding_ref['file'], '--binding-sha256', binding_ref['sha256'], '--apply'], str(ROOT), helper_map={binding['helper']['file']: binding['helper']['sha256']})
replacements = {r['destination']: r for r in integration['exact_replacements']}
assert set(replacements) == {'book/coverage/' + n + '.json' for n in ['core', 'foundations', 'applied', 'applied-promotions', 'modules']}
for n, r in replacements.items():
    checked(r['candidate'])
    assert sha(n) == r['candidate']['sha256']
    assert sha(r['original27_byte_copy']) == r['before_sha256'] == base_manifest['working_inputs_sha256'][n]
    RECHECK[n] = r['candidate']['sha256']
exact(binding['exact_current60_safelearning_assets_sha256'])
assert len(binding['exact_current60_safelearning_assets_sha256']) == 31
RECHECK.update(binding['exact_current60_safelearning_assets_sha256'])
expected = copy.deepcopy(baseline['proof_files'])
first_name = sorted(expected)[0]
first = expected[first_name]['evidence_sha256']
pairs, new_sources = [], {}
for batch in binding['canonical_pair_batches']:
    readiness = checked(batch['readiness'])
    actual = checked(batch['actual_execution'])
    assert readiness['status'] == batch['expected_readiness_status'] and readiness['errors'] == []
    assert readiness['source_count'] == batch['source_count'] and readiness['public_theorem_count'] == batch['public_theorem_count']
    assert readiness['actual_compiler_command_count'] == len(readiness['actual_paired_records']) == 2 * batch['source_count']
    native(actual, batch['expected_command'], str(ROOT), helper_map=batch['expected_helper_sha256'])
    for row in readiness['sources']:
        n = row['canonical_source']
        assert n not in new_sources and n not in expected
        new_sources[n] = row['original_tmp_source']['sha256']
        assert sha(n) == new_sources[n]
    pairs.extend(readiness['actual_paired_records'])
assert len(pairs) == 22 and len(new_sources) == 11
owners, seen = {}, set()
for owner, row in binding['owners'].items():
    offer = checked(row['reviewed_offer'])
    peer = checked(row['final_mapping_peer'])
    assert peer['status'] == row['expected_final_mapping_peer_status'] and peer['errors'] == []
    assert typed_pointer(offer, row['offer_candidate_pointer']) == row['candidate']
    assert typed_pointer(peer, row['peer_candidate_pointer']) == row['candidate']
    assert typed_pointer(peer, row['peer_actual_finalizer_pointer']) == row['actual_finalizer']
    assert replacements[row['destination']]['candidate'] == row['candidate']
    finalizer = checked(row['actual_finalizer'])
    native(finalizer, row['expected_actual_finalizer_command'], str(ROOT), status=row['expected_actual_finalizer_status'], helper_map=row['expected_actual_finalizer_helpers_sha256'], aliases=row.get('actual_finalizer_original_byte_aliases'))
    assert offer['inventory_sha256'] == INVENTORY_SHA
    exact(offer['source_sha256'])
    closure = offer['required_evidence_artifacts_sha256']
    assert closure
    for n, h in closure.items():
        add(first, n, h)
    assert set(offer['proof_files']) == set(row['new_sources'])
    for n, proof in offer['proof_files'].items():
        assert n not in seen and proof['sha256'] == new_sources[n]
        seen.add(n)
        pair = [p for p in pairs if p['source']['file'] == n]
        assert len(pair) == 2 and {p['kind'] for p in pair} == {'standalone', 'named'} and proof['actual_pair'] == pair
        value = proof['evidence_sha256']
        if type(value) is dict:
            evidence = dict(value)
        else:
            assert type(value) is str and value == next(p['actual_record']['sha256'] for p in pair if p['kind'] == 'standalone')
            evidence = {}
        for p in pair:
            record = checked(p['actual_record'])
            command = ['lake', 'env', 'lean', 'SafeLearning/' + Path(n).name] if p['kind'] == 'standalone' else ['lake', 'build', 'SafeLearning.' + Path(n).stem]
            # Paired native records use their original source/time/command fields.
            zero(record)
            assert record['status'] == 'passed'
            commands = [record[k] for k in ['actual_command', 'command'] if k in record]
            locations = [record[k] for k in ['actual_workdir', 'working_directory', 'workdir', 'cwd'] if k in record]
            assert commands and all(c == command for c in commands)
            assert locations and all(c == str(ROOT / 'verification/lean') for c in locations)
            assert record['source'] == n and record['source_sha256_before'] == record['source_sha256_after'] == new_sources[n]
            assert p['raw_log'] == {'file': record['log'], 'sha256': record['log_sha256']}
            for key in ['actual_record', 'raw_log', 'source_snapshot']:
                r = p[key]
                assert set(r) == {'file', 'sha256'} and closure.get(r['file']) == r['sha256'] and sha(r['file']) == r['sha256']
                if type(value) is dict:
                    assert evidence.get(r['file']) == r['sha256']
                else:
                    add(evidence, r['file'], r['sha256'])
            assert p['source_snapshot']['sha256'] == new_sources[n]
        chosen = copy.deepcopy(proof)
        if type(value) is str:
            chosen['original_native_offer_evidence_sha256'] = value
        chosen['evidence_sha256'] = evidence
        chosen['original_actual_zero_record'] = next(p['actual_record']['file'] for p in pair if p['kind'] == 'standalone')
        expected[n] = chosen
    for r in [row['reviewed_offer'], row['final_mapping_peer'], row['actual_finalizer'], row['candidate']]:
        add(first, r['file'], r['sha256'])
    owners[owner] = {'ledger': ref(row['destination']), 'candidate': row['candidate'], 'reviewed_offer': row['reviewed_offer'], 'mapping_peer': row['final_mapping_peer'], 'new_sources': len(offer['proof_files'])}
assert seen == set(new_sources)
assert selection['offers_sha256'] == {r['reviewed_offer']['file']: r['reviewed_offer']['sha256'] for r in binding['owners'].values()}
assert selection['independent_owner_mapping_peers'] == {o: r['final_mapping_peer'] for o, r in binding['owners'].items()}
global_data = checked(plan['global_integrity'])
global_actual = checked(plan['actual_global_integrity_execution'])
zero(global_actual)
assert global_data['integrity_status'] == 'passed' and global_data['errors'] == [] and global_data['mathematical_coverage_complete'] is False
assert global_data['inventory_sha256'] == INVENTORY_SHA
assert global_data['counts']['statuses']['exercise:complete_math'] == 523
assert global_data['counts']['statuses']['exercise:partial'] == 14 and global_data['counts']['statuses']['exercise:pending'] == 19
assert global_data['counts']['material_review_statuses'] == {'reviewed': 4621, 'pending': 8153}
assert selection['global_integrity'] == plan['global_integrity']['file'] and selection['global_integrity_sha256'] == plan['global_integrity']['sha256']
for d in global_data['domains']:
    assert d['ledger_sha256'] == replacements['book/coverage/' + d['domain'] + '.json']['candidate']['sha256']
extras = copy.deepcopy(baseline['extra_frozen_inputs'])
for n, row in plan['additional_frozen_inputs'].items():
    assert set(row) == {'sha256', 'scope'} and row['scope'] == 'immutable_audit_or_local_source_evidence'
    assert n not in extras or extras[n] == row
    assert sha(n) == row['sha256']
    extras[n] = row
assert selection['extra_frozen_inputs'] == extras
for r in [plan['global_integrity'], plan['integration_result'], plan['actual_integration_execution'], binding_ref, plan['independent_selection_helper_review']]:
    add(first, r['file'], r['sha256'])
add(first, selection['selection_plan'], selection['selection_plan_sha256'])
for n, h in plan['helpers_sha256'].items():
    add(first, n, h)
# Derive exact retention ordering and byte reuse without calling the retainer.
bound = {}
for n, row in expected.items():
    add(bound, n, row['sha256'])
    for p, h in row['evidence_sha256'].items():
        add(bound, p, h)
for n, row in extras.items():
    add(bound, n, row['sha256'])
by_hash = {}
for n, h in sorted(bound.items()):
    by_hash.setdefault(h, n)
rows, added, reused = [], {}, 0
for n, h in sorted(base_manifest['frozen_inputs_sha256'].items()):
    frozen = base_manifest['snapshot'] + '/' + n
    assert sha(frozen) == h, frozen
    retained = by_hash.get(h)
    if retained is None:
        retained = frozen
        by_hash[h] = retained
        add(bound, retained, h)
        add(first, retained, h)
        added[retained] = h
    else:
        reused += 1
    assert bound[retained] == h
    rows.append({'original_frozen_path': n, 'sha256': h, 'retained_input': retained})
content = read(CONTENT)
RECHECK[CONTENT] = sha(CONTENT)
assert content['status'] == 'all_original_frozen27_inputs_retained_by_exact_content_fingerprints'
assert content['baseline_selection'] == BASELINE and content['baseline_selection_sha256'] == BASELINE_SHA
assert content['baseline_manifest'] == BASE_MANIFEST and content['baseline_manifest_sha256'] == BASE_MANIFEST_SHA
assert content['baseline_actual_audit'] == {'file': BASE_AUDIT, 'sha256': BASE_AUDIT_SHA}
assert content['original_snapshot'] == base_manifest['snapshot']
assert content['original_input_count'] == len(rows) == len(content['input_bindings']) == 48662 and content['input_bindings'] == rows
assert content['retained_existing_content_rows'] == reused and content['new_unique_snapshot_aliases'] == added
assert content['new_unique_snapshot_alias_count'] == len(added)
assert content['new_unique_snapshot_alias_bytes'] == sum(path(n).stat().st_size for n in added)
assert content['historical_evidence_path_replacements'] == {}
for n in [BASELINE, BASE_MANIFEST, BASE_AUDIT, CONTENT]:
    add(first, n, sha(n))
assert selection['proof_files'] == expected, 'independently reconstructed entire selected rows differ'
assert selection['previous_frozen_input_content_binding'] == {'file': CONTENT, 'sha256': sha(CONTENT), 'original_inputs': 48662, 'new_snapshot_aliases': len(added)}
spec = importlib.util.spec_from_file_location('independent28_name_parser', path('book/coverage/lean_names.py'))
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
public, theorem, new_names = [], [], []
imports = 0
for n, row in expected.items():
    assert sha(n) == row['sha256']
    RECHECK[n] = row['sha256']
    text = path(n).read_text()
    decls = names.declarations(text)
    public.extend(d['name'] for d in decls)
    theorem.extend(d['name'] for d in decls if d['kind'] in {'theorem', 'lemma'})
    if n in seen:
        new_names.extend(d['name'] for d in decls if d['kind'] in {'theorem', 'lemma'})
    for line in names.without_comments(text).splitlines():
        if re.match(r'^\s*import\s', line):
            for dep in line.split()[1:]:
                if dep.startswith('SafeLearning.'):
                    assert 'verification/lean/' + dep.replace('.', '/') + '.lean' in expected
                    imports += 1
assert len(public) == len(set(public)) and len(theorem) == len(set(theorem)) == 9896 and len(new_names) == len(set(new_names)) == 252
for owner, row in binding['owners'].items():
    ledger = read(row['destination'])
    for claim in ledger['material_claims'] + [c for e in ledger['exercises'] for c in e['claims']]:
        assert set(claim['lean_declarations']) <= set(public), (owner, claim['id'])
frozen = {}
excluded = {'foundations': [], 'core': [], 'modules': [], 'applied': ['verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean', 'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean', 'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']}
if args.manifest:
    # Freeze must be an exact source/evidence snapshot, with only the three known
    # unreferenced Applied metadata rows pruned and an explicitly generated import file.
    manifest = read(args.manifest)
    RECHECK[args.manifest] = sha(args.manifest)
    assert manifest['status'] == 'frozen_inputs_not_yet_aggregate_verified' and manifest['coverage_complete'] is False
    assert manifest['selection'] == SELECTION and manifest['selection_sha256'] == sha(SELECTION) and manifest['proof_files'] == expected
    snapshot = manifest['snapshot']
    assert path(snapshot).is_dir() and snapshot.startswith('reports/full-coverage/')
    freeze_actual = read(args.freeze_execution)
    native(freeze_actual, ['python3', FREEZER, '--selection', SELECTION, '--snapshot', snapshot, '--selection-sha256', sha(SELECTION)], str(ROOT))
    RECHECK[args.freeze_execution] = sha(args.freeze_execution)
    working = manifest['working_inputs_sha256']
    frozen = manifest['frozen_inputs_sha256']
    exact(working)
    assert all(working.get(n) == h for n, h in bound.items())
    assert all(working.get(n) == h for n, h in binding['exact_current60_safelearning_assets_sha256'].items())
    excluded = {'foundations': [], 'core': [], 'modules': [], 'applied': [
        'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
        'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
        'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']}
    assert manifest['excluded_unreferenced_ledger_metadata'] == excluded
    generated = 'verification/lean/SafeLearning.lean'
    aggregator = '\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(expected)) + '\n'
    assert path(snapshot + '/' + generated).read_text() == aggregator
    assert frozen[generated] == hashlib.sha256(aggregator.encode()).hexdigest()
    projected = read('book/coverage/applied.json')
    projected['proof_files'] = {n: v for n, v in projected['proof_files'].items() if n in expected}
    if 'proof_sha256' in projected:
        projected['proof_sha256'] = {n: v for n, v in projected['proof_sha256'].items() if n in expected}
    payload = (json.dumps(projected, indent=2) + '\n').encode()
    pruned_sha = hashlib.sha256(payload).hexdigest()
    assert path(snapshot + '/book/coverage/applied.json').read_bytes() == payload
    assert set(frozen) == set(working) | {generated}
    for n, h in frozen.items():
        assert sha(snapshot + '/' + n) == h, n
        if n != generated:
            assert h == (pruned_sha if n == 'book/coverage/applied.json' else working[n]), n
    assert manifest['excluded_working_proof_files'] == sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / 'verification/lean/SafeLearning').glob('*.lean') if p.relative_to(ROOT).as_posix() not in expected)
for n, h in RECHECK.items():
    assert sha(n, fresh=True) == h, ('protected input changed during reader', n)
report = {
    'status': ('passed_independent_actual_checkpoint28_selection_and_freeze_output_review' if args.manifest else 'passed_independent_actual_checkpoint28_selection_output_review'),
    'errors': [], 'reviewer': '/root/applied_next', 'review_started_at_utc': started,
    'review_finished_at_utc': datetime.now(timezone.utc).isoformat(),
    'selection': ref(SELECTION), 'selection_plan': ref(selection['selection_plan']),
    'actual_selection_execution': ref(args.selection_execution), 'actual_freeze_execution': (ref(args.freeze_execution) if args.freeze_execution else None),
    'frozen_manifest': (ref(args.manifest) if args.manifest else None), 'content_map': ref(CONTENT),
    'baseline27_selection': ref(BASELINE), 'baseline27_manifest': ref(BASE_MANIFEST), 'baseline27_actual_audit': ref(BASE_AUDIT),
    'actual_owner28_integration': plan['actual_integration_execution'], 'integration_result': plan['integration_result'],
    'global_integrity': plan['global_integrity'], 'actual_global_integrity_execution': plan['actual_global_integrity_execution'],
    'owners': owners, 'proof_file_count': 1186, 'new_source_count': 11,
    'public_theorem_or_lemma_count': 9896, 'new_public_theorem_or_lemma_count': 252,
    'all_typed_public_name_count': len(public), 'actual_new_paired_commands': 22,
    'all_prior_selected_sources_retained_exact': 1175, 'all_prior_frozen_path_content_bindings_retained_exact': 48662,
    'independently_reconstructed_entire_selection_rows': True,
    'new_unique_snapshot_aliases': len(added), 'retained_existing_content_rows': reused,
    'frozen_input_count': len(frozen), 'current60_asset_count': 31,
    'safe_learning_imports_resolved': imports, 'all_claim_declarations_selected': True,
    'coverage_counts': {'complete': 523, 'partial': 14, 'pending': 19},
    'material_counts': {'reviewed': 4621, 'pending': 8153},
    'exact_applied_three_unreferenced_metadata_pruning': excluded['applied'],
    'all_frozen_input_bytes_rehashed': bool(args.manifest), 'distinct_files_hashed': len(HASHES),
    'coverage_complete': False, 'actual_aggregate_or_publication_claimed': False,
    'scope': 'Actual source selection mechanics; freeze included only when frozen_manifest is explicitly present. Native installation/selection/pairs are genuinely zero. Requires fresh checkpoint28 aggregate/kernel/all9896 axiom audit and actual publication.'}
OUT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': 'passed', 'report': str(OUT), 'sha256': hashlib.sha256(OUT.read_bytes()).hexdigest(), 'sources': 1186, 'new_sources': 11, 'theorems': 9896, 'old_frozen_content_bindings': 48662, 'frozen_inputs': len(frozen)}))
