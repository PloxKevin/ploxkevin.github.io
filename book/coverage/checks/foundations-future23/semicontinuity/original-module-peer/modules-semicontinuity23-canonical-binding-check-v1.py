"""Add genuine canonical-pair bindings without retiming the TMP semantic peer."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re
R = Path('/home/oxrexkevin/SafetyBased')
B = 'book/coverage/checks/foundations-future23/semicontinuity'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
J = lambda p: json.loads(Path(p).read_text())
REF = lambda p: {'file': str(p.relative_to(R)) if p.is_relative_to(R) else str(p), 'sha256': H(p)}
OUT = Path('/tmp/foundations-semicontinuity-two-literals-canonical-source-independent-modules-binding23-v1.json')
assert not OUT.exists()
req_path = R / B / 'basics1202-1237-canonical-paired-source-readiness-v1.json'
assert H(req_path) == 'e6285f7e4651589345bec4829bdadd7c06bd14c26d74a14669b7945470464fad'
req = J(req_path)
old_path = Path('/tmp/foundations-semicontinuity-two-literals-independent-modules-source-review23-v1.json')
assert H(old_path) == '1d79324bc7375ff026b06e64c67931945aecff3a39b4c29d79dd21e4a74a0ac5'
old = J(old_path)
source = R / req['canonical_source']['file']
assert H(source) == req['canonical_source']['sha256'] == '280be25369c9cc9b3336d87ada8e5cf4d899cd454da1a4cabcf33725cb612b14'
assert source.read_bytes() == Path('/tmp/foundations-semicontinuity23-trial2.lean').read_bytes()
assert source.read_text() == old['entire_new_TMP_source_body_read']
assert len(re.findall(r'^theorem\s+', source.read_text(), re.M)) == req['public_theorem_count'] == 10
for original, alias in req['all_original_TMP_byte_copies'].items():
    assert H(Path(original)) == H(R / alias['file']) == alias['sha256']
original_request = J(R / req['original_TMP_request']['file'])
assert original_request == req['entire_original_TMP_request_body_and_created_time']
assert H(R / req['original_TMP_request']['file']) == old['original_review_request']['sha256']
inv48 = R / 'book/coverage/inventory-after-correction48.json'
assert H(inv48) == old['inventory_sha256']
old_units = {u['key']: u for u in J(inv48)['material_source_units']}
current_inv = R / 'book/coverage/inventory.json'
current = J(current_inv)
current_units = {u['key']: u for u in current['material_source_units']}
for u in old['material_units']:
    assert u['entire_inventory_record'] == old_units[u['source_unit_key']] == current_units[u['source_unit_key']]
    assert u['whole_unit_approved'] and u['material_status'] == 'proved' and u['missing_clauses'] == []
assert {u['source_unit_key'] for u in old['material_units']} == {'primer-basics.html::node-1202', 'primer-basics.html::node-1237'}
parent = old['full_parent_exercise_record_read']
assert parent == next(e for e in current['exercises'] if e['key'] == parent['key'])
assert H(R / old['source']) == old['source_sha256']
snapshot_ref = req['canonical_source_snapshot']
assert H(R / snapshot_ref['file']) == snapshot_ref['sha256'] == H(source)
pairs = []
for ref in req['actual_canonical_pair']:
    record_path = R / ref['file']
    assert H(record_path) == ref['sha256']
    a = J(record_path)
    assert a['actual_exit_code'] == ref['actual_exit_code'] == 0
    assert a['source'] == req['canonical_source']['file']
    assert a['source_sha256_before'] == a['source_sha256_after'] == H(source)
    assert H(R / a['preserved_source']) == a['preserved_source_sha256'] == H(source)
    assert H(R / a['log']) == a['log_sha256'] == ref['raw_log']['sha256']
    assert a['log'] == ref['raw_log']['file']
    assert a['actual_pair_helper'] == req['actual_helper']['file']
    assert a['actual_pair_helper_sha256'] == req['actual_helper']['sha256']
    pairs.append({'actual_record': ref, 'entire_original_actual_record': a, 'raw_log': ref['raw_log'],
                  'source_snapshot': {'file': a['preserved_source'], 'sha256': a['preserved_source_sha256']}})
assert [p['entire_original_actual_record']['command'] for p in pairs] == [
    ['lake', 'env', 'lean', 'SafeLearning/CompleteFoundationsSemicontinuity23.lean'],
    ['lake', 'build', 'SafeLearning.CompleteFoundationsSemicontinuity23']]
assert (R / pairs[0]['raw_log']['file']).read_text().count('warning:') == 7
assert (R / pairs[1]['raw_log']['file']).read_text().count('warning:') == 7
helper = R / req['actual_helper']['file']
execution = R / B / 'canonical-pair-helper-actual-execution-v1.json'
ex = J(execution)
assert ex['status'] == 'passed' and ex['actual_exit_code'] == 0
assert H(helper) == req['actual_helper']['sha256'] == ex['helper_sha256_before'] == ex['helper_sha256_after']
assert H(R / ex['raw_log']) == ex['raw_log_sha256']
manifest_path = R / 'reports/full-coverage/checkpoint-22-manifest.json'
manifest = J(manifest_path)
assert H(manifest_path) == old['protected_selected22']['manifest']['sha256']
for n, d in manifest['proof_files'].items():
    assert H(R / n) == d['sha256']
snapshot = R / manifest['snapshot']
for n, expected in old['protected_selected22']['frozen48_asset_sha256'].items():
    assert H(snapshot / n) == expected
for n, expected in old['protected_selected22']['held_working22_ledger_sha256'].items():
    assert H(R / n) == expected
report = {
 'status': 'independent_canonical_source_and_actual_pair_binding_confirmation_passed',
 'reviewer': '/root/modules_resume', 'bound_at_utc': datetime.now(timezone.utc).isoformat(),
 'original_semantic_review': {**REF(old_path), 'original_reviewed_at_utc': old['reviewed_at_utc']},
 'canonical_readiness': REF(req_path), 'canonical_proof_source': req['canonical_source'],
 'material_units': copy.deepcopy(old['material_units']),
 'actual_canonical_pair': pairs, 'actual_pair_helper_execution': REF(execution),
 'original_full_semantic_body_decisions_hypotheses_reasons_declarations_and_time_preserved': True,
 'original_source48_identity': REF(inv48), 'current_unchanged_Basics_identity': {
     'inventory': REF(current_inv), 'two_entire_unit_records_and_parent_equal_original48': True},
 'all1113_selected22_sources_31_frozen48_assets_four_working22_ledgers_exact': True,
 'actual_checker': str(Path(__file__)), 'actual_checker_sha256': H(__file__),
 'limits': ['Only source byte identity and genuine canonical standalone/named execution are added.',
            'The two whole decisions and all original semantic scopes/times remain unchanged. No parent exercise or Module8 theorem is promoted.',
            'Source48 inventory and frozen22 old assets are explicit historical identities. The unrelated Monitoring correction may change current inventory while both current Basics units and parent remain exactly equal.',
            'No live owner integration or aggregate23 execution is inferred.'], 'errors': []}
OUT.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(OUT), 'sha256': H(OUT)}))
