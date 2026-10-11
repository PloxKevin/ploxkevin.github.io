"""Prepare one NEW exact owner25 binding manifest; never install owner assets.

Root must supply a pinned input JSON and explicitly request execution. Original
offers, semantic reviews, candidate builders and compiler records are read only.
This version accepts the native command/log aliases only when all aliases agree.
Absolute TMP compiler history is retained as provenance and is never eligible as
the required canonical standalone/named pair.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
BASELINE = 'reports/full-coverage/checkpoint-24-manifest.json'
BASELINE_SHA = '5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0'
INVENTORY = 'book/coverage/inventory-after-correction52.json'
INVENTORY_SHA = '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
INTEGRATION = 'book/coverage/checks/root_integrate_owner25_candidates_v1.py'
INTEGRATION_SHA = 'fca0f767652c079d280bf6112767f0b4bc9bcb7d09929f2c85b06c82c4e1a973'
OWNERS = {'core', 'foundations', 'applied', 'modules'}
EXPECTED_SOURCES = {'core': 1, 'foundations': 2, 'applied': 7, 'modules': 2}

def safe(name):
    assert isinstance(name, str) and name
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts and str(p) == name
    target = ROOT / p
    assert target.resolve().is_relative_to(ROOT.resolve())
    return target

def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}
def checked(row):
    assert isinstance(row, dict) and set(row) == {'file', 'sha256'}
    assert isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256'])
    assert sha(row['file']) == row['sha256'], row['file']
    return read(row['file'])

def alias(record, keys):
    values = [record[k] for k in keys if k in record]
    assert values and all(value == values[0] for value in values), keys
    return values[0]

def zero(record):
    values = [record[k] for k in ('actual_exit_code', 'exit_code') if k in record]
    assert values and all(type(value) is int and value == 0 for value in values)

def add_evidence(dest, name, digest):
    assert isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest)
    assert sha(name) == digest, name
    assert name not in dest or dest[name] == digest
    dest[name] = digest

def canonical_pair(source, proof):
    """Normalize a genuine relative-input standalone and lake named build."""
    digest = proof['sha256']
    assert sha(source) == digest
    evidence = proof['evidence_sha256']
    for name, value in evidence.items(): assert sha(name) == value, name
    canonical_input = str(Path(source).relative_to('verification/lean'))
    commands = {'standalone': ['lake', 'env', 'lean', canonical_input],
                'named': ['lake', 'build', 'SafeLearning.' + Path(source).stem]}
    eligible = {'standalone': [], 'named': []}
    for name, record_hash in evidence.items():
        if not name.endswith('.json'): continue
        record = read(name)
        if not isinstance(record, dict): continue
        if record.get('source') != source: continue
        if record.get('source_sha256_before') != digest or record.get('source_sha256_after') != digest: continue
        if not any(k in record for k in ('command', 'actual_command')): continue
        command = alias(record, ('command', 'actual_command'))
        if not isinstance(command, list): continue
        kind = next((kind for kind, expected in commands.items() if command == expected), None)
        if kind is None:
            # Original TMP/lean -o/other executions remain immutable evidence.
            # They cannot supply either member of this canonical pair.
            continue
        zero(record)
        assert record.get('source_unchanged', True) is True
        assert record['actual_workdir'] == str(ROOT / 'verification/lean')
        log_hash = alias(record, ('log_sha256', 'raw_log_sha256'))
        raw_names = [record[k] for k in ('log', 'raw_log') if k in record]
        assert raw_names and all(isinstance(n, str) for n in raw_names)
        logs = sorted(n for n, h in evidence.items() if n.endswith('.log') and h == log_hash)
        assert logs, name
        for raw_name in raw_names:
            if not Path(raw_name).is_absolute():
                assert sha(raw_name) == log_hash, raw_name
            # Absolute original names may only survive through exact aliases.
        preferred = next((n for n in raw_names if n in logs), logs[0])
        if 'source_snapshot_sha256' in record or 'preserved_source_sha256' in record:
            snapshot_hash = alias(record, ('source_snapshot_sha256', 'preserved_source_sha256'))
            assert snapshot_hash == digest
            assert any(n.endswith('.lean') and h == digest for n, h in evidence.items())
            for k in ('source_snapshot', 'preserved_source'):
                if k in record and not Path(record[k]).is_absolute(): assert sha(record[k]) == digest
        eligible[kind].append({'file': name, 'sha256': record_hash,
            'actual_source': source, 'actual_command': command,
            'actual_workdir': record['actual_workdir'],
            'canonical_raw_log': {'file': preferred, 'sha256': log_hash}})
    assert all(len(rows) == 1 for rows in eligible.values()), (source, eligible)
    return {'sha256': digest, 'actual_pair': [eligible['standalone'][0], eligible['named'][0]]}

def semantic_refs(owner, offer):
    if owner == 'core': return offer['whole_source_reviews']
    if owner == 'foundations': return [dict(file=n, sha256=h) for n, h in offer['exact_source_reviews_sha256'].items()]
    key = 'original_independent_review_references' if owner == 'applied' else 'original_full_or_precise_source_reviews'
    return [{k: row[k] for k in ('file', 'sha256')} for row in offer[key]]

def candidate_schema(owner, offer):
    if owner == 'core':
        candidate = {k: offer['candidate_ledger'][k] for k in ('file', 'sha256')}
        peer_ref = offer['final_independent_candidate_peer']
        return candidate, peer_ref, ['candidate_ledger', 'file'], ['candidate_ledger', 'sha256'], 'candidate'
    key = 'module_ledger' if owner == 'modules' else 'mapped_ledger'
    candidate = {'file': offer[key], 'sha256': offer[key + '_sha256']}
    peer_key = 'independent_final_candidate_mapping_peer' if owner == 'modules' else 'final_independent_candidate_mapping_peer'
    return candidate, offer[peer_key], [key], [key + '_sha256'], 'candidate'

def builder_ref(owner, offer, peer):
    if owner == 'core': return offer['actual_builder']
    if owner == 'foundations': return {'file': offer['actual_builder_record'], 'sha256': offer['actual_builder_record_sha256']}
    if owner == 'modules': return {k: offer['actual_builder'][k] for k in ('file', 'sha256')}
    return offer['actual_isolated_candidate_preparation']

def build_binding(config, input_name):
    assert config['status'] == 'root_requested_exact_four_owner25_binding_preparation_inputs'
    assert set(config['offers']) == OWNERS and set(config['extra_closed_evidence']) == OWNERS
    assert config['preparation_helper'] == ref(str(Path(__file__).relative_to(ROOT)))
    assert sha(INTEGRATION) == INTEGRATION_SHA
    helper_peer = checked(config['independent_integration_helper_review'])
    assert 'passed' in helper_peer['status'] and helper_peer.get('errors', []) == []
    assert helper_peer['helper_sha256'] == INTEGRATION_SHA
    assert sha(BASELINE) == BASELINE_SHA
    baseline = read(BASELINE)
    assert len(baseline['proof_files']) == 1144 and len(baseline['frozen_inputs_sha256']) == 40485
    assert sha(baseline['selection']) == baseline['selection_sha256']
    assert sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    assets = {n: sha(n) for n in baseline['frozen_inputs_sha256'] if n.startswith('SafeLearning/')}
    original_assets = {n: h for n, h in baseline['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets) == 31
    assert {n for n in assets if assets[n] != original_assets[n]} == set()
    assert assets['SafeLearning/nn-in-the-loop.html'] == '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
    apply_name = 'reports/full-coverage/source52-apply-execution-v1.json'
    post_name = 'book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'
    apply, post = read(apply_name), read(post_name)
    zero(apply); zero(post)
    assert post['inventory_after_sha256'] == INVENTORY_SHA
    assert sha(alias(apply, ('log', 'raw_log'))) == alias(apply, ('log_sha256', 'raw_log_sha256'))
    held = {n: baseline['working_inputs_sha256'][n] for n in ['book/coverage/' + owner + '.json' for owner in OWNERS] + ['book/coverage/applied-promotions.json']}
    for n, h in held.items(): assert sha(n) == h
    owners, new_sources = {}, {}
    for owner in sorted(OWNERS):
        offer_ref = config['offers'][owner]
        offer = checked(offer_ref)
        inventory_values = [offer[k] for k in ('inventory_sha256', 'current_inventory_sha256') if k in offer]
        assert inventory_values and all(h == INVENTORY_SHA for h in inventory_values)
        candidate, peer_ref, path_pointer, hash_pointer, peer_key = candidate_schema(owner, offer)
        candidate_data, peer = checked(candidate), checked(peer_ref)
        assert 'passed' in peer['status'] and peer.get('errors', []) == []
        assert peer[peer_key] == candidate
        build_ref = builder_ref(owner, offer, peer)
        actual_builder = checked(build_ref)
        zero(actual_builder)
        builder_log = alias(actual_builder, ('log', 'raw_log'))
        builder_log_hash = alias(actual_builder, ('log_sha256', 'raw_log_sha256'))
        assert sha(builder_log) == builder_log_hash
        semantics = []
        for semantic_ref in semantic_refs(owner, offer):
            body = checked(semantic_ref)
            assert body.get('errors', []) == []
            original_time = body.get('reviewed_at_utc', body.get('checked_at_utc'))
            assert original_time is not None
            semantics.append(dict(semantic_ref, original_review_status=body['status'], original_review_time=original_time))
        assert semantics
        proof_rows = offer['proof_files']
        assert len(proof_rows) == EXPECTED_SOURCES[owner]
        proofs = {}
        evidence = {}
        for map_key in ('required_evidence_artifacts_sha256', 'required_live_integration_evidence_sha256', 'canonical_readiness_sha256', 'canonical_source_peer_bindings_sha256', 'actual_canonical_execution_records_sha256'):
            for n, h in offer.get(map_key, {}).items(): add_evidence(evidence, n, h)
        for source, proof in proof_rows.items():
            assert source not in baseline['proof_files'] and source not in new_sources
            normalized = canonical_pair(source, proof)
            proofs[source] = normalized
            new_sources[source] = normalized['sha256']
            for n, h in proof['evidence_sha256'].items(): add_evidence(evidence, n, h)
        for r in config['extra_closed_evidence'][owner]: add_evidence(evidence, r['file'], r['sha256'])
        add_evidence(evidence, build_ref['file'], build_ref['sha256'])
        add_evidence(evidence, builder_log, builder_log_hash)
        for source, digest in candidate_data['source_sha256'].items():
            assert sha(source) == digest
            if source.startswith('SafeLearning/'): assert assets[source] == digest
            else: assert read('book/coverage/' + owner + '.json')['source_sha256'][source] == digest
        companions = []
        if owner == 'applied':
            destination = 'book/coverage/applied-promotions.json'
            companion = {'file': offer['mapped_promotions'], 'sha256': offer['mapped_promotions_sha256']}
            checked(companion)
            companions.append({'held24_asset': destination, 'held24_asset_sha256': held[destination], 'candidate': companion})
        ledger = 'book/coverage/' + owner + '.json'
        owners[owner] = {'ready': True, 'held24_ledger': ledger, 'held24_ledger_sha256': held[ledger],
            'candidate_ledger': candidate, 'reviewed_final_offer': offer_ref,
            'offer_candidate_path_pointer': path_pointer, 'offer_candidate_sha256_pointer': hash_pointer,
            'independent_candidate_mapping_peer': peer_ref,
            'peer_candidate_path_pointer': [peer_key, 'file'], 'peer_candidate_sha256_pointer': [peer_key, 'sha256'],
            'actual_candidate_builder': build_ref, 'original_full_source_semantic_reviews': semantics,
            'additional_exact_provenance': [dict(file=n, sha256=h) for n, h in sorted(evidence.items())],
            'new_immutable_proof_sources': proofs, 'companion_candidates': companions}
    assert len(new_sources) == 12
    for n, h in held.items(): assert sha(n) == h
    return {'status': 'all_four_reviewed_current52_owner_candidates_bound_ready_for_root_execution',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'preparation_helper': ref(str(Path(__file__).relative_to(ROOT))), 'preparation_input': ref(input_name),
        'helper': ref(INTEGRATION), 'independent_helper_review': config['independent_integration_helper_review'],
        'baseline24_manifest': ref(BASELINE), 'inventory_sha256': INVENTORY_SHA,
        'exact_current52_safelearning_assets_sha256': assets,
        'actual_source52_apply': ref(apply_name), 'actual_source52_postwrite': ref(post_name),
        'source52_corrections_sha256': sha('book/coverage/material-corrections.json'),
        'owners': owners, 'new_proof_sources': 12, 'original_canonical_execution_records': 24,
        'coverage_complete': False,
        'scope': 'Preparation only. Original actual canonical pairs, semantic bodies/times and fresh current52 candidate peers are pinned without rewriting them. This helper only writes a new manifest. Root integration/global25/production selection/aggregate audit/publication require their own actual executions.'}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', required=True)
    parser.add_argument('--input-sha256', required=True)
    parser.add_argument('--root-authorized-binding-preparation', action='store_true', required=True)
    args = parser.parse_args()
    assert args.root_authorized_binding_preparation and sha(args.input) == args.input_sha256
    config = read(args.input)
    destination = config['destination']
    assert destination.startswith('book/coverage/checks/root-owner25-reviewed-candidate-bindings-') and destination.endswith('.json')
    assert not safe(destination).exists()
    body = build_binding(config, args.input)
    with safe(destination).open('x') as f: f.write(json.dumps(body, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps({'binding_manifest': ref(destination), 'owners': 4, 'new_sources': 12, 'original_canonical_execution_records': 24}))

if __name__ == '__main__': main()
