"""Prepare one NEW exact owner26 binding manifest; never install owner assets.

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
BASELINE = 'reports/full-coverage/checkpoint-25-manifest.json'
BASELINE_SHA = '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
INVENTORY = 'book/coverage/inventory-after-correction53.json'
INVENTORY_SHA = '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
INTEGRATION = 'book/coverage/checks/root_integrate_owner26_candidates_v1.py'
INTEGRATION_SHA = 'c4908715dfffd56595c602cee097a0097cefc71f3ec50ce7e5a88f228c61376e'
OWNERS = {'core', 'foundations', 'applied', 'modules'}
EXPECTED_SOURCES = {'core': 4, 'foundations': 2, 'applied': 3, 'modules': 2}

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


def pointer(data, keys):
    assert isinstance(keys, list) and keys
    for key in keys: data = data[key]
    return data

def actual_builder_evidence(record):
    zero(record)
    command = alias(record, ('actual_command', 'command'))
    assert isinstance(command, list) and len(command) >= 2 and command[0] in ('python', 'python3')
    helper = command[1]; safe(helper)
    assert helper.startswith('book/coverage/') and helper.endswith('.py')
    assert alias(record, ('actual_workdir', 'cwd')) == str(ROOT)
    before = alias(record, ('helper_sha256_before', 'actual_helper_sha256_before'))
    after = alias(record, ('helper_sha256_after', 'actual_helper_sha256_after'))
    assert before == after
    if isinstance(before, dict):
        assert helper in before and before
        for name, digest in before.items(): assert sha(name) == digest
    else: assert isinstance(before, str) and sha(helper) == before
    log = alias(record, ('log', 'raw_log'))
    log_hash = alias(record, ('log_sha256', 'raw_log_sha256', 'original_log_sha256'))
    assert sha(log) == log_hash
    return log, log_hash

def build_binding(config, input_name):
    assert config['status'] == 'root_requested_exact_four_owner26_binding_preparation_inputs'
    assert set(config['offers']) == OWNERS and set(config['owner_interfaces']) == OWNERS and set(config['extra_closed_evidence']) == OWNERS
    assert config['preparation_helper'] == ref(str(Path(__file__).relative_to(ROOT)))
    assert sha(INTEGRATION) == INTEGRATION_SHA
    helper_peer = checked(config['independent_integration_helper_review'])
    assert 'passed' in helper_peer['status'] and helper_peer.get('errors', []) == [] and helper_peer['helper_sha256'] == INTEGRATION_SHA
    assert sha(BASELINE) == BASELINE_SHA
    baseline = read(BASELINE)
    assert len(baseline['proof_files']) == 1156 and len(baseline['frozen_inputs_sha256']) == 44111
    assert sha(baseline['selection']) == baseline['selection_sha256']
    assert sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    assets = {n: sha(n) for n in baseline['frozen_inputs_sha256'] if n.startswith('SafeLearning/')}
    original_assets = {n: h for n, h in baseline['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets) == 31 and {n for n in assets if assets[n] != original_assets[n]} == {'SafeLearning/lyapunov-mpc.html'}
    application_name = 'reports/full-coverage/source53-correction-application-v1.json'
    assert sha(application_name) == 'fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548'
    application, application_execution = read(application_name), read('reports/full-coverage/source53-correction-application-execution-v1.json')
    zero(application_execution)
    assert 'passed' in application['status'] and application['selected25_proof_sources_unchanged'] == 1156 and application['five_installed25_owner_ledgers_unchanged'] is True
    assert application['inventory_after'] == ref(INVENTORY)
    assert assets['SafeLearning/lyapunov-mpc.html'] == application['source_after']['sha256'] == '5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
    assert original_assets['SafeLearning/lyapunov-mpc.html'] == application['source_before']['sha256']
    assert application_execution['helper_sha256_before'] == application_execution['helper_sha256_after'] == {'book/coverage/checks/root_apply_source53_v2.py':'20d5933637d720bdd263838f2af361425d4aa730e6ad33d721e61f5c625d481e'}
    assert sha(application_execution['log']) == application_execution['log_sha256']
    assert len(read('book/coverage/material-corrections.json')['corrections']) == 53
    held = {n: baseline['working_inputs_sha256'][n] for n in ['book/coverage/' + owner + '.json' for owner in OWNERS] + ['book/coverage/applied-promotions.json']}
    for n,h in held.items(): assert sha(n) == h
    owners, new_sources, export_count = {}, {}, 0
    pointer_keys = {'offer_candidate_path_pointer','offer_candidate_sha256_pointer','offer_independent_peer_pointer','peer_candidate_path_pointer','peer_candidate_sha256_pointer','offer_actual_builder_path_pointer','offer_actual_builder_sha256_pointer','original_full_source_semantic_reviews'}
    for owner in sorted(OWNERS):
        offer_ref = config['offers'][owner]; offer = checked(offer_ref)
        schema = config['owner_interfaces'][owner]; assert set(schema) == pointer_keys
        inventories = [offer[k] for k in ('inventory_sha256', 'current_inventory_sha256') if k in offer]
        assert inventories and all(h == INVENTORY_SHA for h in inventories)
        candidate = {'file':pointer(offer,schema['offer_candidate_path_pointer']),'sha256':pointer(offer,schema['offer_candidate_sha256_pointer'])}
        peer_ref = pointer(offer,schema['offer_independent_peer_pointer'])
        assert isinstance(peer_ref,dict) and set(peer_ref) == {'file','sha256'}
        candidate_data, peer = checked(candidate), checked(peer_ref)
        assert 'passed' in peer['status'] and peer.get('errors',[]) == []
        assert pointer(peer,schema['peer_candidate_path_pointer']) == candidate['file'] and pointer(peer,schema['peer_candidate_sha256_pointer']) == candidate['sha256']
        build_ref = {'file':pointer(offer,schema['offer_actual_builder_path_pointer']),'sha256':pointer(offer,schema['offer_actual_builder_sha256_pointer'])}
        actual_builder = checked(build_ref); builder_log, builder_log_hash = actual_builder_evidence(actual_builder)
        semantics = []
        assert isinstance(schema['original_full_source_semantic_reviews'],list) and schema['original_full_source_semantic_reviews']
        for semantic_ref in schema['original_full_source_semantic_reviews']:
            body = checked(semantic_ref); assert body.get('errors',[]) == []
            original_time = body.get('reviewed_at_utc',body.get('checked_at_utc')); assert original_time is not None
            semantics.append(dict(semantic_ref,original_review_status=body['status'],original_review_time=original_time))
        proof_rows = offer['proof_files']; assert len(proof_rows) == EXPECTED_SOURCES[owner]
        proofs, evidence = {}, {}
        for key in ('required_evidence_artifacts_sha256','required_live_integration_evidence_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256','actual_canonical_execution_records_sha256','additional_frozen_inputs'):
            for n,h in offer.get(key,{}).items(): add_evidence(evidence,n,h)
        for source,proof in proof_rows.items():
            assert source not in baseline['proof_files'] and source not in new_sources
            normalized = canonical_pair(source,proof); proofs[source]=normalized; new_sources[source]=normalized['sha256']
            public_count = len(re.findall(r'^(?:theorem|lemma)\s+\w+',safe(source).read_text(),re.M)); assert public_count > 0; export_count += public_count
            for n,h in proof['evidence_sha256'].items(): add_evidence(evidence,n,h)
        for r in config['extra_closed_evidence'][owner]: add_evidence(evidence,r['file'],r['sha256'])
        add_evidence(evidence,build_ref['file'],build_ref['sha256']);add_evidence(evidence,builder_log,builder_log_hash)
        for source,digest in candidate_data['source_sha256'].items():
            assert sha(source) == digest
            if source.startswith('SafeLearning/'): assert assets[source] == digest
            else: assert read('book/coverage/' + owner + '.json')['source_sha256'][source] == digest
        companions = []
        if owner == 'applied':
            destination = 'book/coverage/applied-promotions.json';companion={'file':offer['mapped_promotions'],'sha256':offer['mapped_promotions_sha256']};checked(companion)
            companions.append({'held25_asset':destination,'held25_asset_sha256':held[destination],'candidate':companion})
        ledger = 'book/coverage/' + owner + '.json'
        owners[owner] = {'ready':True,'held25_ledger':ledger,'held25_ledger_sha256':held[ledger],
            'candidate_ledger':candidate,'reviewed_final_offer':offer_ref,
            'offer_candidate_path_pointer':schema['offer_candidate_path_pointer'],'offer_candidate_sha256_pointer':schema['offer_candidate_sha256_pointer'],
            'independent_candidate_mapping_peer':peer_ref,'peer_candidate_path_pointer':schema['peer_candidate_path_pointer'],'peer_candidate_sha256_pointer':schema['peer_candidate_sha256_pointer'],
            'actual_candidate_builder':build_ref,'original_full_source_semantic_reviews':semantics,
            'additional_exact_provenance':[dict(file=n,sha256=h) for n,h in sorted(evidence.items())],
            'new_immutable_proof_sources':proofs,'companion_candidates':companions}
    assert len(new_sources) == 11 and export_count == 134
    for n,h in held.items():assert sha(n) == h
    return {'status':'all_four_reviewed_current53_owner_candidates_bound_ready_for_root_execution',
        'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'preparation_helper':ref(str(Path(__file__).relative_to(ROOT))),'preparation_input':ref(input_name),
        'helper':ref(INTEGRATION),'independent_helper_review':config['independent_integration_helper_review'],
        'baseline25_manifest':ref(BASELINE),'inventory_sha256':INVENTORY_SHA,'exact_current53_safelearning_assets_sha256':assets,
        'actual_source53_application':ref(application_name),'actual_source53_application_execution':ref('reports/full-coverage/source53-correction-application-execution-v1.json'),
        'source53_corrections_sha256':sha('book/coverage/material-corrections.json'),
        'owners':owners,'new_proof_sources':11,'new_public_exports':134,'original_canonical_execution_records':22,'coverage_complete':False,
        'scope':'Preparation only. All original semantic bodies/times, eleven actual canonical sources134 and22 native pair records are pinned unchanged. Only a new manifest is written. Root integration/global26/production selection/aggregate/publication require separate actual executions.'}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--input',required=True);parser.add_argument('--input-sha256',required=True);parser.add_argument('--root-authorized-binding-preparation',action='store_true',required=True);args=parser.parse_args()
    assert args.root_authorized_binding_preparation and sha(args.input) == args.input_sha256
    config=read(args.input);destination=config['destination']
    assert destination.startswith('book/coverage/checks/root-owner26-reviewed-candidate-bindings-') and destination.endswith('.json') and not safe(destination).exists()
    body=build_binding(config,args.input)
    with safe(destination).open('x') as output:output.write(json.dumps(body,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'binding_manifest':ref(destination),'owners':4,'new_sources':11,'public_exports':134,'original_canonical_execution_records':22}))
if __name__=='__main__':main()
