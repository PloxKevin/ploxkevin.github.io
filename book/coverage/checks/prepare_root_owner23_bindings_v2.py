"""Bind completed independent candidates and original actual compiler records.

This preparation writes a new manifest only. It never installs owner ledgers.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
DEST = 'book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json'
OFFERS = {
    'core': 'book/coverage/checks/future23-core/core-audit23-candidate-source51-additions-v2-reviewed.json',
    'foundations': 'book/coverage/checks/foundations-future23/source51/foundations-audit23-candidate-source51-additions-v2-reviewed.json',
    'applied': 'book/coverage/checks/applied-future23/source51/applied-audit23-candidate-source51-additions-v2-reviewed.json',
    'modules': 'book/coverage/checks/modules-future23/source51/modules-audit23-candidate-source51-lft-additions-v3-reviewed.json',
}

def path(name):
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts
    assert (ROOT / p).resolve().is_relative_to(ROOT.resolve())
    return ROOT / p

def sha(name): return hashlib.sha256(path(name).read_bytes()).hexdigest()
def read(name): return json.loads(path(name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}
def checked(r):
    assert sha(r['file']) == r['sha256']
    return read(r['file'])

baseline_name = 'reports/full-coverage/checkpoint-22-manifest.json'
baseline = read(baseline_name)
old = read('book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json')
owners = {}
for owner, offer_name in OFFERS.items():
    offer = read(offer_name)
    pointer = 'module_ledger' if owner == 'modules' else 'mapped_ledger'
    candidate = {'file': offer[pointer], 'sha256': offer[pointer + '_sha256']}
    checked(candidate)
    peer_ref = offer.get('final_independent_candidate_mapping_peer', offer.get('independent_final_candidate_mapping_peer'))
    peer = checked(peer_ref)
    peer_key = 'candidate' if owner in {'core', 'modules'} else 'candidate_ledger'
    assert peer[peer_key] == candidate
    if owner == 'core':
        builder = {'file': offer['actual_builder'], 'sha256': offer['actual_builder_sha256']}
        semantic_refs = [dict(file=n, sha256=s) for n, s in offer['review_sha256'].items()]
    elif owner == 'foundations':
        builder = {'file': offer['actual_builder_record'], 'sha256': offer['actual_builder_record_sha256']}
        semantic_refs = [dict(file=n, sha256=s) for n, s in offer['exact_source_reviews_sha256'].items()]
    elif owner == 'modules':
        builder = {k: offer['actual_builder'][k] for k in ('file', 'sha256')}
        semantic_refs = [{k: r[k] for k in ('file', 'sha256')} for r in offer['original_full_source_reviews']]
    else:
        builder = offer['actual_isolated_candidate_preparation']
        semantic_refs = [{k: r[k] for k in ('file', 'sha256')} for r in old['owners']['applied']['original_full_source_semantic_reviews']]
    assert checked(builder)['actual_exit_code'] == 0
    semantics = []
    for r in semantic_refs:
        body = checked(r)
        assert body.get('errors', []) == []
        semantics.append(dict(r, original_review_status=body['status'], original_review_time=body.get('reviewed_at_utc', body.get('checked_at_utc'))))
    proofs = {}
    for name, row in offer['proof_files'].items():
        assert sha(name) == row['sha256'] and name not in baseline['proof_files']
        pairs = row.get('actual_paired_records')
        if pairs is None:
            pairs = []
            for evidence_name, digest in row['evidence_sha256'].items():
                assert sha(evidence_name) == digest
                if not evidence_name.endswith('.json'): continue
                execution = read(evidence_name)
                if execution.get('source') != name or execution.get('source_sha256_before') != row['sha256']: continue
                assert execution.get('source_sha256_after') == row['sha256']
                codes = [execution[k] for k in ('actual_exit_code', 'exit_code') if k in execution]
                assert codes and all(c == 0 for c in codes)
                log_names = [n for n, s in row['evidence_sha256'].items() if n.endswith('.log') and s == execution['log_sha256']]
                original_log = execution.get('log')
                log_name = original_log if original_log in log_names else log_names[0]
                pairs.append({'actual_record': ref(evidence_name), 'raw_log': ref(log_name)})
        assert len(pairs) == 2, name
        actual_pairs = []
        for pair in pairs:
            r = {k: pair['actual_record'][k] for k in ('file', 'sha256')}
            execution = checked(r)
            assert execution['source'] == name
            log = {k: pair['raw_log'][k] for k in ('file', 'sha256')}
            assert sha(log['file']) == log['sha256'] == execution['log_sha256']
            actual_pairs.append(dict(r, actual_source=name, actual_command=execution['command'], actual_workdir=execution['actual_workdir'], canonical_raw_log=log))
        proofs[name] = {'sha256': row['sha256'], 'actual_pair': actual_pairs}
    provenance = []
    evidence = dict(offer.get('required_evidence_artifacts_sha256', {}))
    for proof in offer['proof_files'].values():
        evidence.update(proof['evidence_sha256'])
    for n, s in evidence.items():
        assert sha(n) == s, n
        provenance.append({'file': n, 'sha256': s})
    ledger_name = 'book/coverage/' + owner + '.json'
    held = baseline['working_inputs_sha256'][ledger_name]
    assert sha(ledger_name) == held
    companions = []
    if owner == 'applied':
        auxiliary = 'book/coverage/applied-promotions.json'
        assert sha(auxiliary) == baseline['working_inputs_sha256'][auxiliary]
        companions.append({'held22_asset': auxiliary, 'held22_asset_sha256': sha(auxiliary), 'candidate': {'file': offer['mapped_promotions'], 'sha256': offer['mapped_promotions_sha256']}})
    owners[owner] = {'ready': True, 'held22_ledger': ledger_name, 'held22_ledger_sha256': held, 'candidate_ledger': candidate, 'reviewed_final_offer': ref(offer_name), 'offer_candidate_path_pointer': [pointer], 'offer_candidate_sha256_pointer': [pointer + '_sha256'], 'independent_candidate_mapping_peer': peer_ref, 'peer_candidate_path_pointer': [peer_key, 'file'], 'peer_candidate_sha256_pointer': [peer_key, 'sha256'], 'actual_candidate_builder': builder, 'original_full_source_semantic_reviews': semantics, 'additional_exact_provenance': provenance, 'new_immutable_proof_sources': proofs, 'companion_candidates': companions}

inventory = read('book/coverage/inventory.json')
assets = {n: sha(n) for n in baseline['frozen_inputs_sha256'] if n.startswith('SafeLearning/')}
assert len(assets) == 31
assert sum(len(r['new_immutable_proof_sources']) for r in owners.values()) == 18
out = {'status': 'all_four_reviewed_current51_owner_candidates_bound_ready_for_root_execution', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'preparation_helper': ref(str(Path(__file__).relative_to(ROOT))), 'helper': ref('book/coverage/checks/root_integrate_owner23_candidates_v2.py'), 'independent_helper_review': ref('book/coverage/checks/future23-core/original-tmp/root23-three-helpers-independent-modules-code-review-v1.json'), 'baseline22_manifest': ref(baseline_name), 'inventory_sha256': sha('book/coverage/inventory.json'), 'exact_current51_safelearning_assets_sha256': assets, 'actual_source51_apply': ref('reports/full-coverage/source51-apply-execution-v1.json'), 'actual_source51_postwrite': ref('book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json'), 'source51_corrections_sha256': sha('book/coverage/material-corrections.json'), 'owners': owners, 'coverage_complete': False, 'scope': 'Preparation only: completed exact candidates, fresh independent mapping peers, original semantic bodies/times, and original actual standalone/named records are pinned. Integration and aggregate23 require separate actual executions.'}
assert not path(DEST).exists()
with path(DEST).open('x') as f: f.write(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'binding': ref(DEST), 'owners': 4, 'new_sources': 18}))
