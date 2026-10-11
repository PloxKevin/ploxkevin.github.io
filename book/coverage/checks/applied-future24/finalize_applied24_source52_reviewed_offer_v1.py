"""Append closed identity-peer provenance to the immutable source52 draft only."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[4]
BASE = 'book/coverage/checks/applied-future24/source52'
DRAFT = BASE + '/applied-audit24-candidate-source52-additions-v1.json'
DEST = BASE + '/applied-audit24-candidate-source52-additions-v2-reviewed.json'
PEER = 'book/coverage/checks/future24-core/source52-independent-owner-identity-peer/applied24-source52-identity-independent-modules-confirmation-v1.json'
INV = 'book/coverage/inventory-after-correction52.json'

def sha(name): return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}
def checked(row):
    assert sha(row['file']) == row['sha256'], row['file']
    return read(row['file'])

def main():
    assert sha(DRAFT) == '536b7b97eb56eda0ce5bf15dd01001ceabc76a168188a8710e4a1668c699f8ec'
    assert sha(PEER) == '443da1ea6382a604f034f544ff076f8ccb20a5d4db1c9552ecb61663342f64df'
    assert sha(INV) == sha('book/coverage/inventory.json') == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
    draft, peer = read(DRAFT), read(PEER)
    assert 'passed' in peer['status'] and peer['errors'] == []
    assert peer['source52_offer'] == ref(DRAFT)
    assert peer['source52_candidate'] == {'file': draft['mapped_ledger'], 'sha256': draft['mapped_ledger_sha256']}
    assert peer['candidate_and_offer_inverse_exact'] is True
    assert peer['mathematical_bodies_hypotheses_reasons_decisions_times_proofs_and_compiler_records_unchanged'] is True
    assert draft['counts']['new_proof_sources'] == 4 and draft['counts']['new_public_exports'] == 29
    evidence = copy.deepcopy(draft['required_live_integration_evidence_sha256'])
    evidence[PEER] = sha(PEER)
    for row in peer['prior_checker_versions_and_actual_failures_preserved'].values():
        assert sha(row['file']) == row['sha256']
        evidence[row['file']] = row['sha256']
    for key in ['original_checker', 'actual_independent_checker_execution', 'actual_independent_checker_raw_log', 'actual_outer_measured_runner']:
        row = peer[key]
        assert sha(row['file']) == row['sha256']
        evidence[row['file']] = row['sha256']
    execution = checked(peer['actual_independent_checker_execution'])
    assert execution['actual_exit_code'] == 0
    identity = peer['actual_identity_execution']
    for key in ['actual_record', 'raw_log', 'helper']:
        row = identity[key]
        assert sha(row['file']) == row['sha256']
        evidence[row['file']] = row['sha256']
    assert checked(identity['actual_record'])['actual_exit_code'] == 0
    for key in ['identity_sidecar', 'identity_integrity']:
        row = draft['current52_identity_rebase'][key]
        assert sha(row['file']) == row['sha256']
        evidence[row['file']] = row['sha256']
    helper = str(Path(__file__).relative_to(ROOT))
    evidence[helper] = sha(helper)
    for name, digest in evidence.items(): assert sha(name) == digest, name
    for name, digest in peer['held_live_owner_sha256'].items(): assert sha(name) == digest, name
    out = copy.deepcopy(draft)
    out['required_live_integration_evidence_sha256'] = evidence
    out['final_independent_candidate_mapping_peer'] = ref(PEER)
    out['actual_isolated_candidate_preparation'] = identity['actual_record']
    out['source52_final_reviewed_identity_offer_provenance'] = {
        'finalized_at_utc': datetime.now(timezone.utc).isoformat(),
        'original_current52_draft': ref(DRAFT),
        'original_required_live_integration_evidence_sha256': draft['required_live_integration_evidence_sha256'],
        'helper': ref(helper),
        'new_independent_identity_peer_status': peer['status'],
        'original_identity_peer_time': peer['checked_at_utc'],
        'scope': 'Only already-closed current52 identity and independent checker evidence is appended. Entire original semantic decisions, review times, draft/candidate/proof/compiler bodies and four-source29 cutoff remain exact. No live install/global24/selection/aggregate claim. The finalizer does not hash its own open execution output.'}
    reverse = copy.deepcopy(out)
    for key in ['final_independent_candidate_mapping_peer', 'actual_isolated_candidate_preparation', 'source52_final_reviewed_identity_offer_provenance']: reverse.pop(key)
    reverse['required_live_integration_evidence_sha256'] = draft['required_live_integration_evidence_sha256']
    assert reverse == draft
    with (ROOT / DEST).open('x') as f: f.write(json.dumps(out, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({'reviewed_offer': ref(DEST), 'independent_identity_peer': ref(PEER), 'new_sources': 4, 'new_exports': 29, 'inverse_draft_exact': True}))

if __name__ == '__main__': main()
