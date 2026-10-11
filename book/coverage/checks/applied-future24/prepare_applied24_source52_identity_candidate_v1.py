"""Unexecuted draft: Root-authorized isolated source52 identity rebase only.
Never writes live ledgers, HTML, inventory, Lean sources, or original source51 artifacts.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json
ROOT = Path(__file__).resolve().parents[4]
BASE = 'book/coverage/checks/applied-future24/source52'
OLD_OFFER = 'book/coverage/checks/applied-future24/source51/applied-audit24-candidate-source51-additions-v2-reviewed.json'
OLD_OFFER_SHA = '67fa27df2b462cc4bc655fe5177924963d6cef5b7a1a1d2fd7cac449e4958627'
OLD_INV = 'book/coverage/inventory-after-correction51.json'
OLD_INV_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
NEW_INV = 'book/coverage/inventory-after-correction52.json'
LIVE = {'book/coverage/applied.json': 'cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131', 'book/coverage/applied-promotions.json': '64d40e98a0cb98cbb0e4355c38709a6a89b7d2822e982e34fc340dbc402fcdce'}
def digest(name): return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def ref(name): return {'file': name, 'sha256': digest(name)}
def write(name, body):
    p = ROOT/name
    assert not p.exists(), name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(body, indent=2, ensure_ascii=False)+'\n')
def main():
    p = argparse.ArgumentParser()
    p.add_argument('--inventory-sha256', required=True)
    p.add_argument('--root-authorized-source52-identity-rebase', action='store_true', required=True)
    args = p.parse_args()
    assert args.root_authorized_source52_identity_rebase
    assert len(args.inventory_sha256) == 64 and all(c in '0123456789abcdef' for c in args.inventory_sha256)
    assert digest(NEW_INV) == digest('book/coverage/inventory.json') == args.inventory_sha256
    assert digest(OLD_INV) == OLD_INV_SHA and digest(OLD_OFFER) == OLD_OFFER_SHA
    old_offer = read(OLD_OFFER)
    assert digest(old_offer['mapped_ledger']) == old_offer['mapped_ledger_sha256']
    assert digest(old_offer['mapped_promotions']) == old_offer['mapped_promotions_sha256']
    old_ledger, old_promotions = read(old_offer['mapped_ledger']), read(old_offer['mapped_promotions'])
    assert all(digest(k) == v for k, v in LIVE.items())
    a, b = read(OLD_INV), read(NEW_INV)
    scope = set(old_ledger['scope_pages'])
    assert len(scope) == 3 and set(old_offer['source_sha256']) == scope
    assert old_offer['source_sha256'] == old_ledger['source_sha256']
    for path, sha in old_offer['source_sha256'].items():
        assert digest(path) == sha == a['source_sha256'][path] == b['source_sha256'][path]
    records = {}
    for kind, count in [('exercises', 128), ('material_source_units', 2059)]:
        aa = {r['key']: r for r in a[kind] if r['source'] in scope}
        bb = {r['key']: r for r in b[kind] if r['source'] in scope}
        assert aa == bb and len(bb) == count
        records[kind] = list(bb.values())
    assert len(old_ledger['exercises']) == 128
    assert sum(len(e['claims']) for e in old_ledger['exercises']) == 468
    assert len(old_ledger['material_claims']) == 1954 and len(old_ledger['proof_files']) == 302
    assert old_offer['counts']['new_proof_sources'] == 4 and old_offer['counts']['new_public_exports'] == 29
    assert old_offer['counts']['actual_zero_paired_records'] == 8
    manifest = read('reports/full-coverage/checkpoint-23-manifest.json')
    assert len(manifest['proof_files']) == 1131
    for path, row in manifest['proof_files'].items(): assert digest(path) == row['sha256']
    for path, sha in old_ledger['proof_files'].items(): assert digest(path) == sha
    for row in old_offer['new_actual_paired_records']:
        assert digest(row['file']) == row['sha256'] and read(row['file']) == row['entire_original_record']
        r = read(row['file']); assert r['exit_code'] == 0 and digest(r['log']) == r['log_sha256']
    evidence = dict(old_offer.get('required_live_integration_evidence_sha256', {}))
    evidence.update(old_offer.get('required_evidence_artifacts_sha256', {}))
    for path, sha in evidence.items(): assert digest(path) == sha
    for row in old_offer['original_independent_review_references']: assert digest(row['file']) == row['sha256']
    side = BASE+'/unchanged-owned-literal-identity-v1.json'
    identity = {'status': 'exact_source51_to52_unchanged_applied24_owned_entire_literal_records',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'historical_inventory': ref(OLD_INV),
        'current_inventory': ref(NEW_INV), 'original_source51_reviewed_offer': ref(OLD_OFFER),
        'original_source51_candidate': ref(old_offer['mapped_ledger']),
        'original_source51_promotions': ref(old_offer['mapped_promotions']),
        'owned_source_sha256': old_offer['source_sha256'], 'entire_owned_inventory_records': records,
        'all_original_semantic_bodies_hypotheses_decisions_reviewtimes_and_proof_evidence_unchanged': True,
        'counts': {'owned_exercises': 128, 'exercise_claims': 468, 'material_claim_records': 1954,
            'owned_physical_units': 2059, 'proof_metadata_rows': 302, 'new_identity_promotions': 0},
        'limits': ['Source52 changes another owner page only. This is literal identity, not a fresh mathematical decision.',
            'Original five whole material decisions and sole401 covariance component retain exactly their original scopes and times. Whole401 remains pending.',
            'Four canonical sources29 exports/eight compiler records are retained genuine existing evidence; no new compiler/global/aggregate execution is claimed.']}
    write(side, identity)
    overlay = {'inventory': NEW_INV, 'inventory_sha256': digest(NEW_INV), 'identity_sidecar': ref(side),
        'original_source51_reviewed_offer': ref(OLD_OFFER), 'scope': 'Entire unchanged Applied24 source51 literal/semantic/proof bodies preserved; source52 inventory identity only.'}
    out, outp = copy.deepcopy(old_ledger), copy.deepcopy(old_promotions)
    assert 'current52_owner_identity' not in out and 'current52_owner_identity' not in outp
    out['current52_owner_identity'] = overlay; outp['current52_owner_identity'] = overlay
    assert {k:v for k,v in out.items() if k!='current52_owner_identity'} == old_ledger
    assert {k:v for k,v in outp.items() if k!='current52_owner_identity'} == old_promotions
    ledger = BASE+'/applied24-candidate-source52-identity-v1.json'
    promotions = BASE+'/applied-promotions24-candidate-source52-identity-v1.json'
    write(ledger, out); write(promotions, outp)
    integrity = BASE+'/identity-candidate-integrity-v1.json'
    write(integrity, {'status':'passed_exact_isolated_applied24_source52_identity_preparation', 'errors':[],
        'checked_at_utc':datetime.now(timezone.utc).isoformat(), 'candidate':ref(ledger), 'candidate_promotions':ref(promotions),
        'identity_sidecar':ref(side), 'original_source51_reviewed_offer':ref(OLD_OFFER),
        'exact_inverse_restores_entire_source51_candidate_and_promotions':True,
        'all1131_selected23_sources_exact':True, 'all302_candidate_metadata_sources_exact':True,
        'all_owned_records_and_actual_zero_execution_bodies_exact':True, 'live23_owner_assets_unchanged':LIVE,
        'scope':'Actual isolated identity preparation only. No new mathematical review, compiler execution, live owner copy/global validation or aggregate24 audit.'})
    offer = copy.deepcopy(old_offer)
    current = {'inventory':NEW_INV, 'inventory_sha256':digest(NEW_INV), 'mapped_ledger':ledger,
        'mapped_ledger_sha256':digest(ledger), 'mapped_promotions':promotions, 'mapped_promotions_sha256':digest(promotions),
        'candidate_builder':str(Path(__file__).relative_to(ROOT)),
        'candidate_builder_sha256':digest(str(Path(__file__).relative_to(ROOT)))}
    original_fields = {k:old_offer[k] for k in current}
    offer.update(current)
    offer['current52_identity_rebase']={'identity_sidecar':ref(side), 'identity_integrity':ref(integrity),
        'original_source51_reviewed_offer':ref(OLD_OFFER), 'original_source51_outer_fields':original_fields,
        'rebase_scope':'Only active inventory/candidate/builder pointers rebind. All semantic decisions/time/counts/source/evidence and historical source51 outer offer fields are preserved.'}
    reverse=copy.deepcopy(offer);reverse.pop('current52_identity_rebase');reverse.update(original_fields);assert reverse==old_offer
    write(BASE+'/applied-audit24-candidate-source52-additions-v1.json', offer)
    assert digest(OLD_OFFER)==OLD_OFFER_SHA and all(digest(k)==v for k,v in LIVE.items())
    print(json.dumps({'offer':ref(BASE+'/applied-audit24-candidate-source52-additions-v1.json'),'candidate':ref(ledger),'candidate_promotions':ref(promotions),'identity_sidecar':ref(side),'integrity':ref(integrity)}))
if __name__=='__main__': main()
