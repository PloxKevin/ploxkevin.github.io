"""Unexecuted isolated identity draft. Run only after Root's actual source52 release.

Preserve every source51 candidate, review, theorem and compiler record. New paths
contain only an active inventory identity overlay and its reversible offer delta.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json

ROOT = Path(__file__).resolve().parents[2]
BASE = 'book/coverage/checks/foundations-future24/source52'
OLD_OFFER = 'book/coverage/checks/foundations-future24/source51/foundations-audit24-candidate-source51-additions-v1-reviewed.json'
OLD_OFFER_SHA = 'c939f72d7ed32eb76016788ce8c0aabcf244c2334753a2f9564b08cfc3168b26'
OLD_CANDIDATE_SHA = '3446fbfe7889cdfa8c8dff485ce03f223b6662478e3d4599cd1d1850bbb7f2c9'
OLD_INV = 'book/coverage/inventory-after-correction51.json'
OLD_INV_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
NEW_INV = 'book/coverage/inventory-after-correction52.json'
MANIFEST = 'reports/full-coverage/checkpoint-23-manifest.json'
MANIFEST_SHA = 'e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06'
OWNER_PATHS = ['book/coverage/'+n+'.json' for n in ['core','foundations','applied','modules','applied-promotions']]

def digest(name): return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def ref(name): return {'file':str(name), 'sha256':digest(name)}
def write(name, body):
    p = ROOT/name
    assert not p.exists(), name
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('x') as f: f.write(json.dumps(body, indent=2, ensure_ascii=False)+'\n')

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--inventory-sha256', required=True)
    parser.add_argument('--root-authorized-source52-identity-rebase', action='store_true', required=True)
    args = parser.parse_args()
    assert args.root_authorized_source52_identity_rebase
    assert len(args.inventory_sha256)==64 and all(c in '0123456789abcdef' for c in args.inventory_sha256)
    assert digest(NEW_INV)==digest('book/coverage/inventory.json')==args.inventory_sha256
    apply_path = 'reports/full-coverage/source52-apply-execution-v1.json'
    post_path = 'book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'
    actual, post = read(apply_path), read(post_path)
    assert actual['actual_exit_code']==post['actual_exit_code']==0
    assert digest(actual['log'])==actual['log_sha256']
    assert post['inventory_after']==NEW_INV and post['inventory_after_sha256']==args.inventory_sha256
    assert digest('book/coverage/material-corrections.json')==post['registry_after_sha256']
    assert len(read('book/coverage/material-corrections.json')['corrections'])==52
    assert digest(MANIFEST)==MANIFEST_SHA and digest(OLD_OFFER)==OLD_OFFER_SHA and digest(OLD_INV)==OLD_INV_SHA
    manifest = read(MANIFEST)
    assert len(manifest['proof_files'])==1131
    held = {n:manifest['working_inputs_sha256'][n] for n in OWNER_PATHS}
    for n,h in held.items(): assert digest(n)==h, n
    old_offer = read(OLD_OFFER)
    old_path = old_offer['mapped_ledger']
    assert digest(old_path)==old_offer['mapped_ledger_sha256']==OLD_CANDIDATE_SHA
    old = read(old_path)
    assert old_offer['new_proof_file_count']==5 and old_offer['new_theorem_or_lemma_count']==37
    assert old_offer['independent_final_candidate_mapping_peer_pending'] is False
    assert old_offer['independent_canonical_binding_peer_pending'] is False
    assert old_offer['actual_builder_record_pending'] is False
    scope = set(old['scope_pages'])
    assert len(scope)==3
    before, after = read(OLD_INV), read(NEW_INV)
    assert before['counts']==after['counts']
    records = {}
    for kind,count in [('exercises',119),('material_source_units',1756)]:
        a = [r for r in before[kind] if r['source'] in scope]
        b = [r for r in after[kind] if r['source'] in scope]
        assert len(a)==len(b)==count and a==b
        records[kind]=b
    assert old['source_sha256']==old_offer['source_sha256']
    for n,h in old['source_sha256'].items():
        assert digest(n)==h
        if n.startswith('SafeLearning/'):
            assert before['source_sha256'][n]==after['source_sha256'][n]==h
        else:
            assert read('book/coverage/foundations.json')['source_sha256'][n]==h
    assert len(old['exercises'])==119
    assert len(old['proof_files'])==243
    assert set(old['proof_files'])==set(old['proof_sha256'])
    for n,h in old['proof_sha256'].items(): assert digest(n)==h
    for n,row in manifest['proof_files'].items(): assert digest(n)==row['sha256']
    evidence = {}
    for n,row in old_offer['proof_files'].items():
        assert digest(n)==row['sha256']
        evidence.update(row['evidence_sha256'])
    for field in ['exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256']:
        evidence.update(old_offer[field])
    for n,h in evidence.items(): assert digest(n)==h
    for n in old_offer['actual_canonical_execution_records_sha256']:
        r=read(n)
        exits=[r[k] for k in ['exit_code','actual_exit_code'] if k in r]
        assert exits and all(x==0 for x in exits)
        assert digest(r['log'])==r['log_sha256']
        assert digest(r['source'])==r['source_sha256_before']==r['source_sha256_after']
    assert len(old_offer['actual_canonical_execution_records_sha256'])==10
    side=BASE+'/foundations24-source51-to52-unchanged-entire-owned-literal-identity-v1.json'
    candidate=BASE+'/foundations24-candidate-source52-identity-v1.json'
    integrity=BASE+'/source52-identity-preparation-integrity-v1.json'
    offer_path=BASE+'/foundations-audit24-candidate-source52-additions-draft-v1.json'
    assert not any((ROOT/n).exists() for n in [side,candidate,integrity,offer_path])
    failed_path=BASE+'/identity-builder-actual-execution-source52-v1.json'
    failed=read(failed_path)
    assert failed['actual_exit_code']==1 and digest(failed['raw_log'])==failed['raw_log_sha256']
    assert digest(failed['actual_helper'])==failed['actual_helper_sha256_before']==failed['actual_helper_sha256_after']
    assert digest(failed['actual_runner'])==failed['actual_runner_sha256']
    failed_history={'record':ref(failed_path),'entire_original_record_body_and_time':failed,'raw_log':ref(failed['raw_log']),'helper':ref(failed['actual_helper']),'runner':ref(failed['actual_runner']),'cause':'Original identity reader used dictionary items on proof_files although Foundation schema has a path list plus proof_sha256 mapping. Failed before new sidecar/candidate writes; v2 reads exact list/map without changing the original candidate.'}
    identity={'status':'exact_source51_to52_unchanged_foundation24_entire_owned_records',
        'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'historical_inventory':ref(OLD_INV),'current_inventory':ref(NEW_INV),
        'original_source51_reviewed_offer':ref(OLD_OFFER),'original_source51_candidate':ref(old_path),
        'preserved_first_identity_builder_failure':failed_history,
        'original_six_literal_interface':ref(old_offer['material24_exact_interface_binding']),
        'entire_owned_inventory_records':records,'owned_source_sha256':old['source_sha256'],
        'actual_root_source52_apply':ref(apply_path),'actual_root_source52_postwrite':ref(post_path),
        'counts':{'owned_exercises':119,'owned_physical_units':1756,'whole_material_units_retained':6,'new_sources_retained':5,'public_exports_retained':37,'actual_compiler_records_retained':10},
        'original_full_semantic_bodies_hypotheses_decisions_times_and_compiler_evidence_unchanged':True,
        'limits':['Source52 modifies a different owner page. Every Foundation entire literal record is equal to source51.',
            'This is an inventory identity delta. Original six whole mathematical decisions, exact hypotheses and reviewer times remain unchanged.',
            'All five paired sources37 exports retain genuine original compiler evidence; no new compiler, live installation or aggregate24 result is inferred.']}
    write(side,identity)
    overlay={'inventory':ref(NEW_INV),'identity_sidecar':ref(side),'original_source51_reviewed_offer':ref(OLD_OFFER),
        'scope':'Active source52 identity only; the entire original source51 candidate and its semantic/proof/history bodies remain exact.'}
    current=copy.deepcopy(old)
    assert 'current52_owner_identity' not in current
    current['current52_owner_identity']=overlay
    reverse=copy.deepcopy(current);reverse.pop('current52_owner_identity');assert reverse==old
    write(candidate,current)
    write(integrity,{'status':'passed_actual_isolated_foundation24_source52_identity_preparation','checked_at_utc':datetime.now(timezone.utc).isoformat(),
        'candidate_ledger':ref(candidate),'identity_sidecar':ref(side),'original_source51_reviewed_offer':ref(OLD_OFFER),
        'exact_inverse_restores_entire_source51_candidate':True,'all119_and1756_entire_inventory_records_exact':True,
        'all1131_selected23_and243_candidate_sources_exact':True,'all10_original_compiler_records_and_raw_logs_exact':True,
        'all_original_semantic_bodies_review_times_and_claims_exact':True,'all_five_live23_owner_sha256':held,'errors':[],
        'scope':'Genuine isolated inventory identity preparation only. No mathematical redecision, compiler rerun, live owner installation or aggregate24 status.'})
    out=copy.deepcopy(old_offer)
    fields={'status':'isolated_source52_identity_foundation24_candidate_pending_independent_identity_delta_peer',
        'mapped_ledger':candidate,'mapped_ledger_sha256':digest(candidate),'current_inventory':NEW_INV,'current_inventory_sha256':digest(NEW_INV),
        'current_owner_builder':str(Path(__file__).relative_to(ROOT)),'current_owner_builder_sha256':digest(str(Path(__file__).relative_to(ROOT)))}
    originals={k:old_offer[k] for k in fields}
    out.update(fields)
    out['current52_identity_rebase']={'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'identity_sidecar':ref(side),'integrity':ref(integrity),
        'original_source51_reviewed_offer':ref(OLD_OFFER),'original_source51_outer_fields':originals,
        'actual_identity_builder_record_pending':True,'independent_source52_identity_delta_peer_pending':True,
        'original_source51_candidate_builder_and_peer_remain_historical':True,
        'scope':'Only active status/inventory/candidate/builder pointers and this new identity record change. Original outer prepared_at_utc and every semantic time/body/count/source/evidence remain exact.'}
    inverse=copy.deepcopy(out);inverse.pop('current52_identity_rebase');inverse.update(originals);assert inverse==old_offer
    write(offer_path,out)
    assert digest(OLD_OFFER)==OLD_OFFER_SHA and digest(old_path)==OLD_CANDIDATE_SHA
    for n,h in held.items():assert digest(n)==h
    for n,h in evidence.items():assert digest(n)==h
    print(json.dumps({'status':'passed_isolated_foundation_source52_identity_preparation','candidate':ref(candidate),'identity':ref(side),'integrity':ref(integrity),'draft_offer':ref(offer_path)}))

if __name__=='__main__':main()
