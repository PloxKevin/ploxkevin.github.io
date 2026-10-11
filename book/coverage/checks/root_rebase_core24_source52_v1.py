"""Create an isolated inventory identity binding for unchanged Core24 literals."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
DEST = ROOT / 'book/coverage/checks/future24-core/source52'
OLD_OFFER = 'book/coverage/checks/future24-core/core-audit24-candidate-source51-material-additions-v1-reviewed.json'
OLD_CANDIDATE = 'book/coverage/checks/future24-core/core24-source51-material-candidate-v1.json'
SELF = 'book/coverage/checks/root_rebase_core24_source52_v1.py'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def ref(name): return {'file':name,'sha256':sha(ROOT/name)}
def write_new(path,data):
    with path.open('x') as output: output.write(json.dumps(data,indent=2)+'\n')

assert not DEST.exists()
assert sha(ROOT/OLD_OFFER) == '97e86bfdcbc4793534f52984e89780cf910f9509d8e015378a2f444dcdce734f'
assert sha(ROOT/OLD_CANDIDATE) == 'cdb5404870cae2f2d4ec28bc0a04721c65338fa080fd16b4346407bb0e0afb2e'
old_offer = read(OLD_OFFER)
old_candidate = read(OLD_CANDIDATE)
old_inventory = read('book/coverage/inventory-after-correction51.json')
new_inventory = read('book/coverage/inventory-after-correction52.json')
assert sha(ROOT/'book/coverage/inventory-after-correction51.json') == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert sha(ROOT/'book/coverage/inventory.json') == sha(ROOT/'book/coverage/inventory-after-correction52.json')
assert read('reports/full-coverage/source52-apply-execution-v1.json')['actual_exit_code'] == 0
post = read('book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json')
assert post['actual_exit_code'] == 0 and post['inventory_after_sha256'] == sha(ROOT/'book/coverage/inventory.json')
assert len(read('book/coverage/material-corrections.json')['corrections']) == 52
assert read('reports/full-coverage/live-checkpoint-23-attempt2.json')['status'] == 'passed_all31_asset_sha256'
assert old_inventory['counts'] == new_inventory['counts']
pages = set(old_candidate['scope_pages'])
assert 'SafeLearning/nn-in-the-loop.html' not in pages and 'nn-in-the-loop.html' not in pages
literal_bindings = {}
for section in ['exercises','material_source_units']:
    before = {row['key']:row for row in old_inventory[section]}
    after = {row['key']:row for row in new_inventory[section]}
    assert before.keys() == after.keys()
    owned = {key:row for key,row in before.items() if row['source'] in old_candidate['source_sha256']}
    assert owned and all(row == after[key] for key,row in owned.items())
    literal_bindings[section] = {key:row['text_sha256'] for key,row in owned.items()}
for name,digest in old_candidate['source_sha256'].items():
    assert sha(ROOT/name) == digest
guards = {name:sha(ROOT/name) for name in ['book/coverage/core.json','book/coverage/foundations.json',
    'book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
assert guards['book/coverage/core.json'] == '1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a'
manifest = read('reports/full-coverage/checkpoint-23-manifest.json')
assert len(manifest['proof_files']) == 1131
assert all(sha(ROOT/name) == row['sha256'] for name,row in manifest['proof_files'].items())
for name,row in old_offer['proof_files'].items(): assert sha(ROOT/name) == row['sha256']
DEST.mkdir(parents=True)
identity = {'status':'passed_exact_unchanged_owned_literals_source51_to_source52_identity_only',
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),'prepared_by':'/root',
    'helper':ref(SELF),'original_reviewed_offer':ref(OLD_OFFER),'original_candidate':ref(OLD_CANDIDATE),
    'old_inventory':ref('book/coverage/inventory-after-correction51.json'),
    'current_inventory':ref('book/coverage/inventory-after-correction52.json'),
    'actual_source52_apply':ref('reports/full-coverage/source52-apply-execution-v1.json'),
    'actual_source52_postwrite':ref('book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'),
    'exact_owned_inventory_literal_sha256':literal_bindings,'all_owned_inventory_rows_exact':True,
    'all1131_selected23_sources_exact':True,'held_live_owner_sha256':guards,
    'scope':'Inventory identity only. Original exercise/material/proof records and semantic reviews remain unchanged.'}
identity_path = DEST/'core24-source51-to-source52-identity-v1.json'
write_new(identity_path,identity)
candidate = copy.deepcopy(old_candidate)
candidate.update(current_inventory='book/coverage/inventory-after-correction52.json',
    current_inventory_sha256=sha(ROOT/'book/coverage/inventory-after-correction52.json'))
candidate['source52_core_identity_binding'] = ref(identity_path.relative_to(ROOT).as_posix())
inverse = copy.deepcopy(candidate)
inverse.pop('source52_core_identity_binding')
inverse['current_inventory'] = old_candidate['current_inventory']
inverse['current_inventory_sha256'] = old_candidate['current_inventory_sha256']
assert inverse == old_candidate
candidate_path = DEST/'core24-source52-material-candidate-v1.json'
write_new(candidate_path,candidate)
offer = copy.deepcopy(old_offer)
offer.update(prepared_at_utc=datetime.now(timezone.utc).isoformat(),
    candidate_ledger=ref(candidate_path.relative_to(ROOT).as_posix()),
    inventory='book/coverage/inventory-after-correction52.json',
    inventory_sha256=sha(ROOT/'book/coverage/inventory-after-correction52.json'))
offer['source52_identity'] = ref(identity_path.relative_to(ROOT).as_posix())
offer['original_source51_reviewed_offer'] = ref(OLD_OFFER)
offer['entire_original_source51_offer_body_and_time'] = old_offer
offer['final_independent_source52_identity_peer_pending'] = True
offer_path = DEST/'core-audit24-candidate-source52-material-additions-v1.json'
write_new(offer_path,offer)
assert all(sha(ROOT/name) == digest for name,digest in guards.items())
assert all(sha(ROOT/name) == row['sha256'] for name,row in manifest['proof_files'].items())
assert sha(ROOT/OLD_CANDIDATE) == 'cdb5404870cae2f2d4ec28bc0a04721c65338fa080fd16b4346407bb0e0afb2e'
print(json.dumps({'status':'passed_isolated_unchanged_literal_identity_only','candidate':ref(candidate_path.relative_to(ROOT).as_posix()),
    'offer':ref(offer_path.relative_to(ROOT).as_posix()),'coverage_complete':False}))
