"""Bind the unchanged Applied source44 decisions to the current source47 inventory."""
from pathlib import Path
import copy
import datetime
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
IDENTITY = 'book/coverage/checks/applied-source47-owner-identity20-v1.json'
IDENTITY_SHA = '562c8032b7cc35b1602b92103b0bea48d8c54d930fb2d5504c3e82efdb85aa89'
PEER = 'book/coverage/checks/applied-source47-owner-identity20-independent-foundations-confirmation-v1.json'
PEER_SHA = 'e7fa54bfd4903dbd512f5f96b795635c767fb8d5253733996cb2e14aa43cc9cf'
INVENTORY = 'book/coverage/inventory-after-correction47.json'
INVENTORY_SHA = 'ab2b27355004f545180b00ca1c1d5243aeb88683100d6ca747e3054987bbf0c2'

def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT / name).read_text())

def build():
    assert sha(IDENTITY) == IDENTITY_SHA and sha(PEER) == PEER_SHA
    assert sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    identity = read(IDENTITY)
    inv = read(INVENTORY)
    pages = set(identity['source_sha256'])
    assert [e for e in inv['exercises'] if e['source'] in pages] == identity['exact_current_owned_exercise_records']
    assert [u for u in inv['material_source_units'] if u['source'] in pages] == identity['exact_current_owned_material_records']
    for source, expected in identity['source_sha256'].items():
        assert sha(source) == inv['source_sha256'][source] == expected
    for source, expected in identity['proof_source_sha256'].items():
        assert sha(source) == expected
    baseline = identity['preserved_source44_owned_metadata']
    for item in baseline:
        assert sha(item['preserved_history']) == item['sha256']
    provenance = {
        'inventory': INVENTORY,
        'inventory_sha256': INVENTORY_SHA,
        'unchanged_owner_identity': IDENTITY,
        'unchanged_owner_identity_sha256': IDENTITY_SHA,
        'independent_identity_confirmation': PEER,
        'independent_identity_confirmation_sha256': PEER_SHA,
        'exact_unchanged_exercise_inventory_records': 128,
        'exact_unchanged_material_inventory_records': 2059,
        'changed_owned_literal_keys': [],
        'scope': 'All source44 mathematical decisions, review times, component gaps and actual compiler evidence remain unchanged. This field records only the independently confirmed current source47 inventory identity.'
    }
    for item in baseline[:2]:
        old = read(item['preserved_history'])
        current = read(item['original'])
        normalized = copy.deepcopy(current)
        normalized.pop('current47_owner_identity', None)
        assert normalized == old, item['original']
        out = copy.deepcopy(old)
        out['current47_owner_identity'] = provenance
        (ROOT / item['original']).write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'status': 'passed_exact_identity_only_binding', 'counts': read(baseline[0]['original'])['counts'], 'ledger_sha256': sha(baseline[0]['original']), 'promotions_sha256': sha(baseline[1]['original'])}))

if __name__ == '__main__':
    build()
