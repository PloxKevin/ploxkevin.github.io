"""Check explicit current44 identities of unchanged reviewed core literals.

All semantic decisions and original review times remain in immutable originals.
Only the separately recorded source/inventory pointer changes are normalized.
"""
import copy
import hashlib
import json
from pathlib import Path

MANIFEST = 'book/coverage/checks/core-source44-unchanged-review-identity-manifest-v1.json'
MANIFEST_SHA256 = '5ad03aa321b2a2fbaa3fd053f85dbb82681537d5a43884d1df362638e0e38c2a'
CONFIRMATION = 'book/coverage/checks/core-source44-unchanged-review-identity-independent-root-confirmation-v1.json'

def _manifest(root, sha):
    assert sha(MANIFEST) == MANIFEST_SHA256
    manifest = json.loads((root / MANIFEST).read_text())
    confirmation = json.loads((root / CONFIRMATION).read_text())
    assert confirmation['status'] == 'independent_exact_inventory_identity_rebase_confirmation_passed'
    assert confirmation['rebase_manifest'] == MANIFEST and confirmation['rebase_manifest_sha256'] == MANIFEST_SHA256
    assert confirmation['immutable_inventory_after'] == manifest['immutable_inventory_after']
    assert confirmation['immutable_inventory_after_sha256'] == manifest['immutable_inventory_after_sha256'] == sha('book/coverage/inventory.json')
    assert sha(manifest['immutable_inventory_after']) == manifest['immutable_inventory_after_sha256']
    return manifest

def verify_identity(root, review, review_path, sha):
    manifest = _manifest(root, sha)
    path = str(Path(review_path).relative_to(root))
    row = next(x for x in manifest['records'] if x['rebased_review'] == path)
    assert sha(path) == row['rebased_review_sha256']
    assert sha(row['original_review']) == row['original_review_sha256']
    normalized = copy.deepcopy(review)
    normalized.pop(row['provenance_field'])
    for change in reversed(row['changed_current_identity_fields']):
        obj = normalized
        for key in change['path'][:-1]:
            obj = obj[key]
        key = change['path'][-1]
        assert obj[key] == change['after']
        obj[key] = change['before']
    original = json.loads((root / row['original_review']).read_text())
    assert normalized == original
    assert review.get('reviewed_at_utc') == original.get('reviewed_at_utc')
    return CONFIRMATION

def current_review(root, path, sha):
    path = Path(path)
    manifest = _manifest(root, sha)
    relative = str(path.relative_to(root))
    target = manifest['review_path_aliases'].get(relative)
    if target is None:
        return path
    selected = root / target
    verify_identity(root, json.loads(selected.read_text()), selected, sha)
    return selected

def verify_overlap_parent(root, record, owner, sha):
    """Retain the old exact parent hash while checking identical mathematics."""
    manifest = _manifest(root, sha)
    name = manifest['immutable_source33_core_ledger']
    assert sha(name) == manifest['immutable_source33_core_ledger_sha256']
    original = next(e for e in json.loads((root / name).read_text())['exercises'] if e['inventory_key'] == owner['inventory_key'])
    actual_old_hash = hashlib.sha256(json.dumps(original['claims'], sort_keys=True).encode()).hexdigest()
    assert actual_old_hash == record['reviewed_parent_claims_sha256']
    def semantic(value):
        if isinstance(value, dict):
            return {k: semantic(v) for k, v in value.items() if k not in {'source_review', 'independent_review'}}
        if isinstance(value, list):
            return [semantic(v) for v in value]
        return value
    assert semantic(owner['claims']) == semantic(original['claims'])
    return True
