"""Prepare explicit pointer-only versions of unchanged core source44 reviews."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
def read(name):
    return json.loads((ROOT / name).read_text())
def write(name, value):
    path = ROOT / name
    assert not path.exists(), name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')

OLD_MANIFEST = 'book/coverage/checks/core-source44-unchanged-review-identity-manifest-v2.json'
old_manifest = read(OLD_MANIFEST)
old_name = 'book/coverage/inventory-after-correction44.json'
new_name = 'book/coverage/inventory-after-correction47.json'
old_inv, new_inv = read(old_name), read(new_name)
assert sha(new_name) == sha('book/coverage/inventory.json') == 'ab2b27355004f545180b00ca1c1d5243aeb88683100d6ca747e3054987bbf0c2'
old_units = {u['key']: u for section in ('exercises', 'material_source_units') for u in old_inv[section]}
new_units = {u['key']: u for section in ('exercises', 'material_source_units') for u in new_inv[section]}
original_labels = '/tmp/core-instructional-label-material-batch2-source44-independent-applied-review20-v2.json'
labels = 'book/coverage/checks/future20-core/core-instructional-label-material-batch2-source44-independent-applied-review20-v2.json'
assert hashlib.sha256(Path(original_labels).read_bytes()).hexdigest() == '846672544a4ed5f2b5284315251e46809fe8d1cbf65ea51d583891dd89a139e8'
if not (ROOT / labels).exists():
    (ROOT / labels).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / labels).write_bytes(Path(original_labels).read_bytes())
assert sha(labels) == '846672544a4ed5f2b5284315251e46809fe8d1cbf65ea51d583891dd89a139e8'
rows = [(r['rebased_review'], r['kind']) for r in old_manifest['records']]
rows += [(f'book/coverage/checks/{name}', 'unchanged_semantic_review_identity') for name in (
    'policy-cpo-9-2-corrected44-whole-source-review19-v1.json',
    'policy-penalty-barrier-9-4-corrected44-whole-source-review19-v1.json',
    'policy-benchmark-9-5-corrected44-whole-source-review19-v1.json')]
rows += [('book/coverage/core-instructional-label-material-candidates-20-batch2-source44.json', 'unchanged_candidate_identity'),
         (labels, 'unchanged_semantic_review_identity')]
assert len(rows) == 47 and len(set(name for name, _ in rows)) == 47
targets = {name: str(Path(name).with_name(Path(name).stem + '-source47-identity20-v1.json')) for name, _ in rows}
records, identities, aliases = [], {}, {}
prepared_at = datetime.now(timezone.utc).isoformat()

for name, kind in sorted(rows, key=lambda row: row[1] != 'unchanged_candidate_identity'):
    original = read(name)
    current = copy.deepcopy(original)
    changes = []
    def change(path, after):
        value = current
        for key in path[:-1]:
            value = value[key]
        key = path[-1]
        before = value[key]
        if before != after:
            changes.append(dict(path=path, before=copy.deepcopy(before), after=copy.deepcopy(after)))
            value[key] = after
    def literal_check(row):
        key = row.get('source_unit_key', row.get('exercise_key'))
        if key not in old_units:
            return
        old, new = old_units[key], new_units[key]
        for field in ('source', 'source_text', 'text_sha256', 'line', 'locator'):
            assert old.get(field) == new.get(field), (name, key, field)
        for field, actual in (('unit_text_sha256', 'text_sha256'), ('exercise_text_sha256', 'text_sha256'), ('source_text', 'source_text'), ('exercise_text', 'source_text')):
            if field in row and ((field.startswith('unit') or field == 'source_text') == ('source_unit_key' in row)):
                assert row[field] == new[actual], (name, key, field)
        identities[key] = dict(key=key, source=new['source'], text_sha256=new['text_sha256'], source_text=new['source_text'], line=new['line'], locator=new.get('locator'), source_sha256_before=old['source_sha256'], source_sha256_after=new['source_sha256'])
    for section in ('records', 'material_units'):
        for index, row in enumerate(current.get(section, [])):
            literal_check(row)
            key = row.get('source_unit_key', row.get('exercise_key'))
            if key in new_units and isinstance(row.get('source_sha256'), str):
                assert row['source_sha256'] == old_units[key]['source_sha256']
                change([section, index, 'source_sha256'], new_units[key]['source_sha256'])
    if 'inventory' in current:
        assert current['inventory'] in {'book/coverage/inventory.json', old_name}
        change(['inventory'], new_name)
    if 'inventory_sha256' in current:
        assert current['inventory_sha256'] == sha(old_name)
        change(['inventory_sha256'], sha(new_name))
    if isinstance(current.get('source_sha256'), dict):
        for source, expected in current['source_sha256'].items():
            assert expected == old_inv['source_sha256'][source], (name, source)
            change(['source_sha256', source], new_inv['source_sha256'][source])
    elif isinstance(current.get('source_sha256'), str):
        source = current.get('source')
        assert source in old_inv['source_sha256'] and current['source_sha256'] == old_inv['source_sha256'][source]
        change(['source_sha256'], new_inv['source_sha256'][source])
    for pointer, digest in (('candidate_manifest', 'candidate_manifest_sha256'), ('candidate_source', 'candidate_sha256'), ('candidate', 'candidate_sha256')):
        if pointer in current and current[pointer] in targets:
            assert sha(current[pointer]) == current[digest]
            change([pointer], targets[current[pointer]])
            change([digest], sha(current[pointer]))
    provenance = 'source47_identity_provenance'
    assert provenance not in current
    current[provenance] = dict(original_review=name, original_review_sha256=sha(name), identity_prepared_by='/root', identity_prepared_at_utc=prepared_at, semantic_review_time_unchanged=True, only_recorded_current_identity_fields_changed=True)
    restored = copy.deepcopy(current)
    restored.pop(provenance)
    for delta in reversed(changes):
        value = restored
        for key in delta['path'][:-1]:
            value = value[key]
        assert value[delta['path'][-1]] == delta['after']
        value[delta['path'][-1]] = delta['before']
    assert restored == original and current.get('reviewed_at_utc') == original.get('reviewed_at_utc')
    target = targets[name]
    write(target, current)
    records.append(dict(original_review=name, original_review_sha256=sha(name), rebased_review=target, rebased_review_sha256=sha(target), kind=kind, changed_current_identity_fields=changes, provenance_field=provenance))
    aliases[name] = target
for alias, old_target in {**old_manifest['review_path_aliases'], **old_manifest.get('candidate_path_aliases', {})}.items():
    assert old_target in targets
    aliases[alias] = targets[old_target]
manifest = dict(schema_version=1, status='prepared_exact_unchanged_core_review_identity_versions_awaiting_independent_confirmation', prepared_by='/root', prepared_at_utc=prepared_at,
    immutable_inventory_before=old_name, immutable_inventory_before_sha256=sha(old_name), immutable_inventory_after=new_name, immutable_inventory_after_sha256=sha(new_name),
    prior_identity_manifest=OLD_MANIFEST, prior_identity_manifest_sha256=sha(OLD_MANIFEST), records=records, review_path_aliases=aliases, literal_identity_records=list(identities.values()),
    immutable_source33_core_ledger=old_manifest['immutable_source33_core_ledger'], immutable_source33_core_ledger_sha256=old_manifest['immutable_source33_core_ledger_sha256'],
    changed_exercise_keys_excluded=['policy-optimization.html::exercise-18','cmdp.html::exercise-20'], changed_material_keys_excluded=['policy-optimization.html::node-1449','cmdp.html::node-1129'],
    limits=['Exact identities of unchanged literals only. No new semantic decision or compiler success.', 'All original review bodies and review times are preserved. The two corrected whole exercises require fresh current47 reviews.'])
name = 'book/coverage/checks/core-source47-unchanged-review-identity-manifest20-v1.json'
write(name, manifest)
print(json.dumps(dict(status=manifest['status'], manifest=name, manifest_sha256=sha(name), records=len(records), distinct_unchanged_literals=len(identities))))
