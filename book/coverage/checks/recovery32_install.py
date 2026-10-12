"""Install three exact reviewed owner candidates, preserving original ledgers."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[3]
OUT = 'reports/full-coverage/owner32-recovery-integration-v1.json'
HISTORY = 'reports/full-coverage/source-history/owner31-before-recovery32-v1'
PEER = 'book/coverage/checks/recovery32-review/six-whole-material-candidate32-independent-review-v1.json'
CORE = 'book/coverage/checks/recovery32-core/polygonal14-component-v1/polygonal14-readiness-v2.json'


def read(n):
    return json.loads((ROOT / n).read_bytes())


def ref(n):
    return dict(file=n, sha256=hashlib.sha256((ROOT / n).read_bytes()).hexdigest())


def exact(r):
    assert not Path(r['file']).is_absolute() and '..' not in Path(r['file']).parts
    assert ref(r['file'])['sha256'] == r['sha256']
    return read(r['file'])


assert not (ROOT / OUT).exists() and not (ROOT / HISTORY).exists()
assert ref(PEER)['sha256'] == 'edab1cef3d3acd26101c00947f0a77191dc44f41cd4f0d61e6b33192f6a774bf'
peer = read(PEER)
assert peer['status'].startswith('passed') and peer['errors'] == []
assert peer['changed_whole_material_units'] == 6 and peer['exact_inverse_all_other_fields_and_all_exercises_preserved'] is True
replacements = []
for r in peer['owner_candidate_reviews']:
    baseline, candidate = exact(r['baseline']), exact(r['candidate'])
    assert r['exact_inverse_to_baseline'] is True and r['unchanged_all_exercises_and_other_material_claims'] is True
    assert baseline['exercises'] == candidate['exercises']
    replacements.append(dict(destination=r['baseline']['file'], before=r['baseline'], candidate=r['candidate'], independent_mapping_peer=ref(PEER)))
core = read(CORE)
assert core['status'].startswith('passed') and core['errors'] == [] and core['public_theorem_count'] == 14
candidate = exact(core['candidate'])
baseline = read('book/coverage/core.json')
assert baseline['material_claims'] == candidate['material_claims']
changed_exercises = [(a, b) for a, b in zip(baseline['exercises'], candidate['exercises']) if a != b]
assert len(changed_exercises) == 1
a, b = changed_exercises[0]
assert a['inventory_key'] == b['inventory_key'] == 'barriers.html::exercise-16'
assert a['status'] == b['status'] == 'partial' and b['claims'][:-1] == a['claims']
assert {k: v for k, v in a.items() if k != 'claims'} == {k: v for k, v in b.items() if k != 'claims'}
claim = b['claims'][-1]
assert claim['source_review']['whole_exercise_or_enclosing_material_approved'] is False
assert claim['status'] == 'proved' and claim['remaining_gaps'] == []
math_peer = exact(core['original_math_peer'])
assert math_peer['all14_components_mathematically_approved'] is True
assert math_peer['current_whole_Exercise16_or_generic_Filippov_existence_approved'] is False
assert candidate['counts']['proof_files'] == baseline['counts']['proof_files'] + 1
replacements.append(dict(destination='book/coverage/core.json', before=ref('book/coverage/core.json'), candidate=core['candidate'], independent_mapping_peer=core['original_math_peer'], root_review=dict(full14_proof_bodies_and_two_definitions_read=True, exact_source_correspondence_component_only=True, global_pointwise_bound_explicit=True, whole_exercise_and_all_material_rows_preserved=True)))
selection = read('reports/full-coverage/checkpoint-32-selection.json')
protected = {n: r['sha256'] for n, r in selection['proof_files'].items()}
protected.update(read('book/coverage/inventory.json')['source_sha256'])
protected['book/coverage/modules.json'] = ref('book/coverage/modules.json')['sha256']
protected['book/coverage/applied-promotions.json'] = ref('book/coverage/applied-promotions.json')['sha256']
assert all(ref(n)['sha256'] == h for n, h in protected.items())
for r in replacements:
    exact(r['before']); exact(r['candidate'])
for r in replacements:
    n = HISTORY + '/' + Path(r['destination']).name
    p = ROOT / n
    p.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / r['destination'], p)
    assert ref(n)['sha256'] == r['before']['sha256']
    r['preserved_original'] = ref(n)
for r in replacements:
    shutil.copyfile(ROOT / r['candidate']['file'], ROOT / r['destination'])
    assert ref(r['destination'])['sha256'] == r['candidate']['sha256']
assert all(ref(n)['sha256'] == h for n, h in protected.items())
record = dict(status='three_exact_reviewed_owner32_candidates_installed', applied=True,
              installed_at_utc=datetime.now(timezone.utc).isoformat(), exact_replacements=replacements,
              whole_material_units_completed=6, new_canonical_files=6, new_public_theorems=83,
              selected_source_and_current_site_protected=True, coverage_complete=False,
              aggregate_or_kernel_or_publication_claimed=False)
with (ROOT / OUT).open('x') as f:
    f.write(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(status=record['status'], record=ref(OUT))))
