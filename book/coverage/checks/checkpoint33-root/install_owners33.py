"""Install four exact independently reviewed Source88 owner candidates."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[4]
OUT = 'reports/full-coverage/owner33-integration-v1.json'
HISTORY = 'reports/full-coverage/source-history/owners32-before-checkpoint33-v1'
BINDING = 'book/coverage/checks/checkpoint33-ledgers/owner-candidate-binding-v2.json'

def path(n):
    assert isinstance(n, str) and n and not Path(n).is_absolute()
    assert not {'..', '.git', '.lake'}.intersection(Path(n).parts)
    p = ROOT / n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p

def read(n): return json.loads(path(n).read_bytes())
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n): return dict(file=n, sha256=sha(n))
def exact(r):
    assert sha(r['file']) == r['sha256'], r['file']
    return read(r['file'])

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--peer', required=True)
ap.add_argument('--peer-sha256', required=True)
args = ap.parse_args()
assert not path(OUT).exists() and not path(HISTORY).exists()
peer_ref = dict(file=args.peer, sha256=args.peer_sha256)
peer = exact(peer_ref)
assert peer['status'].startswith('passed') and peer.get('errors', []) == []
binding = read(BINDING)
assert binding['status'] == 'prepared_isolated_four_owner_candidates_for_root_independent_review'
assert binding['whole_material_promotions'] == 10
assert binding['exercise_status_or_statement_changes'] == 0
assert binding['historical_review_and_native_artifact_bytes_rewritten'] == 0
assert binding['mathematical_correspondence_broken_by_changed_ancestors'] == []
assert binding['candidate_installation_performed'] is False
assert sha('book/coverage/inventory.json') == binding['inventory']['sha256']
replacements = binding['replacements']
assert len(replacements) == 4
assert {r['destination'] for r in replacements} == {
    'book/coverage/foundations.json', 'book/coverage/applied.json',
    'book/coverage/modules.json', 'book/coverage/core.json'}

def contains(d, h):
    if isinstance(d, dict): return any(contains(v, h) for v in d.values())
    if isinstance(d, list): return any(contains(v, h) for v in d)
    return d == h

for r in replacements:
    before, candidate = exact(r['before']), exact(r['candidate'])
    exact(r['exact_inverse'])
    assert contains(peer, r['candidate']['sha256'])
    # Only current source fingerprints in exercises may rebase. Their actual
    # statements, statuses, subclaims and historical reviews must be retained.
    assert len(before['exercises']) == len(candidate['exercises'])
    for a, b in zip(before['exercises'], candidate['exercises']):
        assert {k:v for k,v in a.items() if k != 'source_sha256'} == {
            k:v for k,v in b.items() if k != 'source_sha256'}
protected = {n:r['sha256'] for n,r in read('reports/full-coverage/checkpoint-33-selection.json')['proof_files'].items()}
protected.update(read('book/coverage/inventory.json')['source_sha256'])
for n in ['book/coverage/applied-promotions.json', 'book/coverage/material-corrections.json', 'book/coverage/inventory.json']:
    protected[n] = sha(n)
assert all(sha(n) == h for n,h in protected.items())
for r in replacements:
    original = HISTORY + '/' + Path(r['destination']).name
    path(original).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(path(r['destination']), path(original))
    assert sha(original) == r['before']['sha256']
    r['preserved_original'] = ref(original)
    r['independent_mapping_peer'] = peer_ref
for r in replacements:
    shutil.copyfile(path(r['candidate']['file']), path(r['destination']))
    assert sha(r['destination']) == r['candidate']['sha256']
assert all(sha(n) == h for n,h in protected.items())
record = dict(status='four_exact_independently_reviewed_source88_owner_candidates_installed',
    applied=True, installed_at_utc=datetime.now(timezone.utc).isoformat(),
    exact_replacements=replacements, owner_candidate_binding=ref(BINDING), independent_peer=peer_ref,
    whole_material_units_completed=10, new_canonical_files=7, new_public_theorems=78,
    exercises_completed=0, node922_whole_remains_pending=True,
    selected_source_and_current_site_protected=True, coverage_complete=False,
    aggregate_or_kernel_or_publication_claimed=False)
with path(OUT).open('x') as f: f.write(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(status=record['status'], record=ref(OUT))))
