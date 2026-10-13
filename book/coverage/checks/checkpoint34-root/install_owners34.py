"""Install the exact reviewed Source90 ledgers, resuming interrupted copies.

All originals are preserved before the first replacement. Each replacement and
the final receipt use an atomic rename; reruns accept only original or reviewed
candidate hashes. Existing receipts are checked rather than rewritten.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import copy
import hashlib
import json
import os
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BINDING = 'book/coverage/checks/checkpoint34-ledgers/owner-candidate-binding-v3.json'
PEER = 'book/coverage/checks/checkpoint34-review/independent-four-owner34-candidates-review-v3.json'
OUT = 'reports/full-coverage/owner34-integration-v1.json'
HISTORY = 'reports/full-coverage/source-history/owners33-before-checkpoint34-v1'


def path(name):
    p = Path(name)
    assert not p.is_absolute() and p.as_posix() == name
    assert not {'..', '.git', '.lake'}.intersection(p.parts)
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not parent.is_symlink() for parent in p.parents if parent.is_relative_to(ROOT))
    return p


def sha(name):
    with path(name).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def ref(name):
    return {'file': name, 'sha256': sha(name)}


def read(name):
    return json.loads(path(name).read_bytes())


def exact(row):
    assert sha(row['file']) == row['sha256'], row['file']
    if 'bytes' in row:
        assert path(row['file']).stat().st_size == row['bytes']
    return path(row['file'])


def atomic(name, data):
    p = path(name)
    p.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temporary, p)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def restore(candidate, patches):
    document = copy.deepcopy(candidate)
    for patch in reversed(patches):
        parent = document
        for key in patch['pointer'][:-1]:
            parent = parent[key]
        key = patch['pointer'][-1]
        if patch['after_exists']:
            assert parent[key] == patch['after']
        else:
            assert key not in parent
        if patch['before_exists']:
            parent[key] = copy.deepcopy(patch['before'])
        elif isinstance(parent, list):
            assert key == len(parent) - 1
            parent.pop()
        else:
            del parent[key]
    return document


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binding-sha256', required=True)
    parser.add_argument('--peer-sha256', required=True)
    args = parser.parse_args()
    assert sha(BINDING) == args.binding_sha256
    assert sha(PEER) == args.peer_sha256
    binding, peer = read(BINDING), read(PEER)
    assert peer['status'].startswith('approved_independent_four_Source90_owner34_v3')
    assert peer['errors'] == [] and peer['binding'] == {**ref(BINDING), 'bytes': path(BINDING).stat().st_size}
    assert binding['whole_material_promotions'] == peer['new_whole_material_promotions'] == 7
    assert binding['exercise_status_changes'] == 2
    assert binding['historical_evidence_rewritten'] == 0
    assert binding['changed_ancestors_without_independent_approval'] == []
    assert sha('book/coverage/inventory.json') == binding['inventory']['sha256']
    destinations = {r['destination'] for r in binding['replacements']}
    assert destinations == {'book/coverage/' + n + '.json' for n in ['foundations', 'applied', 'modules', 'core']}
    assert len(binding['replacements']) == 4
    protected = {n: h for n, h in binding['protected_input_sha256'].items() if n not in destinations}
    assert all(sha(n) == h for n, h in protected.items())
    decisions = {r['before']['file']: r for r in peer['owner_decisions']}
    replacements = []
    for r in binding['replacements']:
        decision = decisions[r['destination']]
        assert all(r[k] == decision[k] for k in ['before', 'candidate', 'exact_inverse'])
        candidate_path = exact(r['candidate'])
        inverse = json.loads(exact(r['exact_inverse']).read_bytes())
        assert inverse['baseline'] == r['before'] and inverse['candidate'] == r['candidate']
        original = encode(restore(json.loads(candidate_path.read_bytes()), inverse['patches']))
        assert hashlib.sha256(original).hexdigest() == r['before']['sha256']
        history_name = HISTORY + '/' + Path(r['destination']).name
        current = sha(r['destination'])
        assert current in {r['before']['sha256'], r['candidate']['sha256']}, r['destination']
        if path(history_name).exists():
            assert sha(history_name) == r['before']['sha256']
        else:
            # A resumed candidate requires the genuinely saved original, rather
            # than reconstructing and claiming a new original copy.
            assert current == r['before']['sha256']
            atomic(history_name, path(r['destination']).read_bytes())
        assert path(history_name).read_bytes() == original
        replacements.append({**r, 'preserved_original': ref(history_name), 'independent_mapping_peer': ref(PEER), 'applied': True})
    if path(OUT).exists():
        receipt = read(OUT)
        assert receipt['owner_candidate_binding'] == ref(BINDING)
        assert receipt['independent_peer'] == ref(PEER)
        assert receipt['exact_replacements'] == replacements
        assert all(sha(r['destination']) == r['candidate']['sha256'] for r in replacements)
        print(json.dumps({'status': 'passed_existing_exact_installation_receipt', 'record': ref(OUT)}))
        return
    for r in replacements:
        if sha(r['destination']) != r['candidate']['sha256']:
            atomic(r['destination'], exact(r['candidate']).read_bytes())
        assert sha(r['destination']) == r['candidate']['sha256']
    assert all(sha(n) == h for n, h in protected.items())
    receipt = dict(status='four_exact_independently_reviewed_source90_owner_candidates_installed',
        applied=True, installed_at_utc=datetime.now(timezone.utc).isoformat(),
        exact_replacements=replacements, owner_candidate_binding=ref(BINDING), independent_peer=ref(PEER),
        whole_material_units_completed=7, new_canonical_files=3, new_public_theorems=114,
        exercises_completed=2, closed_exercises=peer['closed_exercises'],
        selected_source_and_current_site_protected=True, coverage_complete=False,
        aggregate_or_kernel_or_publication_claimed=False,
        restart_policy='Only exact original or approved candidate bytes accepted; all originals saved before atomic replacements.')
    atomic(OUT, encode(receipt))
    print(json.dumps({'status': receipt['status'], 'record': ref(OUT)}))


if __name__ == '__main__':
    main()
