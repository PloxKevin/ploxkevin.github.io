"""Install only exact independently approved checkpoint35 owner candidates.

Original ledgers are retained by hash before the first replacement. Every
replacement is atomic. Interrupted stages accept only the approved before/after
bytes; completed stages verify the immutable installation receipt.
"""
import argparse
import json
import os
import tempfile
from prepare_runtime35 import ROOT, encode, exact, path, put, read, ref, sha

BINDING = 'book/coverage/checks/checkpoint35-ledgers/owner-candidate-binding-v1.json'
OUT = 'reports/full-coverage/owner35-integration-v1.json'


def atomic(name, data):
    p = path(name)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, p)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def restored(candidate, patches):
    for patch in reversed(patches):
        parent = candidate
        for part in patch['pointer'][:-1]:
            parent = parent[part]
        key = patch['pointer'][-1]
        assert parent[key] == patch['after']
        if patch['before_exists']:
            parent[key] = patch['before']
        elif isinstance(parent, list):
            assert key == len(parent) - 1
            parent.pop()
        else:
            del parent[key]
    return candidate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binding-sha256', required=True)
    parser.add_argument('--peer', action='append', required=True)
    parser.add_argument('--peer-sha256', action='append', required=True)
    args = parser.parse_args()
    exact({'file': BINDING, 'sha256': args.binding_sha256})
    assert len(args.peer) == len(args.peer_sha256) == 2
    binding = read(BINDING)
    peers = []
    covered = set()
    for n, fingerprint in zip(args.peer, args.peer_sha256):
        row = {'file': n, 'sha256': fingerprint}
        peer = json.loads(exact(row).read_bytes())
        assert peer['status'].startswith(('passed', 'approved')) and peer['errors'] == []
        assert peer['binding'] == ref(BINDING)
        covered.update(peer['approved_mapping_proposals'])
        peers.append(row)
    assert covered == {r['file'] for r in binding['mapping_proposals']}
    assert binding['coverage_complete'] is False
    assert {r['destination'] for r in binding['replacements']} == {'book/coverage/modules.json', 'book/coverage/core.json'}
    for n, h in binding['protected_input_sha256'].items():
        assert sha(n) == h, n
    replacements = []
    for row in binding['replacements']:
        candidate = exact(row['candidate'])
        original = exact(row['preserved_original'])
        inverse = json.loads(exact(row['exact_inverse']).read_bytes())
        assert inverse['baseline'] == row['before'] and inverse['candidate'] == row['candidate']
        assert restored(json.loads(candidate.read_bytes()), inverse['patches']) == json.loads(original.read_bytes())
        assert row['before']['sha256'] == row['preserved_original']['sha256']
        assert sha(row['destination']) in {row['before']['sha256'], row['candidate']['sha256']}
        replacements.append(row)
    result = {
        'status': 'passed_two_exact_independently_reviewed_checkpoint35_owner_candidates_installed',
        'applied': True, 'binding': ref(BINDING), 'independent_peers': peers,
        'exact_replacements': replacements, 'new_canonical_files': 3, 'new_public_theorems': 13,
        'exercises_completed': binding['exercises_completed'],
        'whole_material_units_completed': binding['whole_material_units_completed'],
        'refreshed_existing_material_units': binding['refreshed_existing_material_units'],
        'exercise_counts': binding['exercise_counts'], 'material_counts': binding['material_counts'],
        'coverage_complete': False, 'aggregate_or_kernel_or_publication_claimed': False,
        'restart_policy': 'Only exact original or independently approved candidate bytes are accepted.'}
    if path(OUT).exists():
        assert read(OUT) == result
        assert all(sha(r['destination']) == r['candidate']['sha256'] for r in replacements)
        print(json.dumps({'status': 'passed_existing_exact_installation_receipt', 'record': ref(OUT)}))
        return
    for row in replacements:
        if sha(row['destination']) != row['candidate']['sha256']:
            atomic(row['destination'], exact(row['candidate']).read_bytes())
        assert sha(row['destination']) == row['candidate']['sha256']
    for n, h in binding['protected_input_sha256'].items():
        assert sha(n) == h
    put(OUT, encode(result))
    print(json.dumps({'status': result['status'], 'record': ref(OUT)}))


if __name__ == '__main__':
    main()
