"""Record the one reviewed draft-to-first-execution helper change for owner25."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
PEER = 'book/coverage/checks/future25-core/baseline24-one-working-helper-delta-independent-foundations-review-v1.json'
PEER_SHA = 'e46825885fe42399e20fc1191da42374728fa9a3d5fb5ed89ce05de13b8ebf89'
OUT = 'book/coverage/checks/root-owner25-authorized-future-code-updates-v1.json'
HELPER = 'book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'
OLD = 'f98e1a5ed31c6641ee15b3ecb00af0f0268bb0518d1cf5f125447320b1554ca6'
CURRENT = '53d47e49148a10f3dca53fff80514219e814764f557ae8f809c0d3dd28221fc6'

def sha(name):
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT / name).read_text())

def checked(ref):
    assert set(ref) == {'file', 'sha256'} and sha(ref['file']) == ref['sha256']
    return read(ref['file'])

assert not (ROOT / OUT).exists()
assert sha(PEER) == PEER_SHA
peer = read(PEER)
assert 'passed' in peer['status'] and peer.get('errors', []) == []
native = copy.deepcopy(peer['reviewed_update'])
assert native.pop('file') == HELPER
assert native['old_working_sha256'] == OLD and native['current_sha256'] == CURRENT == sha(HELPER)
manifest = checked(peer['baseline24_manifest'])
assert manifest['working_inputs_sha256'][HELPER] == manifest['frozen_inputs_sha256'][HELPER] == OLD
assert native['original_frozen_input'] == {'file': manifest['snapshot'] + '/' + HELPER, 'sha256': OLD}
assert sha(native['original_frozen_input']['file']) == OLD
execution = checked(native['actual_first_execution'])
assert type(execution['actual_exit_code']) is int and execution['actual_exit_code'] == 0
assert execution['actual_command'] == ['python3', HELPER]
assert execution['helper_sha256_before'][HELPER] == execution['helper_sha256_after'][HELPER] == CURRENT
assert execution['log'] == native['raw_log']['file'] and execution['log_sha256'] == native['raw_log']['sha256']
assert sha(native['raw_log']['file']) == native['raw_log']['sha256']
checked(native['closed_readiness'])
checked(peer['working_difference_observation'])
for name, digest in peer['closed_evidence_sha256'].items():
    assert sha(name) == digest
native['independent_delta_peer'] = {'file': PEER, 'sha256': PEER_SHA}
out = {
    'status': 'root_authorized_exact_current_future_code_updates',
    'root_authorized_at_utc': datetime.now(timezone.utc).isoformat(),
    'baseline24_manifest': peer['baseline24_manifest'],
    'working_difference_observation': peer['working_difference_observation'],
    'authorized_current_future_code_updates': {HELPER: native},
    'reason': 'The completed24 snapshot retains an unexecuted draft. Before its first genuine canonical25 run, this preparation helper gained four original-history archive patterns. The independent whole-helper delta review confirms unchanged compiler commands, source protection and guard logic. Its genuine successful first execution binds the current bytes. Root authorizes this one explicit working-code update while preserving every original frozen24 byte and requiring every other immutable working input to retain its original hash.'
}
with (ROOT / OUT).open('x') as stream:
    stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps({'status': 'passed_singleton_root_future_code_authorization_recorded', 'authorization': {'file': OUT, 'sha256': sha(OUT)}, 'authorized_working_code_updates': 1, 'live_owner_changed': False}))
