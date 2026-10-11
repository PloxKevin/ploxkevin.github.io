"""Pin a new owner25 request with the singleton reviewed working-code update."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = 'book/coverage/checks/root-owner25-binding-preparation-inputs-v1.json'
OLD_SHA = '9f4f860c9267f7973840f870d72bfae146d4a1e7757e8a4c9fd92c6b303b929d'
OUT = 'book/coverage/checks/root-owner25-binding-preparation-inputs-v2.json'
HELPER = 'book/coverage/checks/prepare_root_owner25_bindings_v3.py'
HELPER_SHA = '9d510810736bfdc9e671c913d1720e97a85e6ae477b3a2c3388170b5cd371b5c'
INTEGRATOR = 'book/coverage/checks/root_integrate_owner25_candidates_v3.py'
INTEGRATOR_SHA = '61e5f01dc3bc671d93e543caef716bc343933d0ba9f60a680d26b96e9e6b042d'
AUTH = 'book/coverage/checks/root-owner25-authorized-future-code-updates-v1.json'
AUTH_SHA = '65a0f1d21e0645663b290062112dec3cc071c9c1e018f2c359ab74f418faa052'

def sha(name):
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts and (ROOT / path).resolve().is_relative_to(ROOT.resolve())
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()

def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}

parser = argparse.ArgumentParser()
parser.add_argument('--independent-peer', required=True)
parser.add_argument('--peer-sha256', required=True)
args = parser.parse_args()
assert not (ROOT / OUT).exists()
assert sha(OLD) == OLD_SHA and sha(AUTH) == AUTH_SHA
assert sha(HELPER) == HELPER_SHA and sha(INTEGRATOR) == INTEGRATOR_SHA
assert sha(args.independent_peer) == args.peer_sha256
peer = read(args.independent_peer)
assert 'passed' in peer['status'] and peer.get('errors', []) == []
assert peer['helper_sha256'] == INTEGRATOR_SHA
assert peer['helpers_sha256'][HELPER] == HELPER_SHA and peer['helpers_sha256'][INTEGRATOR] == INTEGRATOR_SHA
authorization = read(AUTH)
assert authorization['status'] == 'root_authorized_exact_current_future_code_updates'
assert set(authorization['authorized_current_future_code_updates']) == {'book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'}
config = copy.deepcopy(read(OLD))
config['preparation_helper'] = ref(HELPER)
config['independent_integration_helper_review'] = ref(args.independent_peer)
config['destination'] = 'book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json'
config['current_future_code_update_authorization'] = ref(AUTH)
config['authorized_current_future_code_updates'] = copy.deepcopy(authorization['authorized_current_future_code_updates'])
config['root_requested_at_utc'] = datetime.now(timezone.utc).isoformat()
config['original_binding_preparation_input_v1'] = ref(OLD)
extras = {row['file']: row['sha256'] for row in config['extra_closed_evidence']['core']}
names = [OLD, AUTH, args.independent_peer, HELPER, INTEGRATOR, str(Path(__file__).relative_to(ROOT)),
    'book/coverage/checks/create_root_owner25_future_code_authorization_v1.py',
    'reports/full-coverage/prepare-owner25-future-code-authorization-execution-v1.json',
    'reports/full-coverage/prepare-owner25-future-code-authorization-execution-v1.log',
    'book/coverage/checks/root-owner25-reviewed-candidate-bindings-v1.json',
    'reports/full-coverage/prepare-owner25-bindings-execution-v1.json',
    'reports/full-coverage/prepare-owner25-bindings-execution-v1.log',
    'reports/full-coverage/owner25-integration-dry-execution-v1.json',
    'reports/full-coverage/owner25-integration-dry-execution-v1.log',
    'book/coverage/checks/future25-core/owner25-native-binding-independent-foundations-confirmation-v1.json']
for name in names: extras[name] = sha(name)
for body in (peer, read(names[-1])):
    for name, digest in body['closed_evidence_sha256'].items():
        assert sha(name) == digest; extras[name] = digest
for name, row in authorization['authorized_current_future_code_updates'].items():
    assert sha(name) == row['current_sha256']; extras[name] = row['current_sha256']
    for key in ('actual_first_execution', 'raw_log', 'closed_readiness', 'independent_delta_peer'):
        evidence = row[key]; assert sha(evidence['file']) == evidence['sha256']; extras[evidence['file']] = evidence['sha256']
    for closed_name, digest in read(row['independent_delta_peer']['file'])['closed_evidence_sha256'].items():
        assert sha(closed_name) == digest; extras[closed_name] = digest
config['extra_closed_evidence']['core'] = [{'file': name, 'sha256': digest} for name, digest in sorted(extras.items())]
for rows in config['extra_closed_evidence'].values():
    for row in rows: assert sha(row['file']) == row['sha256']
for row in config['offers'].values(): assert sha(row['file']) == row['sha256']
with (ROOT / OUT).open('x') as stream: stream.write(json.dumps(config, indent=2) + '\n')
print(json.dumps({'status': 'passed_pinned_root25_revised_binding_request', 'input': ref(OUT), 'owners': 4, 'extra_core_closed_artifacts': len(extras), 'authorized_future_code_updates': 1, 'live_owner_written': False}))
