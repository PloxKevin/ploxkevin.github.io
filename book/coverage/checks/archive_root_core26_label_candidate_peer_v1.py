"""Close the five original independent Core26 candidate-reader artifacts."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
BASE = 'book/coverage/checks/future26-core/box-labels'
NAMES = [
    '/tmp/core26-labels-isolated-candidate-independent-applied-confirmation-v1.json',
    '/tmp/check-core26-labels-isolated-candidate-independent-applied-v1.py',
    '/tmp/core26-labels-isolated-candidate-independent-applied-actual-v1.json',
    '/tmp/core26-labels-isolated-candidate-independent-applied-actual-v1.log',
    '/tmp/run-core26-labels-isolated-candidate-independent-applied-v1.py']
PEER_SHA = '3154c7dd3c9aab14155895ba8107de0672a20b7b9232941fc5f786de9381872e'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())

peer = read(Path(NAMES[0]))
assert sha(Path(NAMES[0])) == PEER_SHA
assert 'passed' in peer['status'] and peer['errors'] == []
assert peer['entire_inverse_to_held_isolated25_candidate'] is True
assert sha(ROOT / peer['candidate']['file']) == peer['candidate']['sha256']
execution = read(Path(NAMES[2]))
codes = [execution[key] for key in ('exit_code', 'actual_exit_code') if key in execution]
assert codes and all(type(code) is int and code == 0 for code in codes)
log_hashes = [execution[key] for key in ('log_sha256', 'raw_log_sha256') if key in execution]
assert log_hashes and all(digest == sha(Path(NAMES[3])) for digest in log_hashes)
protected_names = ['book/coverage/' + name + '.json' for name in ('core', 'foundations', 'applied', 'modules', 'applied-promotions')]
protected = {name: sha(ROOT / name) for name in protected_names}
target = ROOT / BASE / 'original-independent-candidate-peer-v1'
assert not target.exists(); target.mkdir()
aliases = []
for name in NAMES:
    original = Path(name); copy = target / original.name
    with copy.open('xb') as stream: stream.write(original.read_bytes())
    assert sha(copy) == sha(original)
    aliases.append({'original_absolute_file': name, 'sha256': sha(original), 'canonical_original_byte_copy': copy.relative_to(ROOT).as_posix()})
assert all(sha(ROOT / name) == digest for name, digest in protected.items())
catalog = ROOT / BASE / 'independent-candidate-peer-original-byte-aliases-v1.json'
with catalog.open('x') as stream:
    stream.write(json.dumps({'status': 'closed_exact_original_core26_independent_candidate_peer_bytes', 'archived_at_utc': datetime.now(timezone.utc).isoformat(), 'original_peer_sha256': PEER_SHA, 'aliases': aliases, 'live_owner_sha256_unchanged': protected, 'scope': 'Original independent read-only checker0, hypotheses, decisions and times are retained without rewriting. This byte closure neither installs a ledger nor compiles Lean.'}, indent=2) + '\n')
print(json.dumps({'status': 'passed', 'closed_originals': 5, 'catalog': {'file': catalog.relative_to(ROOT).as_posix(), 'sha256': sha(catalog)}, 'live_owners_unchanged': True}))
