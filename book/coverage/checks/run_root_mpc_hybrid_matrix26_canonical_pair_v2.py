"""Archive cumulative MPC component evidence and run two actual canonical checks.

The fixed25 selection, sources, assets and installed ledgers are protected.
These new26 checks make no aggregate or whole-exercise promotion claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[3]
TMP = Path('/tmp')
BASE = ROOT / 'book/coverage/checks/future26-core/mpc-hybrid-matrix'
NAME = 'CompleteCoreMPCHybridMatrixInfinityInput26'
SOURCE = TMP / (NAME + '.lean')
DIGEST = '703ab6db4166af324f43b69a022cec247ec1e4e3967833d9e15018bbb4f9ee6d'
PEER = TMP / 'mpc-hybrid-matrix-infinity-input26-independent-applied-five-new-body-component-review-v1.json'
PEER_SHA = 'd2ac49b2a9bd50aa67a0d32177d07eae45980aed4a98cd30ed6d377552ee1747'
SELECTION = 'reports/full-coverage/checkpoint-25-selection.json'
SELECTION_SHA = '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def rel(p): return p.relative_to(ROOT).as_posix()
def exact_copy(source, target):
    assert source.is_file() and not source.is_symlink()
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists(): assert sha(target) == sha(source), str(target)
    else:
        with target.open('xb') as out: out.write(source.read_bytes())
    assert sha(target) == sha(source)

assert sha(ROOT / SELECTION) == SELECTION_SHA
selection = read(ROOT / SELECTION)
assert selection['proof_file_count'] == len(selection['proof_files']) == 1156
manifest_name = 'reports/full-coverage/checkpoint-25-manifest.json'
manifest = read(ROOT / manifest_name)
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert manifest['selection_sha256'] == SELECTION_SHA
protected = {n: r['sha256'] for n, r in selection['proof_files'].items()}
owners = {'book/coverage/' + owner + '.json' for owner in ('core', 'foundations', 'applied', 'modules', 'applied-promotions')}
protected.update({n: h for n, h in manifest['working_inputs_sha256'].items()
                  if n.startswith('SafeLearning/') or n in owners or n == 'book/coverage/inventory.json'})
protected[SELECTION] = SELECTION_SHA
protected[manifest_name] = sha(ROOT / manifest_name)
assert len([n for n in protected if n.startswith('SafeLearning/')]) == 31
assert owners <= set(protected)

def guard():
    for n, h in protected.items(): assert sha(ROOT / n) == h, n

guard()
assert sha(SOURCE) == DIGEST and sha(PEER) == PEER_SHA
peer = read(PEER)
assert peer['whole_exercise_approved'] is False and peer['all5_new_complete_bodies_read'] is True and peer['errors'] == []
assert peer['complete_source_body'] == SOURCE.read_text()
assert len(re.findall(r'^theorem ', SOURCE.read_text(), re.M)) == 30
canonical = ROOT / 'verification/lean/SafeLearning' / (NAME + '.lean')
readiness = BASE / 'root-mpc-hybrid-matrix26-canonical-readiness-v1.json'
assert not canonical.exists() and not readiness.exists()
for suffix in ('-standalone.json', '.log', '-named-build.json', '-named-build.log'):
    assert not (ROOT / 'book/coverage/checks' / (NAME + suffix)).exists()

# The entire original whole-source peer and every existing TMP file referenced
# in its nested original evidence are copied without changing command or time.
originals = {SOURCE, PEER}
def collect(value):
    if isinstance(value, dict):
        for key, item in value.items(): collect(key); collect(item)
    elif isinstance(value, list):
        for item in value: collect(item)
    elif isinstance(value, str) and value.startswith('/tmp/'):
        # Embedded raw warning text is evidence content, not a file name.
        if len(value.encode()) > 240 or any(c in value for c in ('\0', '\n', '\r')):
            return
        p = Path(value)
        if p.parent != TMP:
            return
        if p.is_file():
            assert p.resolve().is_relative_to(TMP.resolve()) and not p.is_symlink()
            assert p.suffix in {'.lean', '.json', '.log', '.py', '.txt'}
            originals.add(p)
collect(peer)
for pattern in ('root-mpc-*26-trial*', 'root_tmp_lean26_runner_v1.py', 'root_tmp_lean26_runner_v2.py'):
    originals.update(p for p in TMP.glob(pattern) if p.is_file())
aliases = {}
for p in sorted(originals):
    target = BASE / 'original-tmp' / p.name
    exact_copy(p, target)
    aliases[str(p)] = {'file': rel(target), 'sha256': sha(target)}
exact_copy(SOURCE, canonical)
snapshot = BASE / (NAME + '-original-source-v1.lean')
exact_copy(SOURCE, snapshot)
pairs = []
for helper, suffix in (('book/coverage/check_core_standalone.py', '-standalone.json'),
                       ('book/coverage/check_core_named_build.py', '-named-build.json')):
    result = subprocess.run(['python3', helper, NAME], cwd=ROOT)
    guard()
    assert sha(canonical) == DIGEST
    if result.returncode: raise SystemExit(result.returncode)
    path = ROOT / 'book/coverage/checks' / (NAME + suffix)
    record = read(path)
    assert type(record['exit_code']) is int and record['exit_code'] == 0
    assert record['source_sha256_before'] == record['source_sha256_after'] == DIGEST
    assert sha(ROOT / record['log']) == record['log_sha256']
    pairs.append({'file': rel(path), 'sha256': sha(path), 'actual_exit_code': 0,
                  'log': {'file': record['log'], 'sha256': record['log_sha256']}})
guard()
readiness.write_text(json.dumps(dict(status='passed_actual_canonical_pair_unselected_future26',
    prepared_at_utc=datetime.now(timezone.utc).isoformat(),
    source={'file': rel(canonical), 'sha256': DIGEST},
    source_snapshot={'file': rel(snapshot), 'sha256': DIGEST},
    original_full_source_peer=aliases[str(PEER)], public_theorem_count=30,
    actual_canonical_pair=pairs, original_TMP_byte_copies=aliases,
    protected_selected25_source_count=1156, protected_current52_asset_count=31,
    protected_installed25_owner_count=5, protected_input_sha256=protected,
    coverage_complete=False,
    scope='Thirty cumulative MPC component theorems, including actual finite-entry switching, terminal quadratic convergence and true initial-law transfer with literal infinity-norm input errors. The generic Assumptions1–4 robust replanning certificate remains an explicit premise and pending obligation; whole Exercise18(d) is not approved. All original source, peer, failed/pass trial, warnings and actual times remain exact. No new aggregate audit, selection or ledger promotion is claimed.'), indent=2) + '\n')
print(json.dumps({'status': 'passed', 'public_theorems': 30,
                  'archived_originals': len(aliases), 'readiness': rel(readiness)}))
