"""Archive the complete smoothing44 review/history and run two real checks.

The fixed25 selection, sources, assets and installed ledgers are protected.
These new26 checks make no aggregate or whole-exercise promotion claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[3]
TMP = Path('/tmp')
BASE = ROOT / 'book/coverage/checks/modules-future26/smoothing'
NAME = 'CompleteModulesSmoothingClassifier26'
SOURCE = TMP / 'modules-smoothing-randomized-kernel26-trial3.lean'
DIGEST = '00a41cb1753adc0082d32fb7f2a1adfd697f1c03ed6637c9326bad8f7fb729c7'
PEER = TMP / 'modules-smoothing44-independent-applied-full-whole-source-review26-v1.json'
PEER_SHA = 'f2c3ae9788f2249e0479a08089922a757ca6d6df6cb77444676174d59b761c63'
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
assert peer['whole_exercise_approved'] is True and peer['errors'] == []
assert peer['proof_source'] == {'file': str(SOURCE), 'sha256': DIGEST}
assert peer['all44_full_bodies_and_definitions_read'] is True
request = TMP / 'modules-smoothing-randomized-seven-wrappers26-independent-review-request-v1.json'
assert sha(request) == '40bdbd697d2979f7433d26ce9fa6c28834e0efd6fa75f6597419722e12a9ff86'
request_body = read(request)
assert request_body['entire_source_body'] == SOURCE.read_text()
assert request_body['public_theorem_count'] == 44
assert peer['entire_original37_review_body_and_time_unchanged'] == read(TMP / 'modules-smoothing37-independent-applied-full-source-components-review26-v1.json')
assert len(re.findall(r'^theorem ', SOURCE.read_text(), re.M)) == 44
canonical = ROOT / 'verification/lean/SafeLearning' / (NAME + '.lean')
readiness = BASE / 'modules-smoothing44-canonical-paired-readiness26-v1.json'
assert not canonical.exists() and not readiness.exists()
for suffix in ('-standalone.json', '.log', '-named-build.json', '-named-build.log'):
    assert not (ROOT / 'book/coverage/checks' / (NAME + suffix)).exists()

# The entire original whole-source peer and every existing TMP file referenced
# in its nested original evidence are copied without changing command or time.
originals = {SOURCE, PEER, request}
def collect(value):
    if isinstance(value, dict):
        for key, item in value.items(): collect(key); collect(item)
    elif isinstance(value, list):
        for item in value: collect(item)
    elif isinstance(value, str) and value.startswith('/tmp/'):
        p = Path(value)
        if p.is_file():
            assert p.resolve().is_relative_to(TMP.resolve()) and not p.is_symlink()
            assert p.suffix in {'.lean', '.json', '.log', '.py', '.txt'}
            originals.add(p)
collect(peer)
collect(request_body)
for pattern in ('modules-smoothing*', 'modules-verification-smoothing*', 'review-smoothing44-independent-applied*', 'run-smoothing44-independent-applied*', 'review-smoothing37-independent-applied*', 'run-smoothing37-independent-applied*', 'root_tmp_lean26_runner_v1.py', 'root_tmp_lean26_runner_v2.py'):
    originals.update(p for p in TMP.glob(pattern) if p.is_file() and p.suffix in {'.lean', '.json', '.log', '.py', '.txt'})
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
    original_full_source_peer=aliases[str(PEER)], public_theorem_count=44,
    entire_original_full_source_peer_body_and_time=peer,
    original_request=aliases[str(request)], entire_original_request_body=request_body,
    actual_canonical_pair=pairs, original_TMP_byte_copies=aliases,
    protected_selected25_source_count=1156, protected_current52_asset_count=31,
    protected_installed25_owner_count=5, protected_input_sha256=protected,
    coverage_complete=False,
    scope='One cumulative44 source: genuine Gaussian likelihood/fiber event transfer, deterministic and fixed-independent-law randomized ideal classifier, sampling confidence given its valid probability-bound premise, true quantile/norm/boundary literals. Original37 prefix/review and every trial/pass/failure remain historical unselected bytes. No aggregate audit, production selection or live ledger integration is claimed.'), indent=2) + '\n')
print(json.dumps({'status': 'passed', 'public_theorems': 44,
                  'archived_originals': len(aliases), 'readiness': rel(readiness)}))
