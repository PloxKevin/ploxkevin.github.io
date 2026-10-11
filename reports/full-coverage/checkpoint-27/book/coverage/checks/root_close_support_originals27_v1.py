"""Keep exact original supporting reviews and their closed TMP evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'book/coverage/checks/future27-core/original-checkpoint27-support-reviews-v1'
ORIGINALS = {
    '/tmp/root-browser26-all48-actual-captured-region-review-closure27-v1.json': 'e2f4ed6013788e0e0ec90b307aa7428b6d0d8911f40d05eb71f613f6a7f9b12e',
    '/tmp/core27-finalizer2-independent-foundations-code-and-native-review-v1.json': '3b82fcc4cec73e530e6f47c5462ce1b21a4110f55582cb3aad8fbe9820985742',
    '/tmp/root-tmp27-runner4-independent-modules-review-v1.json': '05f166cb74d628993d8b5e40f42ca55a4c1e04df04838019829693f65b3a4d60',
}
OWNERS = {'book/coverage/' + k + '.json' for k in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n):
    assert isinstance(n, str) and n
    p = Path(n)
    if not p.is_absolute():
        assert '..' not in p.parts and p.as_posix() == n
        p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
    assert p.is_file() and not p.is_symlink()
    return p
def resolve_original(n, h):
    p = locate(n)
    if sha(p) != h:
        assert n in OWNERS
        row = replacements[n]
        assert row['before_sha256'] == h and sha(p) == row['candidate']['sha256']
        p = locate(row['original26_byte_copy'])
    assert sha(p) == h, n
    return p
assert not BASE.exists()
result_path = locate('reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')
result = json.loads(result_path.read_bytes())
assert result['applied'] is True and result['coverage_complete'] is False
replacements = {r['destination']: r for r in result['exact_replacements']}
assert set(replacements) == OWNERS
requested = dict(ORIGINALS)
root_references = {}
def add(n, h):
    assert n not in requested or requested[n] == h
    requested[n] = h
def typed_tmp_refs(obj):
    if isinstance(obj, dict):
        if set(obj) >= {'file', 'sha256'} and isinstance(obj['file'], str) and obj['file'].startswith('/tmp/'):
            add(obj['file'], obj['sha256'])
        for v in obj.values(): typed_tmp_refs(v)
    elif isinstance(obj, list):
        for v in obj: typed_tmp_refs(v)
for n, h in ORIGINALS.items():
    body = json.loads(resolve_original(n, h).read_bytes())
    typed_tmp_refs(body)
    for name, digest in body.get('closed_evidence_sha256', {}).items():
        resolve_original(name, digest)
        if Path(name).is_absolute() and name.startswith('/tmp/'): add(name, digest)
        else: root_references[name] = digest
sources = {n: resolve_original(n, h) for n, h in requested.items()}
BASE.mkdir(parents=True)
aliases = {}
for index, (n, h) in enumerate(sorted(requested.items())):
    p = sources[n]; target = BASE / h / (str(index) + '-' + p.name)
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as f: f.write(p.read_bytes())
    assert sha(target) == h
    aliases[n + '::' + h] = {'original_file': n, 'original_sha256': h, 'immutable_byte_copy': {'file': target.relative_to(ROOT).as_posix(), 'sha256': h}}
root_aliases = {}
for n, h in root_references.items():
    p = resolve_original(n, h)
    root_aliases[n + '::' + h] = {'original_file': n, 'original_sha256': h, 'immutable_byte_copy': {'file': p.relative_to(ROOT).as_posix(), 'sha256': h}}
catalog = {'status': 'closed_exact_original_supporting_review_bytes_without_retiming_or_new_review', 'closed_at_utc': datetime.now(timezone.utc).isoformat(), 'original_review_files_sha256': ORIGINALS, 'original_closed_byte_aliases': aliases, 'unchanged_or_genuine_before27_root_byte_aliases': root_aliases, 'scope': 'Original review bodies, commands, times, failures and limitations remain unchanged. Browser captures establish only their recorded regions; no whole-page or mathematical approval is added.'}
out = BASE / 'original-support-review-byte-aliases-v1.json'
with out.open('x') as f: f.write(json.dumps(catalog, indent=2) + '\n')
print(json.dumps({'status': catalog['status'], 'originals': len(aliases), 'catalog': out.relative_to(ROOT).as_posix(), 'sha256': sha(out)}))
