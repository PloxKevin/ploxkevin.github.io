from pathlib import Path
import json, hashlib
ROOT = Path('/home/oxrexkevin/SafetyBased')
BASE = ROOT / 'book/coverage/checks/future32-applied/polygonal14-independent-v1'
REQUEST = ROOT / 'book/coverage/checks/future32-core/filippov-polygonal14-author-v1/filippov-polygonal14-full-source-actual-Euler-component-independent-review-request32-v1.json'
REVIEW = Path('/tmp/applied31-polygonal14-component-review-v1')
READER = Path('/tmp/applied31-polygonal14-component-v1-actual.json')
CONTEXT = Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CONTEXT_SHA = '0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
def real(n):
    p = Path(n)
    return p if p.is_absolute() else ROOT / p
def sha(p): return hashlib.sha256(real(p).read_bytes()).hexdigest()
def ref(p):
    p = real(p)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def read(p): return json.loads(real(p).read_bytes())
assert not BASE.exists() and sha(CONTEXT) == CONTEXT_SHA
ctx = read(CONTEXT)
held = {**ctx['pins_sha256'], **ctx['held_current_source_sha256'], **ctx['owners_sha256']}
def guard():
    assert sha(CONTEXT) == CONTEXT_SHA
    for n, h in held.items(): assert sha(n) == h, n
guard()
BASE.mkdir(parents=True)
request = read(REQUEST)
assessment = read(REVIEW / 'assessment.json')
reader = read(READER)
assert reader['actual_exit_code'] == 0 and reader['status'] == 'passed' and reader['protection_errors'] == []
assert sha(reader['log']) == reader['log_sha256'] and assessment['errors'] == []
inner = read(REVIEW / 'inner-actual-reader.json')
assert inner['protection_errors'] == [] and inner['protected_inputs_sha256_before'] == inner['protected_inputs_sha256_after']
aliases = {}
for original, row in request['all_original_byte_aliases'].items():
    d = {k: row[k] for k in ['file', 'sha256', 'bytes']}
    assert ref(d['file']) == d
    aliases[original] = {**d, 'original_file': original}
def add_alias(original, durable=None):
    p = real(original)
    key = str(p)
    d = ref(p)
    if durable is not None:
        dr = ref(durable)
        assert dr['sha256'] == d['sha256'] and dr['bytes'] == d['bytes']
    elif p.is_relative_to(ROOT):
        dr = d
    else:
        out = BASE / 'exact-original-leaf-by-sha256' / d['sha256'] / p.name
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open('xb') as f: f.write(p.read_bytes())
        dr = ref(out)
        assert dr['sha256'] == d['sha256'] and dr['bytes'] == d['bytes']
    if key in aliases:
        assert aliases[key]['sha256'] == d['sha256'] and aliases[key]['bytes'] == d['bytes']
        return aliases[key]
    aliases[key] = {**dr, 'original_file': key}
    return aliases[key]
add_alias(REQUEST)
add_alias(request['parent_full_increment_peer']['file'])
add_alias('/home/oxrexkevin/SafetyBased/verification/lean/SafeLearning/CompleteBarrierFilippovHalfspaces.lean', ROOT / 'book/coverage/checks/future31-core/canonical31-and-Euler6-independent-foundations-v1/original-byte-aliases/711e89ebfad207b24bc953e62b4a24039c9aea63811341878a6afb5601f70402/CompleteBarrierFilippovHalfspaces.lean')
add_alias(ROOT / 'SafeLearning/barriers.html', ROOT / 'book/coverage/checks/future31-applied/AST23-child-and35-structural-independent-applied30b-v1/original-byte-aliases/d9063446c77f88131c89816434966593fe592fedc7bbbf578a2f5a63abd39cda/barriers.html')
for p in [READER, real(reader['log']), REVIEW / 'assessment.json', REVIEW / 'inner-actual-reader.json', REVIEW / 'actual-Exercise16-local-existence-context.json', '/tmp/review-applied31-polygonal14-component-v1.py', '/tmp/record-applied31-polygonal14-component-v1.py', Path(__file__)]: add_alias(p)
for item in assessment['fresh_independent_whole_file_compiler_and_all14_axiom_histories']:
    native = read(item['native']['file'])
    for p in [item['native']['file'], native['raw_log'], native['source_snapshot'], native['source']]:
        if str(real(p)) not in aliases: add_alias(p)
for original, row in aliases.items():
    assert sha(row['file']) == row['sha256'] and real(row['file']).stat().st_size == row['bytes']
    if real(original).exists(): assert sha(original) == row['sha256']
guard()
closed = {**assessment, 'status': 'passed_independent_full_polygonal14_actual_Euler_component_math_body_domain_closed_peer', 'actual_reader': ref(real(aliases[str(READER)]['file'])), 'actual_reader_original_body_time_and_raw_log_preserved': True, 'original_measured_reader': ref(READER), 'original_measured_reader_inner': ref(REVIEW / 'inner-actual-reader.json'), 'all_original_byte_aliases': aliases, 'required_evidence_artifacts_sha256': {row['file']: row['sha256'] for row in aliases.values()}, 'bounded_closure_scope': 'Reused immutable original20 Root leaf aliases plus exact request, exact existing Euler full peer and original primary source leaf aliases; fresh reviewer helpers, assessment, native/raw/snapshots, context excerpt. No recursive prior provenance/snapshot/cache copying. Packaging is static guarded closure, not a relabeled compiler or canonical audit.'}
out = BASE / 'polygonal14-all-bodies-actual-Euler-component-independent-applied32-closed-peer-v1.json'
with out.open('x') as f: json.dump(closed, f, indent=2); f.write('\n')
guard()
print(json.dumps({'status': closed['status'], 'closed_peer': ref(out), 'actual_reader': closed['actual_reader'], 'alias_count': len(aliases)}))
