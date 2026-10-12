"""Reparse two independently reviewed literal corrections before any live write.

Default execution is a read-only preflight. Application requires a full code peer.
Owners and selected Lean sources remain byte exact; coverage rebasing is separate.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, subprocess, sys, time
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_apply_source80_81_v1.py'
BASE = 'book/coverage/checks/root_apply_source54_55_v3.py'
BASE_SHA = '6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
CONTEXT = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
CONTEXT_SHA = '73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
INVENTORY = 'book/coverage/inventory.json'
CORRECTIONS = 'book/coverage/material-corrections.json'
FRAGMENT = 'book/chapters/nn-in-the-loop.html'
METADATA = '676db1f7d13ddbf65c2f0253d1fab79c44948a7e'
HISTORY = 'reports/full-coverage/source-history/approved-corrections80-81-20261012'
REPORT = 'reports/full-coverage/source80-81-corrections-application-v1.json'
SPECTRAL = 'book/coverage/checks/future31-core/spectral-nonuniqueness-narrow-independent-applied30b-v1/foundations-spectral-nonuniqueness-one-phrase-full29-narrow-parser-independent-applied30b-closed-peer-v1.json'
INTEGRAL = 'book/coverage/checks/future31-core/integral-tracking-precision-independent-foundations-v1/modules-integral-tracking-three-exact-precision-phrases-full-literal-parser-independent-foundations31-closed-peer-v1.json'
PEER_PINS = {SPECTRAL: '85db76bb3e923124010b8b25d48d4878cca570243fe74d6df227b24a47e1a2d9', INTEGRAL: 'e008dc4fc6b68ea9abf47f4452f99d57892225d0d42b70b2b85d436549fc44be'}

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_bytes())
def path(name):
    p = Path(name)
    assert '..' not in p.parts and not any(c in str(p) for c in '\0\n\r')
    if not p.is_absolute(): p = ROOT / p
    assert p.is_file() and not p.is_symlink() and (p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp'))
    return p
def ref(name):
    p = path(name)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def checked(row):
    p = path(row['file']); assert sha(p) == row['sha256']
    if 'bytes' in row: assert p.stat().st_size == row['bytes']
    return p
def encoded(data): return (json.dumps(data, indent=2) + '\n').encode()
def new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as out: out.write(data)

assert sha(path(BASE)) == BASE_SHA
spec = importlib.util.spec_from_file_location('source80_81_pinned_parser', path(BASE))
b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)

def replace(original, rows):
    value = original.decode()
    for row in rows:
        assert value.count(row['before']) == 1 and row['after'] not in value
        value = value.replace(row['before'], row['after'], 1)
    result = value.encode()
    for row in reversed(rows):
        assert value.count(row['after']) == 1
        value = value.replace(row['after'], row['before'], 1)
    assert value.encode() == original and result.count(b'\n') == original.count(b'\n')
    sys.path.insert(0, str(ROOT / 'book'))
    from validate import Document
    a, z = Document(original.decode()), Document(result.decode())
    assert [(n.tag, n.attrs, n.line) for n in a.nodes] == [(n.tag, n.attrs, n.line) for n in z.nodes]
    return result

def guard():
    assert sha(CONTEXT) == CONTEXT_SHA
    context = read(CONTEXT)
    held = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
    for n, h in held.items(): assert sha(path(n)) == h, n
    assert sha(path(INVENTORY)) == '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
    assert sha(path(CORRECTIONS)) == 'a6d092a00ac879ba3613609734da9e3d4d8b718135b5c2ffa6bfff03d62ffd94'
    assert len(read(path(CORRECTIONS))['corrections']) == 79
    delivery = read(path('reports/full-coverage/publication30-finish-root-v1.json'))
    assert delivery['status'] == 'passed_actual_checkpoint30_content_and_metadata_push_Pages_all31_delivery'
    assert delivery['metadata_commit'] == METADATA and delivery['coverage_complete'] is False
    for command, expected in [(['git', 'rev-parse', 'HEAD'], METADATA), (['git', 'ls-remote', 'origin', 'refs/heads/main'], METADATA+'\trefs/heads/main'), (['git', 'status', '--porcelain=v1'], '')]:
        done = subprocess.run(command, cwd=ROOT/'reports/book/publication-repo', capture_output=True, text=True)
        assert done.returncode == 0 and done.stdout.strip() == expected
    return held

def proposals():
    peers = {}
    for n, h in PEER_PINS.items():
        assert sha(path(n)) == h, n
        d = read(path(n)); assert d['status'].startswith('passed') and d['errors'] == []
        actual = read(checked(d['actual_finalizer']))
        assert actual['status'].startswith('passed') and actual['actual_exit_code'] == 0
        assert actual['helper_sha256_before'] == actual['helper_sha256_after']
        assert actual.get('protection_errors', []) == []
        log_name = actual.get('raw_log', actual.get('log'))
        log_hash = actual.get('raw_log_sha256', actual.get('log_sha256'))
        assert sha(path(log_name)) == log_hash
        peers[n] = d
    spectral, integral = peers[SPECTRAL], peers[INTEGRAL]
    assert spectral['full_exact_qualifier_mathematical_correspondence_approved'] is True
    assert integral['full_current_and_proposed_literals_and_contexts_read'] is True
    assert integral['independent_parser']['both_ROOT_and_OUT_strictly_TMP'] is True
    assert spectral['exact_forward_and_inverse'] is integral['exact_forward_and_inverse'] is True
    rows = []
    for num, source, peer, replacements_key, proposed_key, changed_key in [
        (80, 'SafeLearning/primer-linalg.html', SPECTRAL, 'exact_literal_substitutions', 'prospective_source', 'actual_changed_literal_keys'),
        (81, 'SafeLearning/nn-in-the-loop.html', INTEGRAL, 'exact_replacements', 'proposed_source', 'fresh_changed_literal_keys'),
    ]:
        request = read(checked(peers[peer]['request']))
        proposal = peers[peer]['request']
        original = path(source).read_bytes()
        assert sha(path(source)) == request['source']['sha256'] and checked(request['source']).read_bytes() == original
        substitutions = request[replacements_key]
        candidate = replace(original, substitutions)
        assert candidate == checked(request[proposed_key]).read_bytes()
        rows.append({'correction_id': num, 'source': source, 'before': ref(source), 'candidate': request[proposed_key], 'proposal': proposal, 'peer': ref(peer), 'replacements': substitutions, 'changed': request[changed_key], 'candidate_bytes': candidate})
    return rows

def parser_worker(control, output):
    d = read(path(control)); candidates = {n: checked(r).read_bytes() for n, r in d.items()}
    assert all(n.startswith('SafeLearning/') and n.endswith('.html') for n in candidates)
    data, _ = b.full_parser(candidates)
    target = Path(output); assert target.is_absolute() and target.resolve().is_relative_to('/tmp') and not target.exists()
    new(target, data)

def main(args):
    assert Path(__file__).resolve() == ROOT/SELF
    held = guard(); rows = proposals(); before_helper = sha(path(SELF))
    work = ROOT/args.record_dir
    assert not work.exists() and work.resolve().is_relative_to(ROOT/'reports/full-coverage') and not work.is_symlink()
    assert not (ROOT/REPORT).exists() and not (ROOT/HISTORY).exists()
    for num in [80, 81]:
        assert not (ROOT/f'book/coverage/inventory-before-correction{num}.json').exists()
        assert not (ROOT/f'book/coverage/inventory-after-correction{num}.json').exists()
    code_peer = None
    if args.apply:
        assert args.code_peer and args.code_peer_sha256
        code_peer = {'file': args.code_peer, 'sha256': args.code_peer_sha256}
        peer = read(checked(code_peer))
        assert peer['status'].startswith('passed') and peer['errors'] == [] and peer['full_code_read'] is True
        assert peer['reviewed_helper'] == ref(SELF)
    work.mkdir(parents=True)
    candidates = {}; previous = read(path(INVENTORY)); parsed = []
    import tempfile
    for row in rows:
        candidates[row['source']] = row['candidate_bytes']
        control_rows = {}
        for i, (n, data) in enumerate(candidates.items()):
            p = work/f"step{row['correction_id']}-candidate{i}.html"; new(p, data); control_rows[n] = ref(str(p))
        control = work/f"step{row['correction_id']}-control.json"; new(control, encoded(control_rows))
        with tempfile.TemporaryDirectory(prefix='source80-81-full29-parser-') as td:
            output = Path(td)/'inventory.json'
            command = ['python3', str(ROOT/SELF), '--parser-worker', str(control), '--parser-output', str(output)]
            start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
            done = subprocess.run(command, cwd=ROOT, capture_output=True)
            finish = datetime.now(timezone.utc).isoformat(); elapsed = time.monotonic()-tick
            log = work/f"step{row['correction_id']}-parser.log"; new(log, done.stdout+done.stderr)
            native = {'status': 'passed_actual_isolated_full29_parser' if done.returncode == 0 else 'failed_actual_isolated_full29_parser', 'actual_command': command, 'actual_workdir': str(ROOT), 'actual_exit_code': done.returncode, 'started_at_utc': start, 'finished_at_utc': finish, 'elapsed_seconds': elapsed, 'log': ref(str(log)), 'helper_sha256_before': before_helper, 'helper_sha256_after': sha(path(SELF)), 'control': ref(str(control)), 'both_parser_ROOT_and_OUT_strictly_TMP': True}
            native_path = work/f"step{row['correction_id']}-parser-native.json"; new(native_path, encoded(native))
            assert done.returncode == 0 and native['helper_sha256_before'] == native['helper_sha256_after']
            data = output.read_bytes(); following = json.loads(data)
        step = {'source': row['source'], 'candidate': row['candidate'], 'counts': previous['counts'], 'exact_changed_text_keys': row['changed']}
        changed = b.inventory_diff(previous, following, step)
        assert following['counts']['exercises'] == 556 and following['counts']['material_source_units'] == 12774
        parsed.append((row, data, changed, ref(str(native_path)))); previous = following
    fragment_original = path(FRAGMENT).read_bytes()
    fragment_new = replace(fragment_original, rows[1]['replacements'])
    assert guard() == held and sha(path(SELF)) == before_helper
    if not args.apply:
        print(json.dumps({'status': 'passed_readonly_source80_81_two_fresh_full29_parser_preflight', 'actual_parser_records': [r[3] for r in parsed], 'source_writes': False, 'coverage_complete': False})); return
    for n in [INVENTORY, CORRECTIONS, FRAGMENT, *(r['source'] for r in rows)]: new(ROOT/HISTORY/n, path(n).read_bytes())
    corrections = read(path(CORRECTIONS)); applications = []
    for row, data, changed, parser in parsed:
        num = row['correction_id']; assert len(corrections['corrections']) == num-1
        before = f'book/coverage/inventory-before-correction{num}.json'; after = f'book/coverage/inventory-after-correction{num}.json'
        new(ROOT/before, path(INVENTORY).read_bytes()); new(ROOT/HISTORY/f'corrections-before{num}.json', path(CORRECTIONS).read_bytes())
        path(row['source']).write_bytes(row['candidate_bytes']); path(INVENTORY).write_bytes(data); new(ROOT/after, data)
        entry = {'correction_id': num, 'source': row['source'], 'before_sha256': row['before']['sha256'], 'after_sha256': row['candidate']['sha256'], 'replacements': row['replacements'], 'corrected_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'source_corrected_exact_independently_reviewed_literal_scope_owner_identity_rebase_pending', 'source_proposal': row['proposal'], 'independent_semantic_review': row['peer'], 'historical_source': ref(HISTORY+'/'+row['source']), 'inventory_before': ref(before), 'inventory_after': ref(after), 'actual_fresh_parser': parser, 'scope': 'Exact reviewed literal correction only; owner identities, canonical installation and whole coverage require separate integration.'}
        corrections['corrections'].append(entry); path(CORRECTIONS).write_bytes(encoded(corrections)); applications.append(entry)
    path(FRAGMENT).write_bytes(fragment_new)
    changed_paths = {FRAGMENT, *(r['source'] for r in rows)}
    for n, h in held.items():
        if n not in changed_paths: assert sha(path(n)) == h, n
    assert len(read(path(CORRECTIONS))['corrections']) == 81 and sha(path(INVENTORY)) == sha(path('book/coverage/inventory-after-correction81.json'))
    record = {'status': 'passed_actual_reviewed_source80_81_two_corrections_and_exact_NN_fragment_sync_owner_rebase_pending', 'helper': ref(SELF), 'code_peer': code_peer, 'applications': applications, 'NN_fragment_before': ref(HISTORY+'/'+FRAGMENT), 'NN_fragment_after': ref(FRAGMENT), 'actual_delivery_gate': ref('reports/full-coverage/publication30-finish-root-v1.json'), '1242_selected_proofs_and_five_raw_owner30_files_unchanged': True, 'coverage_complete': False}
    new(ROOT/REPORT, encoded(record)); print(json.dumps({'status': record['status'], 'report': ref(REPORT), 'inventory': ref(INVENTORY), 'coverage_complete': False}))

if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--record-dir'); p.add_argument('--apply', action='store_true'); p.add_argument('--code-peer'); p.add_argument('--code-peer-sha256'); p.add_argument('--parser-worker'); p.add_argument('--parser-output'); args = p.parse_args()
    if args.parser_worker:
        assert args.parser_output and not args.record_dir and not args.apply
        parser_worker(args.parser_worker, args.parser_output)
    else:
        assert args.record_dir and not args.parser_output
        main(args)
