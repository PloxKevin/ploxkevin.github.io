"""Preserve exact independently reviewed sources and run ten real Lean commands.

This prepares five unselected sources. It never edits an aggregate or raw owner.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, subprocess, sys, time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/recovery32'
CONTEXT = Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CATALOG = ROOT / 'book/coverage/checks/future32-foundations/distinct-nine-compiled107-catalog-v2/foundations-nine-distinct107-actual-compiled-native-full-scope-and-unnumbered-catalog32-v2.json'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n): return Path(n) if Path(n).is_absolute() else ROOT / n
def ref(p):
    p = locate(str(p))
    n = p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p)
    return {'file': n, 'sha256': sha(p), 'bytes': p.stat().st_size}
def checked(r):
    p = locate(r['file']); assert p.is_file() and not p.is_symlink()
    assert sha(p) == r['sha256'], str(p)
    if 'bytes' in r: assert p.stat().st_size == r['bytes']
    return p
def read(r): return json.loads(checked(r).read_bytes())
def new(p, data):
    assert p.is_relative_to(BASE) or p.parent == ROOT / 'verification/lean/SafeLearning'
    assert not p.exists() and not p.is_symlink(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)
def encode(d): return (json.dumps(d, indent=2, ensure_ascii=False) + '\n').encode()

def main():
    assert len(sys.argv) == 1
    context = json.loads(CONTEXT.read_bytes())
    assert context['status'] == 'actual_source81_installed_owner31_selected31_audited_TMP_context_only'
    held = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
    assert len(context['owners_sha256']) == 5
    selection = read(context['selection'])
    assert selection['proof_file_count'] == 1248
    assert all(held[n] == r['sha256'] for n, r in selection['proof_files'].items())
    held['book/coverage/inventory.json'] = sha(ROOT / 'book/coverage/inventory.json')
    held[str(CONTEXT)] = sha(CONTEXT)
    held[str(Path(__file__))] = sha(Path(__file__))
    catalog = json.loads(CATALOG.read_bytes())
    assert catalog['errors'] == [] and catalog['final_distinct_source_count'] == 9
    originals = {str(CATALOG): sha(CATALOG), str(CONTEXT): sha(CONTEXT)}
    spec = importlib.util.spec_from_file_location('recovery32_names', ROOT / 'book/coverage/lean_names.py')
    names = importlib.util.module_from_spec(spec); spec.loader.exec_module(names)
    selected_names = {r['name'] for n in selection['proof_files'] for r in names.declarations((ROOT / n).read_text())}
    families = []
    peer_keys = {'Frobenius15': 'Frobenius15_current315317_whole', 'WeightedAngle11': 'Weighted11_current131_whole', 'MetricExamplesAndCertifiedBalls10': 'MetricExamples10_current202_whole'}
    keys = {'Frobenius15': ['primer-linalg.html::node-315', 'primer-linalg.html::node-317'], 'WeightedAngle11': ['primer-linalg.html::node-131'], 'MetricExamplesAndCertifiedBalls10': ['primer-linalg.html::node-202']}
    for row in catalog['families']:
        if row['family'] not in peer_keys: continue
        source = row['final_source']
        stem = re.sub(r'-draft-v\d+$', '', Path(source['file']).stem)
        histories = [x['native'] for x in row['original_final_source_and_all_axiom_native_records']]
        families.append({'family': row['family'], 'owner': 'foundations', 'original_source': source, 'canonical_source': 'verification/lean/SafeLearning/' + stem + '.lean', 'author_request': row['full_mathematical_review_request'], 'independent_peer': catalog['closed_independent_scope_peers'][peer_keys[row['family']]], 'approved_whole_material_keys': keys[row['family']], 'original_native_records': histories, 'expected_public_theorem_count': row['source_theorem_count']})
    conv_request = ref(ROOT / 'book/coverage/checks/future31-applied/convolution13-author-components-v2/convolution13-entire-source-all-bodies-current1531-entire-literal-independent-review-request31-v1.json')
    conv = read(conv_request)
    families.append({'family': 'Convolution13', 'owner': 'applied', 'original_source': conv['reviewed_source'], 'canonical_source': 'verification/lean/SafeLearning/CompleteAppliedConvolutionReversalBridge32.lean', 'author_request': conv_request, 'independent_peer': ref(ROOT / 'book/coverage/checks/future32-applied/convolution13-independent-foundations-v1/applied-convolution13-entire-source-entire-current1531-whole-independent-foundations32-closed-peer-v1.json'), 'approved_whole_material_keys': ['primer-rl-nn.html::node-1531'], 'original_native_records': [conv['actual_final_source_native'], conv['actual_all13_axiom_native']], 'expected_public_theorem_count': 13})
    static_request = ref(ROOT / 'book/coverage/checks/future32-core/static-regret20-author-v1/static-regret20-full-source-current359-entire-literal-independent-review-request32-v1.json')
    static = read(static_request)
    source = static['all_original_byte_aliases'][static['source']['file']]
    families.append({'family': 'StaticRegret20', 'owner': 'applied', 'original_source': {k: source[k] for k in ['file', 'sha256', 'bytes']}, 'canonical_source': 'verification/lean/SafeLearning/CompleteAppliedStaticRegretDoesNotTrack32.lean', 'author_request': static_request, 'independent_peer': ref(ROOT / 'book/coverage/checks/future32-applied/static-regret20-independent-v1/static-regret20-all-bodies-entire-current359-whole-independent-applied32-closed-peer-v1.json'), 'approved_whole_material_keys': ['primer-rl-nn.html::node-359'], 'original_native_records': static['original_native_history'], 'expected_public_theorem_count': 20})
    all_names = set()
    for row in families:
        source = checked(row['original_source'])
        declarations = names.declarations(source.read_text())
        public = {d['name'] for d in declarations}
        assert len(public) == len(declarations) and not public.intersection(selected_names | all_names)
        all_names.update(public)
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(source.read_text()))
        row['public_declarations'] = declarations
        row['public_theorem_count'] = sum(d['kind'] in ['theorem', 'lemma'] for d in declarations)
        row['public_name_count'] = len(declarations)
        row['original_namespace'] = sorted(set(re.findall(r'^namespace (.+)$', source.read_text(), re.M)))
        assert row['public_theorem_count'] == row.pop('expected_public_theorem_count')
        dest = ROOT / row['canonical_source']; assert not dest.exists()
        peer = read(row['independent_peer']); assert peer['status'].startswith('passed') and peer['errors'] == []
        for r in [row['original_source'], row['author_request'], row['independent_peer']]:
            p = checked(r); originals[str(p)] = sha(p)
        for r in row['original_native_records']:
            native = read(r); p = checked(r); originals[str(p)] = sha(p)
            for k, h in [('raw_log', 'raw_log_sha256'), ('source_snapshot', 'source_snapshot_sha256')]:
                p = checked({'file': native[k], 'sha256': native[h]}); originals[str(p)] = sha(p)
            assert type(native['actual_exit_code']) is int
    assert len(families) == 5 and sum(r['public_theorem_count'] for r in families) == 69
    def guard():
        for n, h in {**held, **originals}.items(): assert sha(locate(n)) == h, n
        for row in families:
            p = ROOT / row['canonical_source']
            if p.exists(): assert sha(p) == row['original_source']['sha256']
    guard()
    aliases = {}
    for n, h in originals.items():
        p = locate(n); dest = BASE / 'originals' / h / p.name
        if dest.exists(): assert sha(dest) == h
        else: new(dest, p.read_bytes())
        aliases[n] = ref(dest)
    for row in families:
        source = checked(row['original_source']); dest = ROOT / row['canonical_source']
        new(dest, source.read_bytes()); row['canonical_source_ref'] = ref(dest)
    guard()
    plan = {'status': 'prepared_five_exact_reviewed_Source81_no_wording_canonical_sources_unselected', 'created_at_utc': datetime.now(timezone.utc).isoformat(), 'baseline_selection': context['selection'], 'baseline_actual_audit': context['actual_audit'], 'source_count': 5, 'public_theorem_count': 69, 'public_name_count': len(all_names), 'whole_material_key_count': 6, 'sources': families, 'preserved_primary_originals': aliases, 'protected_inputs_sha256': held, 'coverage_complete': False, 'owner_or_aggregate_or_selection_modified': False, 'convolution_namespace31_preserved_in_future32_module': True}
    new(BASE / 'five-source-map-v1.json', encode(plan))
    print(json.dumps({'map': ref(BASE / 'five-source-map-v1.json'), 'sources': 5, 'theorems': 69}), flush=True)
    pairs = []
    for row in families:
        stem = Path(row['canonical_source']).stem
        for kind in ['standalone', 'named']:
            guard(); source = ROOT / row['canonical_source']; before = sha(source)
            command = ['lake', 'env', 'lean', 'SafeLearning/' + source.name] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + stem]
            log = BASE / 'compiles' / (stem + '-' + kind + '.log'); log.parent.mkdir(exist_ok=True)
            start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
            with log.open('xb') as f: result = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=f, stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - tick; end = datetime.now(timezone.utc).isoformat()
            protection_errors = []
            try: guard()
            except Exception as error: protection_errors.append(str(error))
            after = sha(source)
            record = {'status': 'passed' if result.returncode == 0 and before == after and not protection_errors else 'failed', 'actual_exit_code': result.returncode, 'command': command, 'actual_workdir': str(ROOT / 'verification/lean'), 'started_at_utc': start, 'finished_at_utc': end, 'elapsed_seconds': elapsed, 'source': row['canonical_source_ref'], 'source_sha256_before': before, 'source_sha256_after': after, 'source_snapshot': row['original_source'], 'raw_log': ref(log), 'protection_errors': protection_errors, 'scope': 'Actual standalone or named compilation only; kernel replay, aggregate audit and owner installation remain separate.'}
            record_path = BASE / 'compiles' / (stem + '-' + kind + '.json'); new(record_path, encode(record))
            pairs.append({'kind': kind, 'source': row['canonical_source_ref'], 'actual_record': ref(record_path), 'raw_log': ref(log), 'actual_exit_code': result.returncode})
            print(json.dumps({'source': stem, 'kind': kind, 'actual_exit_code': result.returncode, 'elapsed_seconds': elapsed, 'protection_errors': protection_errors}), flush=True)
            assert record['status'] == 'passed', str(record_path)
    guard()
    readiness = {'status': 'passed_five_exact_reviewed_Source81_standalone_and_named_pairs_unselected', 'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'source_map': ref(BASE / 'five-source-map-v1.json'), 'source_count': 5, 'public_theorem_count': 69, 'public_name_count': len(all_names), 'actual_compiler_command_count': 10, 'actual_paired_records': pairs, 'protected_inputs_sha256': held, 'coverage_complete': False, 'owner_or_aggregate_or_selection_modified': False}
    new(BASE / 'five-canonical-readiness-v1.json', encode(readiness))
    print(json.dumps({'readiness': ref(BASE / 'five-canonical-readiness-v1.json'), 'actual_commands': 10}), flush=True)

if __name__ == '__main__': main()
