"""Prepare a proof-only six-source plan from completed independent reviews."""
from pathlib import Path
import argparse, hashlib, importlib.util, json

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT/'book/coverage/checks/future31-core/current81-canonical-plan6-v1.json'
CATALOG = Path('/tmp/foundations-four-compiled-families-supply31-v1.json')
CATALOG_SHA = 'ce0e312879506aaf79933dce0cf6ecfcaa60575f184f1b690639e3dc01133dbb'
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
GROWTH = 'book/coverage/checks/future31-applied/growth10-whole-independent-v1/growth10-entire-current1271-independent-applied31-peer-v1.json'
GROWTH_SHA = 'e3f153e9cb87a1f326c0a7c9bc2cce6de1a7f3b8458e1d6dc1a87644c6ecb9d4'
INTEGRAL = 'book/coverage/checks/future31-applied/integral35-whole-independent-v1/integral35-entire-current-prospective-independent-applied31-peer-v1.json'
INTEGRAL_SHA = 'e0d997d45d8d5387cba74e87adc8cc37ac8afec394dfdb0370f12b7f9a3e48c0'
FOUR = 'book/coverage/checks/future31-core/integral39-four-correspondence-independent-modules-v1/modules-integral39-exact35-prefix-four-full-correspondence-bodies-independent-modules31-closed-peer-v1.json'
FOUR_SHA = 'acc36c8719367766fa31b05137d9e784aabd59e4df23acb42f114ab04b46117d'

def path(n):
    p = Path(n); p = p if p.is_absolute() else ROOT/p
    assert p.is_file() and not p.is_symlink() and (p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp'))
    return p
def ref(n):
    p = path(n)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
def checked(n, h):
    r = ref(n); assert r['sha256'] == h
    return json.loads(path(n).read_bytes())
def peer(n, h):
    d = checked(n, h); assert d['status'].startswith('passed_') and d['errors'] == []
    return ref(n)

parser = argparse.ArgumentParser()
parser.add_argument('--euler-peer', required=True); parser.add_argument('--euler-peer-sha256', required=True)
parser.add_argument('--runner-code-peer', required=True); parser.add_argument('--runner-code-peer-sha256', required=True)
args = parser.parse_args()
assert not OUT.exists()
catalog = checked(str(CATALOG), CATALOG_SHA); context = checked(str(CONTEXT), CONTEXT_SHA)
assert context['owner_identity_rebase_pending'] is True and context['aggregate_source81_verification_claimed'] is False
for n, h in {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}.items(): assert ref(n)['sha256'] == h
code = checked(args.runner_code_peer, args.runner_code_peer_sha256)
assert code['status'].startswith('passed_') and code['errors'] == [] and code['full_code_read'] is True
assert code['reviewed_helper']['sha256'] == ref('book/coverage/checks/run_root31_reviewed_canonical_pairs_v1.py')['sha256']
spec = importlib.util.spec_from_file_location('canonical31_names', ROOT/'book/coverage/lean_names.py')
names = importlib.util.module_from_spec(spec); spec.loader.exec_module(names)
rows = []
def add(source, trial, target, peers):
    s, t = ref(source), ref(trial); native = json.loads(path(trial).read_bytes())
    assert native['status'].startswith('passed') and native['actual_exit_code'] == 0 and native['protection_errors'] == []
    assert native['source_sha256_before'] == native['source_sha256_after'] == native['source_snapshot_sha256'] == s['sha256']
    assert ref(native['source_snapshot'])['sha256'] == s['sha256'] and ref(native['raw_log'])['sha256'] == native['raw_log_sha256']
    decls = names.declarations(path(source).read_text())
    rows.append({'canonical_source': target, 'original_tmp_source': s, 'original_actual_tmp_trial': t, 'public_declarations': decls, 'public_theorem_count': sum(r['kind'] in ['theorem', 'lemma'] for r in decls), 'independent_source_peers': peers})
for family in catalog['families']:
    f = family['final_actual_passed_TMP_source']; histories = family['genuine_compiler_histories_preserved']
    last = histories[-1]['actual_native']
    if family['id'] == 'growth_examples_logdet10': reviews = [peer(GROWTH, GROWTH_SHA)]
    else:
        p = family['independent_full_math_scope_peer']; reviews = [peer(p['file'], p['sha256'])]
    add(f['file'], last['file'], family['prospective_canonical_target'], reviews)
add('/tmp/applied-finish31-integral35-correspondence-v2.lean', '/tmp/applied-finish31-integral35-correspondence-native-v2.json', 'verification/lean/SafeLearning/CompleteModulesIntegralTrackingWhole31.lean', [peer(INTEGRAL, INTEGRAL_SHA), peer(FOUR, FOUR_SHA)])
add('/tmp/CompleteCoreFilippovEulerConstruction31-draft-v2.lean', '/tmp/root-filippov-euler24-source81-owner30-trial2.json', 'verification/lean/SafeLearning/CompleteCoreFilippovEulerConstruction31.lean', [peer(args.euler_peer, args.euler_peer_sha256)])
assert len(rows) == 6 and sum(r['public_theorem_count'] for r in rows) == 104
plan = {'status': 'exact_reviewed_new_canonical_pair_plan31_only', 'context': ref(str(CONTEXT)), 'runner_code_peer': ref(args.runner_code_peer), 'foundations_supply_catalog': ref(str(CATALOG)), 'result_directory': 'book/coverage/checks/future31-core/current81-canonical-pairs6-v1', 'source_count': len(rows), 'public_theorem_count': 104, 'public_declaration_count': sum(len(r['public_declarations']) for r in rows), 'sources': rows, 'coverage_complete': False, 'scope': 'Exact reviewed source bytes and actual previous TMP histories only. Twelve real canonical compiler commands are still required; no owner or whole coverage promotion is performed by this plan.'}
OUT.parent.mkdir(parents=True, exist_ok=True)
with OUT.open('x') as f: f.write(json.dumps(plan, indent=2)+'\n')
print(json.dumps({'status': plan['status'], 'plan': ref(str(OUT)), 'sources': 6, 'public_theorems': 104, 'public_declarations': plan['public_declaration_count'], 'coverage_complete': False}))
