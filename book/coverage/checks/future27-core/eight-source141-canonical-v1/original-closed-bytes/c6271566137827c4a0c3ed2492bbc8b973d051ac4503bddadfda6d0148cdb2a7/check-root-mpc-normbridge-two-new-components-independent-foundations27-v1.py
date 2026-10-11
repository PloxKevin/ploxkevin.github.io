from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

R = Path('/home/oxrexkevin/SafetyBased')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
REF = lambda p: {'file': str(p), 'sha256': H(p)}
oldp = Path('/tmp/root-mpc-normbridge5-source54-proposal3-independent-modules-full-component-review27-v1.json')
assert H(oldp) == '0f5d29c601d50295c4c17879dc7af4d0cf141d554ee38683fdf5b689b5399d30'
old = json.loads(oldp.read_text())
oldsource = Path(old['source']['file'])
assert H(oldsource) == old['source']['sha256'] and oldsource.read_text() == old['entire_source']
source = Path('/tmp/CompleteCoreMPCNormBridge27-draft-v4.lean')
assert H(source) == '01bcf4e93bf876705ffefed124666e02b195ca40f986730f35750fd18d9dee0b'
s = source.read_text()
names = re.findall(r'^theorem (\w+)', s, re.M)
assert len(names) == 7 and not re.search(r'\b(?:sorry|admit|axiom)\b', s)
first = s[:s.index('theorem actual_polytopic_state_constraint_set_is_convex')].rstrip()
oldfirst = oldsource.read_text().split('end SafeLearning.CompleteCoreMPCNormBridge27')[0].rstrip()
assert first.replace('import Mathlib.Analysis.Convex.Basic\n', '', 1) == oldfirst
history = []
for i, code in [(1, 1), (2, 0), (3, 1), (4, 0)]:
    path = Path(f'/tmp/root-mpc-normbridge27-trial{i}.json')
    a = json.loads(path.read_text())
    assert type(a['actual_exit_code']) is int and a['actual_exit_code'] == code
    assert type(a['actual_runner_exit_code']) is int and a['actual_runner_exit_code'] == code
    assert a['protection_errors'] == []
    assert a['actual_workdir'] == str(R / 'verification/lean')
    assert a['actual_command'] == ['lake', 'env', 'lean', a['source']]
    assert H(a['source']) == H(a['source_snapshot']) == a['source_sha256_before'] == a['source_sha256_after'] == a['source_snapshot_sha256']
    assert H(a['raw_log']) == a['raw_log_sha256']
    assert H(a['original_actual_runner']['file']) == a['original_actual_runner']['sha256']
    history.append({'record': REF(path), 'entire_original_record_and_time': a, 'raw_log': REF(a['raw_log']), 'source_snapshot': REF(a['source_snapshot'])})
actual = history[-1]['entire_original_record_and_time']
assert actual['source'] == str(source)
assert Path(actual['raw_log']).read_text().count(': warning:') == 1
for key in ['installed26_owner_sha256', 'original_installed26_provenance_sha256']:
    for name, digest in actual[key].items():
        assert H(R / name) == digest
selection = json.loads((R / 'reports/full-coverage/checkpoint-26-selection.json').read_text())
assert len(selection['proof_files']) == 1167
for name, row in selection['proof_files'].items():
    assert H(R / name) == row['sha256']
assets = json.loads((R / 'reports/full-coverage/browser-corrections-26-inputs.json').read_text())['source_sha256']
assert len(assets) == 31
for name, digest in assets.items():
    assert H(R / name) == digest
primary = R / old['primary']['file']
assert H(primary) == old['primary']['sha256']
for name, digest in old['evidence_sha256'].items():
    p = Path(name) if Path(name).is_absolute() else R / name
    assert H(p) == digest
api = R / 'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean'
alines = api.read_text().splitlines(keepends=True)
passages = [{'file': str(api), 'sha256': H(api), 'first_line': lo, 'last_line': hi, 'exact_excerpt': ''.join(alines[lo-1:hi])} for lo, hi in [(90, 105), (245, 268)]]
ns = 'SafeLearning.CompleteCoreMPCNormBridge27.'
components = [
 {'component_id': 'actual_polytopic_constraint_set_convexity', 'lean_declarations': [ns + names[5]], 'hypotheses': ['Actual finite real matrix H, Euclidean state coordinates and arbitrary real common row margin.'], 'per_component_reason': 'Each actual H row is a real linear functional through the Euclidean coordinate equivalence and Matrix.mulVecLin. Its genuine sublevel halfspace is convex, and convex_iInter proves convexity of the exact simultaneous row constraints. Empty row/domain possibilities cause no missing existence assertion.', 'missing_clauses': []},
 {'component_id': 'positive_lambda_assumption3_local_quadratic_budget', 'lean_declarations': [ns + names[6]], 'hypotheses': ['lambda>0, eta>=0, delta>0 and cU>0.', 'The actual Assumption3 inequality eta<=lambda inverse*sqrt(delta/cU).'], 'per_component_reason': 'Multiplication by positive lambda gives lambda*eta<=sqrt(delta/cU). Both sides are nonnegative; squaring and the true square-root identity give the quadratic ratio bound, then positive cU clears the denominator to cU*(lambda*eta)^2<=delta. This is the numerical consequence of Assumption3. Supplying V_delta upper-bound premises and actual trajectory-domain membership remains separate.', 'missing_clauses': []}
]
out = Path('/tmp/root-mpc-normbridge-two-new-components-independent-foundations-review27-v1.json')
assert not out.exists()
evidence = {str(oldp): H(oldp), str(source): H(source), str(Path(__file__)): H(__file__), str(primary): H(primary), str(api): H(api)}
for t in history:
    for k in ['record', 'raw_log', 'source_snapshot']:
        evidence[t[k]['file']] = t[k]['sha256']
    evidence[t['entire_original_record_and_time']['source']] = H(t['entire_original_record_and_time']['source'])
body = {'status': 'independent_two_new_normbridge_components_source_review_passed', 'errors': [], 'reviewer': 'Independent Foundations agent; Root authored these two new proofs', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'source': REF(source), 'entire_source': s, 'all_seven_complete_bodies_read': True, 'public_theorem_count': 7, 'two_new_precise_components': components, 'original_five_component_review': REF(oldp), 'entire_original_five_review_body_and_time': old, 'exact_original_five_bodies_unchanged_with_one_additional_import': True, 'genuine_failed_and_passed_compiler_history': history, 'actual_standalone_warning_groups': 1, 'source53_assumptions_exact_original_context_read': old['current_assumptions_lines504_514'], 'complete_primary_assumptions_and_domain_passages_read': {'domain': old['complete_primary_domain_notation_lines78_165'], 'assumptions': old['complete_primary_lines166_234']}, 'primary_api_passages_read': passages, 'current1167_sources31_assets5_owners_rehashed_exact': True, 'whole_exercise_approved': False, 'whole_material_unit_approved': False, 'remaining_gaps': old['remaining_gaps'], 'scope': 'TMP-only precise two-body mathematical review. Original five components and Source54 proposal decision remain exact. No whole incremental certificate, domain-membership construction, optimizer, shifted feasibility, all-time MPC, source edit, canonical/named build, coverage or aggregate claim.', 'closed_evidence_sha256': evidence}
out.write_text(json.dumps(body, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'status': 'passed', 'peer': REF(out), 'new_components': 2, 'original_components_preserved': 5}))
