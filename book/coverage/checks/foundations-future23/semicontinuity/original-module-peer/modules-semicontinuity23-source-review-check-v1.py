from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQ = Path('/tmp/foundations-semicontinuity23-basics1202-1237-full-source-review-request-v1.json')
OUT = Path('/tmp/foundations-semicontinuity-two-literals-independent-modules-source-review23-v1.json')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
J = lambda p: json.loads(Path(p).read_text())
REF = lambda p: {'file': str(p), 'sha256': H(p)}
assert not OUT.exists()
assert H(REQ) == '430909a23b6ad13222b9e2fc6cd4adadcf5f21676b06863bcb4cd6b9b3ef418a'
r = J(REQ)
old_inv = ROOT / 'book/coverage/inventory-after-correction48.json'
assert H(old_inv) == r['inventory']['sha256']
inv = J(old_inv)
cur_inv = J(ROOT / 'book/coverage/inventory.json')
old_units = {x['key']: x for x in inv['material_source_units']}
cur_units = {x['key']: x for x in cur_inv['material_source_units']}
old_ex = {x['key']: x for x in inv['exercises']}
cur_ex = {x['key']: x for x in cur_inv['exercises']}
manifest = J(ROOT / r['protected_selected22_manifest']['file'])
assert H(ROOT / r['protected_selected22_manifest']['file']) == r['protected_selected22_manifest']['sha256']
snapshot = ROOT / manifest['snapshot']
for p, d in manifest['proof_files'].items():
    assert H(ROOT / p) == d['sha256'], ('selected22 source', p)
assert len(manifest['proof_files']) == 1113
frozen_assets = {}
held_ledgers = {}
for p, expected in r['protected_current48_assets_inventory_and_four_working22_ledger_sha256'].items():
    if p.startswith('SafeLearning/'):
        assert H(snapshot / p) == expected, ('frozen48 asset', p)
        frozen_assets[p] = expected
    elif p.endswith('inventory.json'):
        assert H(snapshot / p) == expected
    else:
        assert H(ROOT / p) == expected, ('held22 ledger', p)
        held_ledgers[p] = expected
assert len(frozen_assets) == 31 and len(held_ledgers) == 4
source = Path('/tmp/foundations-semicontinuity23-trial2.lean')
assert H(source) == '280be25369c9cc9b3336d87ada8e5cf4d899cd454da1a4cabcf33725cb612b14'
body = source.read_text()
names = ['SafeLearning.CompleteFoundationsSemicontinuity23.' + n
         for n in re.findall(r'^theorem\s+(\w+)', body, re.M)]
assert names == r['public_theorem_names'] and len(names) == 10
assert not re.search(r'\bsorry\b|\badmit\b|^axiom\s', body, re.M)
assert body.count('FirstCountableTopology X') == 1
assert 'liminf (fun n => (f (u n) : EReal)) atTop' in body
assert body == r['source_file']['entire_immutable_TMP_source_body'] if 'source_file' in r else True
for t in r['all_actual_unique_trial_history']:
    for k in ['record', 'source_snapshot', 'raw_log']:
        rr = t[k]; assert H(rr['file']) == rr['sha256'], (k, rr['file'])
    rec = J(t['record']['file'])
    assert rec == t['entire_original_actual_record']
    assert rec['source_sha256_before'] == rec['source_sha256_after'] == t['source_snapshot']['sha256']
    assert rec['command'] == ['lake', 'env', 'lean', t['source_snapshot']['file']]
    assert rec['raw_log_sha256'] == t['raw_log']['sha256']
assert J(r['actual_original_standalone']['record']['file'])['actual_exit_code'] == 0
assert J(r['all_actual_unique_trial_history'][0]['record']['file'])['actual_exit_code'] == 1
raw = Path(r['actual_original_standalone']['raw_log']['file']).read_text()
assert raw.count('warning:') == 7 and 'error:' not in raw
for p in r['local_primary_Mathlib_semantics']:
    assert H(ROOT / p['file']) == p['sha256']
assert H(r['actual_runner']['file']) == r['actual_runner']['sha256']
html = ROOT / 'SafeLearning/primer-basics.html'
assert H(html) == 'd6e03363fed45ed19f2747cf29d7c7cfed4c6b163aceeecf93c9fba21321d3d0'
context = r['full_source_HTML_context']
lines = html.read_text().splitlines(keepends=True)
assert ''.join(lines[context['first_line']-1:context['last_line']]) == context['exact_lines']
parent = r['full_parent_exercise_record']
assert old_ex[parent['key']] == parent == cur_ex[parent['key']]
for x in r['material_units']:
    rec = x['entire_inventory_record']
    assert old_units[rec['key']] == rec == cur_units[rec['key']]
    assert hashlib.sha256(rec['source_text'].encode()).hexdigest() == rec['text_sha256']
    assert rec['source_text'] in parent['source_text'] or rec['key'].endswith('1202')

prefix = 'SafeLearning.CompleteFoundationsSemicontinuity23.'
decl = lambda *xs: [prefix+x for x in xs]
components = [
    {'id': 'closed-sublevel-equivalence', 'source_unit_keys': ['primer-basics.html::node-1202'],
     'lean_declarations': decl('actual_lower_semicontinuity_iff_closed_sublevels'),
     'hypotheses': 'Arbitrary topological domain and real-valued f; every real threshold c.',
     'reason': 'The exported iff uses the actual lower-semicontinuity definition and all closed inverse images of Iic c, exactly the closed-sublevel characterization.'},
    {'id': 'genuine-sequential-liminf-equivalence', 'source_unit_keys': ['primer-basics.html::node-1202'],
     'lean_declarations': decl('actual_lower_semicontinuity_iff_all_sequence_liminf_bounds'),
     'hypotheses': 'First-countable topological domain (including the source Euclidean setting), real-valued f, every sequence converging to x; liminf taken in EReal.',
     'reason': 'Both directions are proved. Forward uses all strict real lower thresholds and eventual sequence bounds. Reverse extracts an actual bad sequence from frequent values below a threshold, then derives f(x) <= liminf <= limsup <= threshold. No desired conclusion is an assumption, and EReal handles unbounded sequences.'},
    {'id': 'nonempty-compact-lsc-minimum', 'source_unit_keys': ['primer-basics.html::node-1202'],
     'lean_declarations': decl('actual_lower_semicontinuous_compact_set_has_a_minimizer', 'actual_lower_semicontinuous_compact_sublevels_are_compact'),
     'hypotheses': 'Compact K, K.Nonempty for attainment, real-valued f lower semicontinuous on K.',
     'reason': 'The actual compact lower-semicontinuity theorem supplies x in K attaining the least value, with nonemptiness explicitly supplied by the corrected paragraph. Compact sublevels are separately derived.'},
    {'id': 'actual-zero-one-step', 'source_unit_keys': ['primer-basics.html::node-1202'],
     'lean_declarations': decl('actual_printed_step_values', 'actual_printed_step_all_sublevel_sets', 'actual_printed_step_is_lower_semicontinuous'),
     'hypotheses': 'Actual step on all real x: zero for x<=0, one for x>0; arbitrary real threshold c.',
     'reason': 'The function exactly matches the printed endpoints. Sublevels are empty for c<0, Iic 0 for 0<=c<1, and all reals for c>=1. These actual closed sets derive lower semicontinuity.'},
    {'id': 'compact-minimum-sufficient', 'source_unit_keys': ['primer-basics.html::node-1237'],
     'lean_declarations': decl('actual_compactness_is_sufficient_for_continuous_minimum'),
     'hypotheses': 'ContinuousOn f K on a compact nonempty set. The full T2 parent has nonempty specified domains.',
     'reason': 'The generic genuine compact theorem supplies the attained minimum. The hint is read in its nonempty-domain exercise context.'},
    {'id': 'compactness-not-necessary-square', 'source_unit_keys': ['primer-basics.html::node-1237'],
     'lean_declarations': decl('actual_real_line_is_not_compact', 'actual_printed_square_attains_unique_minimum_on_noncompact_real_line'),
     'hypotheses': 'Actual continuous f(x)=x^2 on all real numbers.',
     'reason': 'Noncompactness is proved by a hypothetical compact maximum of identity and the violating point x+1. The continuous square has minimum zero attained uniquely at zero on that actual noncompact domain, so compactness is not necessary.'}
]
units = []
for x in r['material_units']:
    rec = x['entire_inventory_record']; key = rec['key']
    groups = [g for g in components if key in g['source_unit_keys']]
    ds = list(dict.fromkeys(n for g in groups for n in g['lean_declarations']))
    units.append({'source_unit_key': key, 'source': rec['source'], 'source_sha256': rec['source_sha256'],
                  'line': rec['line'], 'locator': rec['locator'], 'source_text': rec['source_text'],
                  'unit_text_sha256': rec['text_sha256'], 'entire_inventory_record': rec,
                  'status': 'approved_complete_source', 'material_status': 'proved',
                  'whole_unit_approved': True, 'lean_declarations': ds,
                  'hypotheses': [g['hypotheses'] for g in groups],
                  'per_unit_reason': ' '.join(g['reason'] for g in groups),
                  'approved_components': groups, 'missing_clauses': [],
                  'individually_scoped_instruction_or_attribution':
                    'Module8 is a directly read internal cross-reference to budget-boundary lower semicontinuity; it does not assert that the exact step appears there or approve that module\'s MDP theorems.'
                    if key.endswith('1202') else
                    'Find the infimum first is proof guidance. This hint approval does not promote its parent exercise or the parent\'s separate infimum/nonattainment/coercivity answers.'})
module8 = snapshot / 'SafeLearning/cmdp.html'
ml = module8.read_text().splitlines(keepends=True)
module8excerpt = ''.join(ml[672:686])
assert 'state-augmentation' in module8excerpt and 'lower semicontinuous' in module8excerpt
report = {
 'status': 'independent_complete_literal_source_review_passed',
 'reviewer': '/root/modules_resume', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
 'inventory': str(old_inv.relative_to(ROOT)), 'inventory_sha256': H(old_inv),
 'source': str(html.relative_to(ROOT)), 'source_sha256': H(html),
 'original_review_request': REF(REQ), 'material_units': units,
 'full_parent_exercise_record_read': parent, 'full_source_HTML_context_read': context,
 'entire_new_TMP_source_body_read': body, 'new_public_theorem_names': names,
 'actual_new_proof_evidence': r['actual_original_standalone'],
 'actual_original_failure_history': r['all_actual_unique_trial_history'],
 'warning_log_scope': 'Seven genuine deprecation warnings retained; original standalone trial2 exit0. Failed trial1 exit1 remains exact.',
 'local_primary_Mathlib_semantics': r['local_primary_Mathlib_semantics'],
 'direct_internal_Module8_attribution': {
   'file': str(module8.relative_to(ROOT)), 'sha256': H(module8), 'first_line': 673, 'last_line': 686,
   'exact_excerpt_read': module8excerpt,
   'scope': 'Internal reading pointer to lower-semicontinuity of the cost at the budget boundary, conditional n>=c and continuous c. No whole Module8 theorem, infinite-penalty argument, direction-of-jump prose or literal duplication claim is approved.'},
 'protected_selected22': {'manifest': r['protected_selected22_manifest'], 'source_count': 1113,
                         'all_source_hashes_exact': True, 'frozen48_asset_sha256': frozen_assets,
                         'held_working22_ledger_sha256': held_ledgers},
 'current_unchanged_Basics_identity_observation': {'inventory': REF(ROOT / 'book/coverage/inventory.json'),
                                               'two_entire_unit_records_and_parent_equal_original48': True},
 'actual_checker': str(Path(__file__)), 'actual_checker_sha256': H(__file__),
 'errors': [], 'coverage_complete': False,
 'limits': ['Both complete physical units only are approved, in the source real/Euclidean setting. Parent exercise is not promoted.',
            'Original request, previous pending rows, proof attempts, commands, times, warnings and failed trial bytes are preserved.',
            'New proof is genuine TMP standalone only; no canonical source, named build, live owner mapping or aggregate23 is claimed.',
            'Frozen22 source48 assets bind the old source baseline. Current unchanged Basics whole records and parent are independently checked, so a separate unrelated Monitoring correction does not falsify the historical scope.']}
OUT.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'output': str(OUT), 'sha256': H(OUT), 'whole_units': 2, 'public_theorems': 10}))
