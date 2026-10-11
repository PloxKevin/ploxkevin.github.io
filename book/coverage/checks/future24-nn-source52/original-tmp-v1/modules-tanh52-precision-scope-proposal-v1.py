from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, shutil, sys

R = Path('/home/oxrexkevin/SafetyBased')
D = Path('/tmp/modules-tanh52-precision-scope-proposal-v1')
assert not D.exists()
D.mkdir()
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref = lambda p: {'file': str(p), 'sha256': sha(p)}
read = lambda p: json.loads(Path(p).read_text())
source = R / 'SafeLearning/nn-in-the-loop.html'
before = source.read_text()
lines = before.splitlines()
b = next(x for x in lines if '<strong>(b)</strong>' in x and '0.7616' in x)
c = next(x for x in lines if '<strong>(c)</strong>' in x and '0.762' in x)
newb = r'''            <p><strong>(b)</strong> $\tilde v^{\top}\mathsf M\tilde\phi(\tilde v)=(\tilde v_1-\tilde v_2)\big(\tilde\varphi_1(\tilde v_1)-\tilde\varphi_2(\tilde v_2)\big)$. At $(-1,-1.5)$: $\tilde\varphi_1(-1)\approx-0.7616$ and $\tilde\varphi_2(-1.5)=\tanh0.5-\tanh2\approx-0.5019$, so the difference is approximately $-0.2597$ and the actual QC value is $0.5\big(\tanh(-1)-\tanh0.5+\tanh2\big)\approx-0.130\lt0$. A certificate that requires this QC for all shifted inputs has an invalid premise; this counterexample alone does not show that its final stability conclusion is false. Two different functions can be "out of order", which one monotone function never is.</p>'''
newc = r'''            <p style="margin-bottom:0;"><strong>(c)</strong> Bias-free at $x_*=0$ means $v_*=0$ for all neurons (because $\tanh0=0$, every layer's equilibrium is $0$), so $\tilde\varphi_1=\tilde\varphi_2=\tanh$ and $(\tilde v_1-\tilde v_2)(\tanh\tilde v_1-\tanh\tilde v_2)\ge0$ by monotonicity; with the sector terms this is the doubly hyperdominant lemma of Section 3. Being bias-free is sufficient, not necessary: neurons with equal $v_{*,i}$ would share one shifted function too, but here $v_{*,1}\ne v_{*,2}$. (With local slope bounds, a coupled multiplier also needs one common pair $(\mu,\nu)$ for the coupled neurons; Section 3.) Without additional shared-function assumptions, valid choices after the shift include the circle multipliers, which use each neuron's own sector (the diagonal one, here $\tilde v_1\tilde\varphi_1\approx0.762$ and $\tilde v_2\tilde\varphi_2\approx0.753$, with both actual products nonnegative, and also the full-block one, which is required to be nonnegative for every diagonal gain matrix in the sector box and therefore holds for any diagonal nonlinearity). The ordinary monotone Zames&ndash;Falb class with diagonal $M_j$ also remains valid under Section 3's coefficient signs and row/column sums, each channel's slope bounds, and zero initial filter state for the hard IQC. Time invariance keeps the same scalar function at different times; finite-horizon nonnegativity also needs these multiplier conditions. The enlarged odd-nonlinearity class additionally requires the shifted channel to be odd, which a nonzero tanh shift generally is not. The same failure of the coupled LipSDP-Network multiplier is why the offset-free analysis (Section 4) and the incremental certificates (Section 5, Module 12) use a diagonal $T$.</p>'''
replacements = [
    {'before': b, 'after': newb, 'count': 1, 'reason': 'Separate four rigorous rounded displays from actual irrational values and their exact strictly negative QC. Scope invalid-premise language without asserting every particular downstream stability conclusion is false.'},
    {'before': c, 'after': newc, 'count': 1, 'reason': 'Qualify the two rounded diagonal products, preserve their true nonnegativity, and state the independent-channel circle and temporal Zames-Falb hypotheses explicitly. Diagonal temporal coupling is justified by the hard-IQC theorem with its coefficient and zero-state conditions, rather than time invariance alone; the odd class has its additional actual oddness premise.'},
]
after = before
for row in replacements:
    assert after.count(row['before']) == 1
    after = after.replace(row['before'], row['after'], 1)
reverse = after
for row in reversed(replacements):
    assert reverse.count(row['after']) == 1
    reverse = reverse.replace(row['after'], row['before'], 1)
assert reverse == before and before.count('\n') == after.count('\n')
before_path = D / 'nn-in-the-loop-source51-before.html'
after_path = D / 'nn-in-the-loop-proposed52-after.html'
before_path.write_text(before); after_path.write_text(after)
sys.path.insert(0, str(R / 'book'))
from validate import Document
a, z = Document(before), Document(after)
assert len(a.nodes) == len(z.nodes)
assert all((x.tag, x.attrs, x.line) == (y.tag, y.attrs, y.line) for x, y in zip(a.nodes, z.nodes))
sim = D / 'simulation'
(sim / 'SafeLearning').mkdir(parents=True)
for p in (R / 'SafeLearning').glob('*.html'):
    shutil.copy2(p, sim / 'SafeLearning' / p.name)
(sim / 'SafeLearning/nn-in-the-loop.html').write_text(after)
spec = importlib.util.spec_from_file_location('inventory_claims_tanh52_proposal', R / 'book/inventory_claims.py')
generator = importlib.util.module_from_spec(spec); spec.loader.exec_module(generator)
generator.ROOT = sim; generator.OUT = sim / 'book/coverage'
generator.inventory()
old = read(R / 'book/coverage/inventory-after-correction51.json')
new = read(generator.OUT / 'inventory.json')
delta = {}
for section in ('exercises', 'material_source_units'):
    x, y = old[section], new[section]
    assert len(x) == len(y)
    assert [u['key'] for u in x] == [u['key'] for u in y]
    changed = []
    for u, v in zip(x, y):
        assert {k:w for k,w in u.items() if k not in ('source_sha256', 'source_text', 'text_sha256')} == {k:w for k,w in v.items() if k not in ('source_sha256', 'source_text', 'text_sha256')}
        if u['source_text'] != v['source_text']:
            changed.append(u['key'])
        else:
            assert u['text_sha256'] == v['text_sha256']
        if u['source'] != 'SafeLearning/nn-in-the-loop.html':
            assert u == v
    delta[section] = changed
assert delta == {'exercises': ['nn-in-the-loop.html::exercise-20'], 'material_source_units': ['nn-in-the-loop.html::node-1260', 'nn-in-the-loop.html::node-1262']}
proofs = [Path('/tmp/modules-tanh-offset24-trial3.lean'), Path('/tmp/modules-tanh-offset24-trial5.lean'), Path('/tmp/modules-tanh-sector24-trial2.lean')]
records = [Path('/tmp/modules-tanh-offset24-trial3.json'), Path('/tmp/modules-tanh-offset24-trial5.json'), Path('/tmp/modules-tanh-sector24-trial2.json')]
actual = []
for p in records:
    j = read(p); assert j['actual_exit_code'] == 0
    actual.append({'record': ref(p), 'entire_original_record_body_and_time': j})
peers = [Path('/tmp/modules-nn-tanh-offset24-independent-foundations-source-component-review-v1.json'), Path('/tmp/modules-nn-tanh-seven-bridges24-independent-foundations-component-review-v1.json')]
for p in peers:
    assert read(p)['errors'] == []
manifest = read(R / 'reports/full-coverage/checkpoint-23-manifest.json')
assert len(manifest['proof_files']) == 1131
for p, row in manifest['proof_files'].items():
    assert sha(R / p) == row['sha256']
assets = {n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31
for n,d in assets.items(): assert sha(R / n) == d
live_inputs = ['book/coverage/' + n + '.json' for n in ('core', 'foundations', 'applied', 'modules', 'applied-promotions', 'inventory')]
source_lines = before.splitlines()
section3 = '\n'.join(source_lines[270:307])
out = {'schema_version': 1, 'status': 'read_only_proposed_two_paragraph_precision_and_static_temporal_scope_correction_requires_independent_semantic_primary_source_and_fresh_parser_review', 'prepared_by': '/root/modules_resume', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'correction_index_proposed': None, 'source': 'SafeLearning/nn-in-the-loop.html', 'inventory': 'book/coverage/inventory-after-correction51.json', 'inventory_sha256': sha(R / 'book/coverage/inventory-after-correction51.json'), 'source_sha256_before': sha(source), 'proposed_source_sha256_after': sha(after_path), 'source_bytes_before_snapshot': ref(before_path), 'source_bytes_proposed_after_snapshot': ref(after_path), 'replacements': replacements, 'expected_changed_text_keys': delta, 'six_display_precision_qualifications': ['tanh(-1) approximately -0.7616', 'tanh(0.5)-tanh(2) approximately -0.5019', 'the channel difference approximately -0.2597', 'the actual QC approximately -0.130', 'the first diagonal product approximately 0.762', 'the second diagonal product approximately 0.753'], 'original_semantic_component_peers': [ref(p) for p in peers], 'actual_proof_sources': [ref(p) for p in proofs], 'actual_original_TMP_zero_records': actual, 'direct_local_Section3_source_context': {'file': 'SafeLearning/nn-in-the-loop.html', 'source_sha256': sha(source), 'lines_start': 271, 'lines_end': 307, 'exact_lines': section3}, 'primary_source_scope': {'url': 'https://arxiv.org/pdf/2103.17106', 'paper': 'Pauli, Gramlich, Berberich, Allgower, CDC2021, arXiv2103.17106v2', 'locations': ['Section II-D multiplier sign and row/column conditions and hard IQC theorem', 'Section II-E diagonal M_j for non-repeated nonlinearities', 'Appendix B finite zero-padded sequence proof and the non-repeated diagonal specialization'], 'independent_primary_source_review_required': True}, 'fresh_full29_parser': {'counts': {'exercises': len(new['exercises']), 'material_source_units': len(new['material_source_units'])}, 'simulated_inventory': ref(generator.OUT / 'inventory.json'), 'actual_changed_text_keys': delta, 'all_other_literal_text_and_all_structural_fields_unchanged': True, 'all_DOM_tags_attributes_lines_and_node_count_unchanged': True, 'exact_forward_and_reverse_replacement': True}, 'protected_selected23_source_count': 1131, 'all_selected23_proof_sources_and31_live_assets_exact': True, 'live_owner_and_inventory_bytes_at_preparation': {n: sha(R/n) for n in live_inputs}, 'proposal_helper': ref(Path(__file__)), 'remaining_semantic_gaps_preserved': ['This is not a whole Exercise14.6 approval.', 'The new Lean component pack does not prove the full arbitrary finite-horizon temporal Zames-Falb theorem or the complete doubly hyperdominant repeated class; those are primary theorem attributions here and remain separately pending for formal whole-source review.', 'The coupled local-bound generality and final Module12/Sections4-5 attribution require their own exact correspondence.'], 'scope': 'TMP-only reversible proposal; no HTML, inventory, live owner, selection, original review body/time, or already-passed proof mutation. No source52 assignment or application claim.'}
target = Path('/tmp/modules-nn-tanh-precision-temporal-scope-proposal52-v1.json')
assert not target.exists(); target.write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'proposal': ref(target), 'changed_text_keys': delta}))
