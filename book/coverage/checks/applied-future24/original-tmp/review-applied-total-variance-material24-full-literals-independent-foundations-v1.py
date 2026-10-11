from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/applied-total-variance-material24-three-literals-full-source-review-request-v1.json')
OUT = Path('/tmp/applied-total-variance-material24-three-literals-independent-foundations-review-v1.json')
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
R = lambda path: json.loads(Path(path).read_text())
assert not OUT.exists()
assert H(REQUEST) == '403bb26e78c69dd3ba36516447373c5414dddc21e618b666cce0838864ae6579'
request = R(REQUEST)
checked = {}


def bind(reference):
    path = Path(reference['file'])
    assert H(path) == reference['sha256'], str(path)
    checked[str(path)] = H(path)
    return path


inventory_path = bind(request['current_inventory'])
inventory = R(inventory_path)
assert H(ROOT / 'book/coverage/inventory.json') == H(inventory_path)
page_path = bind(request['source_page'])
source_path = bind(request['new_actual_source'])
source = source_path.read_text()
assert source == request['entire_new_source_and_seven_bodies']
assert H(source_path) == '77f0ff654fe53695f7a3030cad757b7eb97fd01b7b29b03602751a184d296b0a'
assert not re.search(r'\b(sorry|admit|axiom)\b', source)
names = ['SafeLearning.CompleteAppliedTotalVarianceMaterial24.' + n for n in re.findall(r'^theorem (\w+)', source, re.M)]
assert names == request['public_theorem_names'] and len(names) == 7
records = {u['key']: u for u in inventory['material_source_units']}
assert [u['source_unit_key'] for u in request['material_units']] == ['primer-probability.html::node-394', 'primer-probability.html::node-395', 'primer-probability.html::node-396']
for unit in request['material_units']:
    literal = records[unit['source_unit_key']]
    assert literal == unit['entire_inventory_record']
    assert hashlib.sha256(literal['source_text'].encode()).hexdigest() == literal['text_sha256']
    assert literal['source_sha256'] == H(page_path)
    assert set(unit['lean_declarations']) <= set(names)
page_lines = page_path.read_text().splitlines(keepends=True)
for context in request['complete_source_contexts']:
    assert ''.join(page_lines[context['lines_start'] - 1:context['lines_end']]) == context['exact_lines']
assert 'Assume finite second moments for the variance and covariance formulas below.' in page_path.read_text()

history = []
for index, trial in enumerate(request['actual_trial_history'], 1):
    record_path = bind(trial['record'])
    record = R(record_path)
    assert record == trial['entire_actual_record']
    snapshot = bind(trial['source_snapshot'])
    raw = bind(trial['raw_log'])
    runner = bind(trial['actual_runner'])
    assert record['actual_command'] == ['lake', 'env', 'lean', str(source_path)]
    assert record['actual_workdir'] == str(ROOT / 'verification/lean')
    assert record['actual_exit_code'] == (0 if index == 3 else 1)
    assert record['source_unchanged'] and record['source_sha256_before'] == record['source_sha256_after'] == H(snapshot)
    assert record['source_snapshot'] == str(snapshot) and record['source_snapshot_sha256'] == H(snapshot)
    assert record['log'] == str(raw) and record['log_sha256'] == H(raw)
    assert record['actual_runner'] == str(runner) and record['actual_runner_sha256'] == H(runner)
    runner_text = runner.read_text()
    assert 'subprocess.run' in runner_text and 'r.returncode' in runner_text and 'source_snapshot' in runner_text
    assert record['elapsed_seconds'] > 0 and record['started_at_utc'] < record['finished_at_utc']
    if index == 3:
        assert snapshot.read_bytes() == source_path.read_bytes() and raw.read_bytes() == b''
    else:
        assert 'error' in raw.read_text()
    history.append({'original_trial': index, 'record': trial['record'], 'entire_original_actual_record': record, 'raw_log': trial['raw_log'], 'source_snapshot': trial['source_snapshot'], 'actual_runner': trial['actual_runner']})
for reference in request['direct_primary_mathlib_sources']:
    bind(reference)
primary_reads = [
    ('Mathlib/Probability/CondVar.lean', 30, 145),
    ('Mathlib/Probability/Moments/Covariance.lean', 39, 68),
    ('Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean', 235, 257),
    ('Mathlib/MeasureTheory/SpecificCodomains/Pi.lean', 27, 53),
]
primary_excerpts = []
for suffix, first, last in primary_reads:
    path = ROOT / 'verification/lean/.lake/packages/mathlib' / suffix
    primary_excerpts.append({'file': str(path), 'sha256': H(path), 'lines_start': first, 'lines_end': last, 'exact_lines': ''.join(path.read_text().splitlines(keepends=True)[first-1:last])})
manifest_path = bind(request['protected_selected22_manifest'])
manifest = R(manifest_path)
assert len(manifest['proof_files']) == 1113
for name in manifest['proof_files']:
    assert H(ROOT / name) == manifest['frozen_inputs_sha256'][name], name
held23_offer = ROOT / 'book/coverage/checks/foundations-future23/source51/foundations-audit23-candidate-source51-additions-v2-reviewed.json'
assert H(held23_offer) == '6013506de49ecde2dada1e10e628233fc574ebf60bc499c6386aab68b4a7d49e'

reason = (
    'Read all seven complete theorem bodies, definitions, all three full literals and both source contexts. '
    'The finite-second-moment assumption at line178 covers this theorem box. The two towers use genuine '
    'conditional expectation integrals; the second-moment identity is almost-everywhere, and total variance '
    'is proved under MemLp2 on an arbitrary probability law. Measurable Y is handled through its actual '
    'comap sigma algebra. Conditional covariance is defined as the actual conditional expectation of '
    'the centered product, then expanded using L2 product integrability and measurable pull-out. The '
    'scalar cross-covariance identity follows from the actual raw-moment formula and both towers. '
    'For any finite coordinate type, each centered conditional product is integrable and both finite '
    'evaluation/integral commutations are justified; thus the displayed vector equality uses the genuine '
    'matrix-valued Bochner integral. No covariance decomposition, independence, Gaussian law, or '
    'desired total-variance equality is assumed. All clauses of the theorem box and inner body match.'
)
units = []
for unit in request['material_units']:
    units.append({
        'source_unit_key': unit['source_unit_key'], 'entire_inventory_record': unit['entire_inventory_record'],
        'material_status': 'proved', 'whole_unit_approved': True,
        'lean_declarations': unit['lean_declarations'], 'hypotheses': unit['hypotheses'],
        'components': unit['candidate_components'], 'per_unit_reason': reason if unit['source_unit_key'] != 'primer-probability.html::node-395' else 'The complete heading asserts the actual scalar total-variance theorem, including arbitrary measurable-Y conditioning, under the inherited finite-second-moment scope. Its theorem body and surrounding full box were read.',
        'missing_clauses': [],
    })
report = {
    'status': 'passed_independent_full_three_literal_total_variance_covariance_source_review_future24_tmp_only',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'reviewer': '/root/config21_next',
    'actual_checker': str(Path(__file__)), 'actual_checker_sha256': H(__file__),
    'original_request': {'file': str(REQUEST), 'sha256': H(REQUEST)}, 'entire_original_request_body_and_time': request,
    'new_actual_source': request['new_actual_source'], 'entire_source_and_all_seven_bodies': source,
    'material_units': units, 'whole_mathematical_units_approved': 3, 'public_theorem_names': names,
    'direct_primary_reads': primary_excerpts, 'original_actual_trial_history': history,
    'checked_artifact_sha256': checked, 'all1113_selected22_source_hashes_exact': True,
    'held_foundation23_final_offer': {'file': str(held23_offer), 'sha256': H(held23_offer)},
    'scope_limits': [
        'Finite second moments for scalar variables and every finite vector coordinate; measurable conditioning Y or a conditioning sigma algebra no finer than ambient.',
        'Conditional representative identities are almost-everywhere. The identities are equalities of actual probability-law moments and matrix-valued Bochner integrals.',
        'The first tower theorem uses total Bochner-integral conventions for arbitrary X; this whole-literal approval invokes it in the page L2 scope, where the needed integrability holds.',
        'Three physical records include their wrapper and mathematical heading. Nearby expectation, covariance-transformation, correlation and predictor-optimality claims are context, not additional approved units.',
        'Actual trial3 is TMP standalone only. No canonical source, named build, current ledger installation, selection, aggregate24, or checkpoint23 amendment is inferred.',
    ],
    'errors': [], 'coverage_complete': False,
}
with OUT.open('x') as output:
    output.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(OUT), 'sha256': H(OUT), 'whole_units': 3, 'public_theorem_count': 7}))
