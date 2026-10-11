from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
ref = lambda p: {'file': str(p), 'sha256': H(p)}
request = Path('/tmp/modules-smoothing-randomized-seven-wrappers26-independent-review-request-v1.json')
assert H(request) == '40bdbd697d2979f7433d26ce9fa6c28834e0efd6fa75f6597419722e12a9ff86'
d = read(request)
for key in ['source', 'original37_source', 'original37_independent_review',
            'original_full_literal_request', 'actual_new_pass_record',
            'actual_new_pass_raw_log', 'source_snapshot']:
    r = d[key]
    assert H(r['file']) == r['sha256'], key
source = Path(d['source']['file']).read_text()
base = Path(d['original37_source']['file']).read_text()
prior = read(d['original37_independent_review']['file'])
literal = read(d['original_full_literal_request']['file'])
assert source == d['entire_source_body'] == Path(d['source_snapshot']['file']).read_text()
assert base == d['original37_source_entire_body_unchanged_prefix'] and source.startswith(base)
assert source[len(base):] == d['complete_new_statement_and_proof_bodies']
assert prior == d['entire_original37_independent_review_body_and_time']
assert literal == d['entire_original_literal_request']
assert not re.search(r'\b(sorry|admit)\b', source)
namespace = ''
names = []
for line in source.splitlines():
    m = re.match(r'namespace\s+(\S+)', line)
    if m:
        namespace = m[1]
    m = re.match(r'theorem\s+(\w+)', line)
    if m:
        names.append(namespace + '.' + m[1])
assert names == d['unchanged_original_public_theorems'] + d['new_public_theorems']
assert len(names) == d['public_theorem_count'] == 44
assert len(d['new_public_theorems']) == d['new_public_theorem_count'] == 7
assert names[:37] == literal['public_theorems']
act = read(d['actual_new_pass_record']['file'])
assert act == d['entire_actual_new_pass_record_and_time']
for key in ['actual_exit_code', 'actual_runner_exit_code']:
    assert type(act[key]) is int and act[key] == 0
assert act['source_sha256_before'] == act['source_sha256_after'] == d['source']['sha256']
assert act['source_unchanged'] is True and act['protection_errors'] == []
assert act['actual_command'] == ['lake', 'env', 'lean', d['source']['file']]
assert act['actual_workdir'] == str(ROOT / 'verification/lean')
assert H(act['raw_log']) == act['raw_log_sha256'] == d['actual_new_pass_raw_log']['sha256']
log = Path(act['raw_log']).read_text()
warnings = re.findall(r'^.*\.lean:\d+:\d+: warning:', log, re.M)
assert len(warnings) == 6
assert not re.search(r'^.*\.lean:\d+:\d+: error(?:\(|:)', log, re.M)
for p, h in d['all_original_new_trial_bytes_sha256'].items():
    assert H(p) == h, p
for trial, code in [(1, 1), (2, 1), (3, 0)]:
    history = read(f'/tmp/modules-smoothing-randomized-kernel26-trial{trial}.json')
    assert type(history['actual_exit_code']) is int and history['actual_exit_code'] == code
    assert history['protection_errors'] == []
    assert H(history['raw_log']) == history['raw_log_sha256']
for row in literal['original_trial_and_source_byte_inputs']:
    assert H(row['file']) == row['sha256'] and Path(row['file']).stat().st_size == row['size_bytes']
inventory = read(literal['current_inventory']['file'])
assert H(literal['current_inventory']['file']) == literal['current_inventory']['sha256']
assert [r for r in inventory['exercises'] if r['key'] == literal['entire_exercise_record']['key']] == [literal['entire_exercise_record']]
current_units = {r['key']: r for r in inventory['material_source_units']}
for row in literal['entire_physical_unit_records']:
    assert current_units[row['key']] == row
page = ROOT / literal['entire_exercise_record']['source']
assert H(page) == literal['entire_exercise_record']['source_sha256']
assert literal['entire_local_section_definition_theorem_np_proof_and_certify_algorithm'] in page.read_text()
selection = read(ROOT / 'reports/full-coverage/checkpoint-25-selection.json')
assert len(selection['proof_files']) == selection['proof_file_count'] == 1156
for p, r in selection['proof_files'].items():
    assert H(ROOT / p) == r['sha256'], p
for p, h in inventory['source_sha256'].items():
    assert H(ROOT / p) == h
for p, h in act['installed25_owner_sha256'].items():
    assert H(ROOT / p) == h
for p, h in act['original_installed25_provenance_sha256'].items():
    assert H(ROOT / p) == h
for row in literal['selected_exact_evidence_and_full_sources_read']:
    assert H(row['source']['file']) == row['source']['sha256']
    assert Path(row['source']['file']).read_text() == row['source_body']
    for evidence in row['checked_evidence']:
        assert H(ROOT / evidence['file']) == evidence['sha256']

new = d['new_public_theorems']
hypotheses = [
    'Finite-dimensional real inner-product/Borel input domain; sigma>0; measurable finite-label base classifier, deterministic or randomized with a fixed measurable seed law independent of the Gaussian draw.',
    'The independent Monte-Carlo confidence procedure in the question supplies a measurable sampling event of probability at least .999 on which the actual selected-class probability is at least Phi(2). This is a probability-bound premise, not a supplied robustness conclusion.',
    'Literal sigma=.5; lower bound Phi(2), or .5 for the abstention case; perturbation inequalities are strict. The infinity-norm clause uses the actual Fin100 coordinate domain.'
]
new_components = [
    {'group': 'generic positive-threshold Gaussian radius and normalized kernel winner',
     'lean_declarations': new[:3], 'component_approved': True, 'hypotheses': hypotheses,
     'reason': 'A nonzero perturbation is normalized to a genuine unit direction, and the previously derived ND bounded-test transfer gives mass above .5 throughout the strict sigma*threshold ball. Integrating the actual pairwise class normalization derives a unique winner; the true CDF quantile inversion supplies the printed radius.', 'missing_clauses': []},
    {'group': 'sampling confidence event uniform over the strict ball',
     'lean_declarations': [new[3]], 'component_approved': True, 'hypotheses': hypotheses,
     'reason': 'The source-given valid confidence event is retained as the same measurable event; on it the probability bound implies the actual kernel winner for every perturbation in the strict ball. The statement is over estimation samples, without a conditional-on-return or fresh confidence-procedure guarantee.', 'missing_clauses': []},
    {'group': 'actual fixed randomization law and Gaussian-product class probabilities',
     'lean_declarations': new[4:], 'component_approved': True, 'hypotheses': hypotheses,
     'reason': 'Integrating the classifier indicator against the fixed genuine seed probability law gives a measurable [0,1]-valued class kernel, with disjoint-label pair sums at most1. Actual product-law indicator integration and Fubini identify the Gaussian-times-seed class probability with its kernel integral. Applying the radius theorem at sigma=.5/Phi2 gives the literal radius1 for the inherited randomized classifier scope.', 'missing_clauses': []}
]
components = prior['components'] + new_components
numeric = names[24:31]
norm_names = names[28:31] + [names[35], names[36]]
units = []
for row in literal['entire_physical_unit_records']:
    key = row['key']
    if key.endswith('1035'):
        declarations = []
        reason = 'The complete prerequisite sentence is an individual navigation instruction with no mathematical assertion.'
        status = 'non_formal'
    elif key.endswith('1041'):
        declarations = [names[24], names[25], names[27]] + new[:3]
        reason = 'The actual CDF-quantile inverse and normalized kernel majority theorem give the single-probability radius in the question domain; the printed Phi2 and .5 cases are both explicitly covered.'
        status = 'proved'
    elif key.endswith('1045'):
        declarations = [names[24], names[25]] + new
        reason = 'Actual Phi2 inverse2 gives .5*2=1. The fixed independent randomization/product-law bridge and sampling-event theorem derive the ideal unique smoothed label throughout every strict Euclidean perturbation of norm<1.'
        status = 'proved'
    elif key.endswith('1047'):
        declarations = norm_names + [new[2], new[4], new[6]]
        reason = 'The actual Fin100 Pi/WithLp2 norm inequality gives Euclidean norm<=10 times infinity norm; strict infinity norm<.1 therefore enters the actual kernel radius1 theorem. No boundary-vector inclusion is inferred.'
        status = 'proved'
    elif key.endswith('1049'):
        declarations = [names[24], names[25], names[27], names[33]] + new[1:]
        reason = 'The valid confidence event is over the given estimation sample law and certifies the actual ideal class probabilities, including randomized base classifiers. True Phi0=.5 and quantile0 produce zero radius; the actual CERTIFY Option rule abstains at .5. The genuine boundary-tie countermodel prevents a positive universal certificate at this threshold.'
        status = 'proved'
    else:
        assert key.endswith('1034')
        declarations = names
        reason = 'Every complete question clause is covered: the actual Phi2 rounding and sigma law, Euclidean radius1, sufficient strict Fin100 infinity radius.1, valid sample-confidence interpretation, randomized ideal classifier correspondence, and zero-radius abstention at lower=.5.'
        status = 'proved'
    units.append({'source_unit_key': key, 'entire_inventory_record': row,
                  'material_status': status, 'whole_unit_approved': True,
                  'lean_declarations': declarations,
                  'hypotheses': [] if status == 'non_formal' else hypotheses,
                  'per_unit_reason': reason, 'components': [] if status == 'non_formal' else components,
                  'missing_clauses': []})
assert sum(u['material_status'] == 'proved' for u in units) == 5
report = {
    'status': 'passed_independent_fresh_full44_body_and_whole_smoothing_practice_review',
    'errors': [], 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'reviewer': 'Independent Applied agent; Modules authored the cumulative44 proof source',
    'request': ref(request), 'entire_exercise_record': literal['entire_exercise_record'],
    'whole_exercise_approved': True, 'whole_exercise_status': 'proved',
    'exercise_lean_declarations': names, 'exercise_hypotheses': hypotheses,
    'components': components, 'material_units': units,
    'remaining_full_literal_bridges': [],
    'whole_exercise_reason': 'All actual literal clauses and inherited measurable deterministic-or-randomized classifier scope are covered by the retained37 and the7 new actual kernel/product-law/sampling-event bodies. The valid confidence procedure is a question premise; every strict-ball ideal-label conclusion is derived.',
    'original37_review': d['original37_independent_review'],
    'entire_original37_review_body_and_time_unchanged': prior,
    'original37_source': d['original37_source'],
    'original37_entire_source_unchanged_prefix': True,
    'original_full_literal_request': d['original_full_literal_request'],
    'proof_source': d['source'], 'all44_full_bodies_and_definitions_read': True,
    'all7_new_full_bodies_and_definitions_read': True,
    'actual_TMP_standalone_record': d['actual_new_pass_record'],
    'entire_actual_new_pass_record_and_time': act,
    'actual_raw_log': d['actual_new_pass_raw_log'], 'retained_actual_diagnostic_warning_count': 6,
    'source_snapshot': d['source_snapshot'],
    'all_new_trial_bytes_sha256': d['all_original_new_trial_bytes_sha256'],
    'original37_trial_history': literal['original_trial_and_source_byte_inputs'],
    'selected_dependency_full_bodies': literal['selected_exact_evidence_and_full_sources_read'],
    'primary_source': prior['primary_source'],
    'scope_exclusions': [
        'This is the complete numeric/confidence practice and its inherited classifier domain, not a whole approval of the separate general two-probability theorem, all endpoint extensions, or the full Monte-Carlo Clopper-Pearson implementation in Section4.',
        'No PRNG execution, conditional-on-observed-return guarantee, canonical/named proof execution, selection, aggregate or live-owner promotion is inferred. The fixed checkpoint25 ledger remains unchanged.'
    ],
    'protected_selected25_source_count': 1156,
    'current52_source_pages_checked': 29, 'installed25_owner_count_checked': 5,
    'scope': 'Read-only fresh full44 body/literal/primary-scope semantic review. The exact old37 partial review/body/time and original failures remain historical evidence without relabeling.'
}
out = Path('/tmp/modules-smoothing44-independent-applied-full-whole-source-review26-v1.json')
assert not out.exists()
out.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'review': ref(out), 'full_bodies': 44, 'new_full_bodies': 7,
                  'whole_exercise_approved': True, 'proved_units': 5, 'nonformal_units': 1}))
