from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/foundations-residual17-full-review28-v1/foundations-residual17-full-review28-v1.json')
OUTPUT = Path('/tmp/foundations-residual17-independent-modules-full-source28-findings-v1.json')
assert not OUTPUT.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def ref(p): return {'file': str(p), 'sha256': sha(p)}
def checked(r):
    assert type(r) is dict and set(r) == {'file', 'sha256'}
    p = Path(r['file'])
    if not p.is_absolute(): p = ROOT/p
    assert p.is_file() and not p.is_symlink() and sha(p) == r['sha256'], str(p)
    return p
def actual_code(d, want):
    fields = [k for k in ('actual_exit_code', 'exit_code', 'actual_runner_exit_code') if k in d]
    assert fields and all(type(d[k]) is int and d[k] == want for k in fields)
def extract(s):
    ms = list(re.finditer(r'^theorem\s+(\w+)\b', s, re.M))
    return {m.group(1): s[m.start():(ms[i+1].start() if i+1<len(ms) else len(s))] for i,m in enumerate(ms)}

started = datetime.now(timezone.utc).isoformat()
assert sha(REQUEST) == '0c98395fda4a08486e951eb7a329be7cef3603ef332e04783e7647ef43f78853'
j = read(REQUEST)
source = checked(j['proof_source'])
assert source.read_text() == j['entire_source']
decls = extract(j['entire_source'])
assert len(decls) == j['public_theorem_count'] == 17
assert not re.search(r'\b(sorry|admit|axiom)\b', j['entire_source'])
for r in j['full_reused_dependency_sources']:
    p = checked(r['source']); assert p.read_text() == r['entire_source']
selected = read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assert len(selected['proof_files']) == selected['proof_file_count'] == 1175
bindings = read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')
assets = bindings['exact_current55_safelearning_assets_sha256']; assert len(assets) == 31
integration = read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')
assert integration['applied'] is True
owners = {r['destination']:r['candidate']['sha256'] for r in integration['exact_replacements']}
assert len(owners) == 5
held = {n:r['sha256'] for n,r in selected['proof_files'].items()}
held.update(assets); held.update(owners)
held.update({str(checked(j[k]).relative_to(ROOT)):j[k]['sha256'] for k in ('current_inventory','current_foundations_owner','current_corrections')})
held['reports/full-coverage/checkpoint-27-selection.json'] = 'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
held['reports/full-coverage/root-source55-final-owner-integration27-v1.json'] = 'aa2cfe3ee0c56ea0758b900abce5121cc36c9725444702ee775e75ab67dd50ea'
def guard():
    for n,h in held.items(): assert sha(ROOT/n) == h, n
guard()
inv = read(checked(j['current_inventory']))
units = {r['key']:r for r in inv['material_source_units']}
assert len(j['full_source_units']) == 3
assert [r['key'] for r in j['full_source_units']] == j['newly_requested_material_units']
for r in j['full_source_units']:
    assert r == units[r['key']]
    assert sha(ROOT/r['source']) == r['source_sha256']
    assert hashlib.sha256(r['source_text'].encode()).hexdigest() == r['text_sha256']
page = ROOT/j['full_source_units'][0]['source']
context = '\n'.join(page.read_text().splitlines()[1332:1395])
assert context == j['full_local_teaching_context_lines1333_to1395']
ledger = read(checked(j['current_foundations_owner']))
keys = set(j['newly_requested_material_units'])
oldrows = [r for r in ledger['material_claims'] if keys.intersection(r.get('source_unit_keys',[]))]
assert oldrows == j['current_existing_claims_unchanged']
for r in j['full_reused_dependency_sources']:
    n = str(checked(r['source']).relative_to(ROOT))
    assert n in selected['proof_files'] and selected['proof_files'][n]['sha256'] == r['source']['sha256']
for original,alias in j['original_closed_byte_aliases'].items():
    assert sha(original) == alias['sha256'] and Path(original).read_bytes() == checked(alias).read_bytes()
trial = read(checked(j['actual_standalone_record']))
assert trial == j['entire_original_actual_record_and_time']
actual_code(trial,0)
assert trial['actual_command'] == ['lake','env','lean',str(source)]
assert trial['actual_workdir'] == str(ROOT/'verification/lean')
assert trial['source_sha256_before'] == trial['source_sha256_after'] == trial['source_snapshot_sha256'] == sha(source)
assert Path(trial['source_snapshot']).read_bytes() == source.read_bytes()
assert trial['protection_errors'] == [] and trial['protected_proof_sources'] == 1175
assert trial['original_actual_runner'] == {'file':'/tmp/root_tmp_lean28_runner_v4.py','sha256':'8fe26e9954800b4e104db5a079eb2e9295e3680064fe7ebaaa74b496e60ec49b'}
checked(trial['original_actual_runner'])
assert trial['installed27_owner_sha256'] == owners
assert checked(j['raw_log']).read_text() == j['entire_raw_log']
assert trial['raw_log_sha256'] == j['raw_log']['sha256']
assert j['actual_warning_count'] == j['entire_raw_log'].count('warning:') == 4
for row in j['genuine_previous_failed_trials']:
    old = read(checked(row['record'])); actual_code(old,1)
    assert old == row['entire_original_record_and_time'] and old['protection_errors'] == []
    assert sha(old['source_snapshot']) == old['source_snapshot_sha256'] == old['source_sha256_before'] == old['source_sha256_after']
    assert Path(old['source_snapshot']).read_text() == row['entire_failed_source']
    assert sha(old['raw_log']) == old['raw_log_sha256'] and Path(old['raw_log']).read_text() == row['entire_raw_log']
    assert old['actual_command'] == ['lake','env','lean',old['source']]

NS = 'SafeLearning.CompleteFoundationsResidualWeightingIdentification27.'
theorem_names = [NS+n for n in decls]
dep = {str(checked(r['source']).relative_to(ROOT)):r['entire_source'] for r in j['full_reused_dependency_sources']}
bridge = dep['verification/lean/SafeLearning/CompleteFoundationsMatrixResidualOrthogonality27.lean']
assert 'theorem actual_independent_matrix_columns_have_one_attained_unique_least_squares_estimate' in bridge
assert '(hH : Function.Injective H.mulVec)' in bridge and '∃!x : EuclideanSpace ℝ n' in bridge
correspondences = {r['source_unit_key']:r for r in j['source_unit_correspondences']}
decisions = []
reason = {
'primer-linalg.html::node-1288': 'The actual rectangular matrix appends [0,1] to the preceding almost-sum channels. Its injective columns and range finrank two, explicit noisy vector outside that range, actual Euclidean residual/sum-of-squares equality and attained unique teaching estimate directly encode the printed model. The already selected full finite-matrix bridge encodes generic attained unique least squares for every finite real full-column-rank matrix and every reading, with direct mulVec/Euclidean loss correspondence. The distinct true state plus additive measurement-error witness has zero fit residual at a different estimate, so a residual is not itself a state error.',
'primer-linalg.html::node-1290': 'Generic finite-channel Euclidean row scaling gives squared coefficients scale_i^2. Two genuine channel criteria have different unique minimizers and strict cross-criterion inequalities. For every epsilon,M>0 a genuine injective diagonal observation map with delta=epsilon/(2M) sends a state error of norm M to measurement error epsilon/2<epsilon. Delta varies with the requested scales; no universal amplification claim about a fixed well-conditioned map is made. Comparability, appropriateness and choosing a weighting policy are explicit modeling guidance. These guidance clauses are classified as such within this whole mixed mathematical/modeling literal; no empirical sensor guarantee is inferred.',
'primer-linalg.html::node-1293': 'The actual one-row matrix [1,1] and column [1/2,1/2] satisfy all four real Moore-Penrose identities, and any matrix satisfying those identities equals that column. The unique Moore-Penrose inverse applied to reading six is exactly (3,3). Every feasible Euclidean vector is exactly (3+t,3-t), its squared norm is 18+2t^2, and the norm minimum is uniquely (3,3). A distinct feasible (4,2) rules out physical identification by the reading alone. Reporting the family or declaring the minimum-norm criterion is the stated descriptive repair.'}
hypotheses = {
'primer-linalg.html::node-1288': ['Real displacement/reading vectors in Euclidean finite-dimensional coordinates; the printed dimensionless additive model H z+eta is conditional on calibration validity.', 'The numerical rectangular H and reading y are exactly the teaching fixture; noisy incompatibility is an existential may witness.', 'The reused generic unique-attainment bridge requires finite real matrices and injective mulVec (independent columns), which the actual rectangular matrix satisfies.'],
'primer-linalg.html::node-1290': ['Finite real channel residuals and arbitrary real row scales; weighting coefficients in squared loss are scale squared.', 'The illustrative two-channel scalar criteria show a possible changed choice, not a universal optimal sensor-weight policy.', 'epsilon>0 and M>0; the constructed weak observation map varies with epsilon and M and has delta>0, injective action and no uniform fixed-map guarantee.'],
'primer-linalg.html::node-1293': ['Real one-row sum measurement z1+z2=6 with Euclidean state length.', 'The pseudoinverse is characterized by all four real Moore-Penrose identities (transpose symmetry equals real self-adjointness).', 'Minimum Euclidean length is an additional explicit selection criterion; the physical state has no assumed equal-displacement prior.']}
for u in j['full_source_units']:
    c = correspondences[u['key']]
    for d in c['lean_declarations']: assert d in theorem_names
    decisions.append({'source_unit_key':u['key'],'entire_inventory_record':copy.deepcopy(u),'whole_unit_approved':True,'whole_literal_approved':True,'status':'proved','decision':'approved_complete_literal_under_explicit_model_hypotheses','lean_declarations':c['lean_declarations']+c.get('reused_declarations',[]),'hypotheses':hypotheses[u['key']],'reason':reason[u['key']],'per_clause_correspondence':c['literal_complete_correspondence'],'missing_clauses':[],'remaining_gaps':[]})
guard()
closure = {str(REQUEST):sha(REQUEST),str(source):sha(source),str(page):sha(page)}
closure.update({str(checked(r['source'])):r['source']['sha256'] for r in j['full_reused_dependency_sources']})
for original,alias in j['original_closed_byte_aliases'].items(): closure[original]=alias['sha256'];closure[alias['file']]=alias['sha256']
closure.update({str(ROOT/n):h for n,h in held.items()})
peer = {'status':'passed_independent_full_three_literal_residual_weighting_identification_source_review28','errors':[],'reviewer':'/root/modules_resume (independent of Foundation author)','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'proof_source':j['proof_source'],'public_theorem_count':17,'all_public_declarations':theorem_names,'all_seventeen_complete_theorem_bodies_and_definitions_read':True,'all_three_complete_literals_and_full_teaching_context_read':True,'all_three_full_reused_dependency_sources_read':True,'entire_source':j['entire_source'],'all_complete_theorem_bodies':decls,'full_reused_dependency_sources':j['full_reused_dependency_sources'],'material_units':decisions,'entire_original_existing_material_claims_and_times':j['current_existing_claims_unchanged'],'original_standalone_record':j['actual_standalone_record'],'entire_original_actual_record_and_time':trial,'entire_genuine_prior_failed_trials':j['genuine_previous_failed_trials'],'raw_log':j['raw_log'],'entire_raw_log':j['entire_raw_log'],'actual_warning_count':4,'full_teaching_context':context,'current_selected1175_sources31_assets5_owners_rehashed_before_after':True,'current_native_inventory_and_corrections':{'inventory':j['current_inventory'],'corrections':j['current_corrections']},'source_unit_1289_not_reopened':True,'scope':'TMP-only independent source/semantic review. Existing selected generic matrix least-squares bridge is reused with explicit hypotheses. No compiler rerun, canonical/named pairing, owner mutation, candidate installation, whole exercise/parent approval or new aggregate verification is claimed.','closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__))}
OUTPUT.write_text(json.dumps(peer,indent=2)+'\n')
print(json.dumps({'status':peer['status'],'errors':[],'material_units':keys and sorted(keys),'public_theorem_count':17,'findings':ref(OUTPUT)}))
