"""Prepare a TMP-only Modules owner31 candidate; never compile or parse book HTML."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/modules-owner31-current81-integral39-ast19-provisional-v1')
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
CANONICAL = 'verification/lean/SafeLearning/CompleteModulesIntegralTrackingWhole31.lean'
EVIDENCE = {
    'original_owner30': ('book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-candidate-v1.json', '6f347b3d512a5ce36222e72e8236eb350f3218ace430c3a9dabd8776a03fbc34'),
    'inventory79': ('book/coverage/inventory-after-correction79.json', '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'),
    'inventory81': ('book/coverage/inventory-after-correction81.json', 'b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'),
    'AST_peer': ('book/coverage/checks/future31-applied/AST23-child-and35-structural-independent-applied30b-v1/AST23-Applied21-complete-reuses-two-clause-gaps-and35-pure-NF-leaves-independent-applied30b-closed-peer-v1.json', 'bb3c92b97798dd355c1d353bd264701e846804ab22dd1c93ccd379de68dcec49'),
    'integral35_peer': ('book/coverage/checks/future31-applied/integral35-whole-independent-v1/integral35-entire-current-prospective-independent-applied31-peer-v1.json', 'e0d997d45d8d5387cba74e87adc8cc37ac8afec394dfdb0370f12b7f9a3e48c0'),
    'integral39_supplement': ('book/coverage/checks/future31-applied/integral35-whole-independent-v1/integral39-combined-source-all-bodies-approved-applied31-supplement-v1.json', '9e10c8e86817a0f2cc93938cffc6b3a2a3ab185470e68ab9fbdd29983b85d55b'),
    'integral39_increment': ('book/coverage/checks/future31-core/integral39-four-correspondence-independent-modules-v1/modules-integral39-exact35-prefix-four-full-correspondence-bodies-independent-modules31-closed-peer-v1.json', 'acc36c8719367766fa31b05137d9e784aabd59e4df23acb42f114ab04b46117d'),
    'plan2': ('/tmp/modules-owner31-static-plan-ast19-integral39-v2.json', 'e621f10acf1473c66c447e6e1e612c873cae07dd2c14a95013cfea5f6eff9ddf'),
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def path(f):
    p = Path(f)
    return p if p.is_absolute() else ROOT / p

def ref(f):
    p = path(f)
    return {'file': str(f), 'sha256': sha(p), 'bytes': p.stat().st_size}

assert sha(CONTEXT) == CONTEXT_SHA
context = json.loads(CONTEXT.read_bytes())
assert context['status'] == 'actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only'
pins = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}

def guard():
    assert sha(CONTEXT) == CONTEXT_SHA
    for f, h in pins.items():
        p = ROOT / f
        assert not Path(f).is_absolute() and '..' not in Path(f).parts
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p) == h, f
    for f, h in EVIDENCE.values():
        assert not path(f).is_symlink() and sha(path(f)) == h, f

guard()
assert not OUT.exists()
OUT.mkdir()
data = {k: json.loads(path(f).read_bytes()) for k, (f, _) in EVIDENCE.items()}
old = data['original_owner30']
assert sha(ROOT / 'book/coverage/modules.json') == EVIDENCE['original_owner30'][1]
inv79, inv81 = data['inventory79'], data['inventory81']
ast, peer35, peer39, increment = [data[k] for k in ['AST_peer', 'integral35_peer', 'integral39_supplement', 'integral39_increment']]
assert not ast['errors'] and not peer35['errors'] and not peer39['errors'] and not increment['errors']
source_ref = peer39['entire_combined39_source']
assert source_ref['sha256'] == '1a388e0109e6e8ff8bd9ce8c102420a7202f064eb7e46a76ff2cd4bcfefc10aa'
assert sha(path(source_ref['file'])) == source_ref['sha256']
source = path(source_ref['file']).read_text()
assert CANONICAL not in old['proof_files']  # Root installed the canonical bytes meanwhile; this version still keeps pair binding pending.
names = increment['all39_public_names']
assert len(names) == 39 and len(set(names)) == 39
assessments = {r['declaration']: r for r in peer35['all35_public_proof_body_assessments']}
for r in peer39['added4_complete_body_assessments']:
    assert r['declaration'] not in assessments
    assessments[r['declaration']] = r
assert set(assessments) == set(names)
assert len(old['declarations']) == old['counts']['new_declarations'] == 3988
assert len(old['proof_files']) == 517 and all(isinstance(x, str) for x in old['declarations'][-504:])
old_names = {r if isinstance(r, str) else r['name'] for r in old['declarations']}
assert not old_names.intersection(names)
definitions = re.findall(r'(?m)^def\s+([A-Za-z0-9_]+)', source)
assert len(definitions) == 13
public_declarations = [{'name': n, 'kind': 'theorem'} for n in names]
public_declarations += [{'name': 'SafeLearning.CompleteModulesIntegralTrackingWhole30.' + n, 'kind': 'def'} for n in definitions]
public_declarations.sort(key=lambda r: source.index(r['kind'] + ' ' + r['name'].rsplit('.', 1)[1]))
assert len(public_declarations) == 52
owned = set(old['source_sha256'])
u79 = {r['key']: r for r in inv79['material_source_units'] if r['source'] in owned}
u81 = {r['key']: r for r in inv81['material_source_units'] if r['source'] in owned}
e79 = {r['key']: r for r in inv79['exercises'] if r['source'] in owned}
e81 = {r['key']: r for r in inv81['exercises'] if r['source'] in owned}
assert set(u79) == set(u81) and len(u81) == 4977
assert set(e79) == set(e81) and len(e81) == 217
changed_units = [k for k in u79 if u79[k]['source_text'] != u81[k]['source_text']]
changed_ex = [k for k in e79 if e79[k]['source_text'] != e81[k]['source_text']]
assert changed_units == ['nn-in-the-loop.html::node-1247']
assert changed_ex == ['nn-in-the-loop.html::exercise-19']
for k, r in increment['actual_source81_literal_equalities_to_approved_prospective_and_unchanged_current'].items():
    assert r == (e81[k] if k in e81 else u81[k]), k
leaves = [r for r in ast['per_structural_leaf_decisions'] if r['owner_scope'] == 'modules']
assert len(leaves) == 19
for r in leaves:
    k = r['inventory_key']
    assert r['classification'] == 'not_a_formal_claim' and r['whole_selected_leaf_NF_approved']
    assert not r['underlying_handler_or_math_wrapper_approved']
    assert r['entire_current_material_literal']['source_text'] == u81[k]['source_text'] == u79[k]['source_text']

def write(name, value):
    p = OUT / name
    with p.open('x', encoding='utf-8') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')
    return ref(str(p))

identity = {
    'status': 'prepared_exact_Source79_owner30_to_actual_Source81_owned_literal_identity',
    'original_owner30': ref(EVIDENCE['original_owner30'][0]),
    'original_inventory79': ref(EVIDENCE['inventory79'][0]), 'actual_inventory81': ref(EVIDENCE['inventory81'][0]),
    'actual_context': ref(str(CONTEXT)), 'owned_material_unit_count': len(u81), 'owned_exercise_count': len(e81),
    'identical_owned_unit_and_exercise_key_sets': True,
    'all_material_identities': [{'key': k, 'original_text_sha256': u79[k]['text_sha256'], 'current_text_sha256': r['text_sha256'], 'original_source_sha256': u79[k]['source_sha256'], 'current_source_sha256': r['source_sha256'], 'literal_unchanged': u79[k]['source_text'] == r['source_text']} for k, r in u81.items()],
    'all_exercise_identities': [{'key': k, 'original_text_sha256': e79[k]['text_sha256'], 'current_text_sha256': r['text_sha256'], 'original_source_sha256': e79[k]['source_sha256'], 'current_source_sha256': r['source_sha256'], 'literal_unchanged': e79[k]['source_text'] == r['source_text']} for k, r in e81.items()],
    'changed_materials_entire_original_and_current': {k: {'entire_original': u79[k], 'entire_current': u81[k]} for k in changed_units},
    'changed_exercises_entire_original_and_current': {k: {'entire_original': e79[k], 'entire_current': e81[k]} for k in changed_ex},
    'whole_Integral39_transfer': ref(EVIDENCE['integral39_increment'][0]),
    'all19_AST_NF_literals_unchanged': True, 'historical_source79_peer_verdicts_or_natives_rewritten': False,
    'source_parser_or_compiler_invoked': False, 'owner_installed': False, 'coverage_complete': False,
}
identity_ref = write('modules31-Source79-to81-entire-owned-literal-identity-v1.json', identity)
candidate = copy.deepcopy(old)
forward, inverse = [], []

def tokens(pointer):
    return [p.replace('~1', '/').replace('~0', '~') for p in pointer.split('/')[1:]]

def parent_obj(obj, pointer):
    t = tokens(pointer)
    for k in t[:-1]:
        obj = obj[int(k)] if isinstance(obj, list) else obj[k]
    return obj, t[-1]

def replace(pointer, value):
    obj, k = parent_obj(candidate, pointer)
    if isinstance(obj, list): k = int(k)
    previous = copy.deepcopy(obj[k])
    if previous == value: return
    forward.extend([{'op': 'test', 'path': pointer, 'value': previous}, {'op': 'replace', 'path': pointer, 'value': copy.deepcopy(value)}])
    inverse[0:0] = [{'op': 'test', 'path': pointer, 'value': copy.deepcopy(value)}, {'op': 'replace', 'path': pointer, 'value': previous}]
    obj[k] = copy.deepcopy(value)

def add(pointer, value):
    obj, k = parent_obj(candidate, pointer)
    if isinstance(obj, list):
        assert k == '-'
        actual_pointer = pointer.rsplit('/', 1)[0] + '/' + str(len(obj))
        obj.append(copy.deepcopy(value))
    else:
        assert k not in obj
        actual_pointer = pointer
        obj[k] = copy.deepcopy(value)
    forward.append({'op': 'add', 'path': pointer, 'value': copy.deepcopy(value)})
    inverse[0:0] = [{'op': 'test', 'path': actual_pointer, 'value': copy.deepcopy(value)}, {'op': 'remove', 'path': actual_pointer}]

refs = {k: ref(f) for k, (f, _) in EVIDENCE.items()}
reviews = {k: refs[k] for k in ['integral35_peer', 'integral39_supplement', 'integral39_increment']}
replace('/status', 'prepared_isolated_Source81_Modules_owner31_Integral39_and19_NF_provisional_pending_actual_canonical_pair_and_independent_mapping')
replace('/source_sha256', {f: inv81['source_sha256'][f] for f in old['source_sha256']})
replace('/current_inventory', EVIDENCE['inventory81'][0])
replace('/current_inventory_sha256', EVIDENCE['inventory81'][1])
replace('/current_identity_binding_validation', {'status': 'prepared_exact_Source81_identity_provisional_owner31_pending_actual39_pair_and_final_independent_mapping', 'inventory': refs['inventory81'], 'identity': identity_ref, 'canonical_owner_integrated': False, 'historical_current79_binding_retained': old['current_identity_binding_validation']})
for a, r in enumerate(candidate['exercises']):
    current = e81[r['inventory_key']]
    assert r['source_text_sha256'] == e79[r['inventory_key']]['text_sha256']
    replace('/exercises/' + str(a) + '/source_sha256', current['source_sha256'])
    if r['inventory_key'] in changed_ex:
        replace('/exercises/' + str(a) + '/source_text_sha256', current['text_sha256'])

def index(k):
    rows = [(a, r) for a, r in enumerate(candidate['material_claims']) if k in r.get('source_unit_keys', [])]
    assert len(rows) == 1 and rows[0][1]['status'] == 'pending', k
    return rows[0]

for d in leaves:
    k = d['inventory_key']; a, r = index(k); r = copy.deepcopy(r)
    assert r['statement_in_prose'] == u81[k]['source_text']
    category = 'navigation' if 'navigation labels' in d['reason'] else 'citation' if 'bibliographic links' in d['reason'] else 'control_label_wrapper'
    r.update(status='not_a_formal_claim', kind='literal_' + category + '_leaf', lean_declarations=[], hypotheses=[], correspondence=d['reason'], remaining_gaps=[])
    r['independent_source_review'] = {**refs['AST_peer'], 'reviewer': ast['reviewer'], 'status': ast['status'], 'inventory_key': k}
    r['current_source81_literal_identity'] = {**identity_ref, 'inventory_key': k, 'text_sha256': u81[k]['text_sha256'], 'source_sha256': u81[k]['source_sha256'], 'exact_unchanged_reviewed_leaf': True}
    r['reviewed_owner31_leaf_scope'] = {'entire_selected_leaf_NF_approved': True, 'underlying_handler_or_math_wrapper_approved': False, 'destination_mathematics_promoted': False}
    r['scope_limits'] = ['Only this exact complete selected leaf is classified. Destination mathematics, enclosing mathematical prose and underlying handlers retain their prior statuses.', 'No compiler evidence is asserted for this nonformal classification.']
    replace('/material_claims/' + str(a), r)

short = {n.rsplit('.', 1)[1]: n for n in names}
def chosen(indices):
    return [names[n-1] for n in indices]

map_a = [1,2,3,4,5,20,21,22,23,24,25,33,36,38,39]
map_b = list(range(6,20)) + [24,26,27,28,29,30,31,32,34,35,37]
map_c = [6,7,8,9,10,11,12,13,14,15,16,17,18,19,26,37]
maps = {'nn-in-the-loop.html::node-1240': list(range(1,40)), 'nn-in-the-loop.html::node-1244': map_a, 'nn-in-the-loop.html::node-1247': map_b, 'nn-in-the-loop.html::node-1249': map_c}
common = ['The printed scalar plant uses a=1/2 and one fixed nominal controller nominalNetwork r x=r/2-(3/10)*tanh(x-r); integral gain is kXi=1/5.', 'References and disturbances are real constants, and the integrator obeys xi[n+1]=xi[n]+r-x[n]. The actual physical trajectories are iterations of the printed augmentedStep.']
scope_a = ['The two wrong-limit/offset examples are exactly (b,d,r)=(1,1/10,1) and (6/5,0,1), from every initial scalar state.', 'The scalar contraction and exact derivative interval apply to b in[1,6/5] and all real d,r,x. The wrong-offset gain example is not extended to all references: pure gain mismatch has zero-offset equilibrium exactly at r=0.', 'The fixed-network impossibility concerns two distinct constant disturbances at the same reference/state; it does not exclude a network fitted to one known true plant.']
scope_b = ['Nonlinear augmented global convergence/exponential estimates cover exactly b=1 or b=6/5, every real constant d,r, every initial physical state and every natural time.', 'General structural equilibrium tracking needs an actual augmented fixed point. General equilibrium existence additionally needs b!=0 and kXi!=0, with an arbitrary network.', 'The structural limiting theorem requires convergence of both output and integrator and the true integrator recurrence; output convergence alone is not a premise sufficient for the claimed conclusion.', 'The Jacobian is the actual Frechet derivative; the exact complete spectra have attained radii sqrt(2/5) and sqrt(19/50), each below1 and within0.0005 of the displayed approximations.', 'Simulation sentences are covered as mathematical limiting-value claims, without asserting reproduction of a finite numerical run.']
scope_c = ['Pauli Theorem1 concerns all initial conditions/references under its strict common LMI and standing invertibility/slope assumptions; Theorem3 concerns one fixed reference on its certified ellipsoid; Theorem4 concerns the certified set of initial-state/reference pairs.', 'These are bounded external primary attribution dependencies checked in the full independent whole peer. No new general Pauli research theorem, generic Section4 result, arbitrary uncertain gain family or arbitrary perturbed-plant stability result is claimed.', 'The stability certificate must cover the true perturbed augmented dynamics on its claimed domain. Once both state components converge, exact output tracking follows structurally without constraints on the network steady-state map.']
scope_by_key = {'nn-in-the-loop.html::node-1240': common + scope_a + scope_b + scope_c, 'nn-in-the-loop.html::node-1244': common + scope_a, 'nn-in-the-loop.html::node-1247': common + scope_b, 'nn-in-the-loop.html::node-1249': common + scope_b + scope_c}

def formal_inputs(ns):
    return [{'declaration': n, 'exact_reviewed_signature_and_all_input_predicates': assessments[n]['actual_signature'], 'complete_source_body_sha256': assessments[n]['exact_source_block_sha256'], 'independent_assessment': assessments[n].get('manual_assessment', assessments[n].get('assessment')), 'source': source_ref} for n in ns]

def reviewed_claim(r, key, ns, correspondence, scopes):
    r = copy.deepcopy(r)
    r.update(status='proved', lean_declarations=ns, hypotheses=scopes, correspondence=correspondence, remaining_gaps=[])
    r['independent_source_review'] = {**refs['integral35_peer'], 'reviewer': peer35['reviewer'], 'status': peer35['status']}
    r['full_combined39_review'] = refs['integral39_supplement']
    r['four_correspondence_increment_and_current81_transfer'] = refs['integral39_increment']
    r['current_source81_literal_identity'] = {**identity_ref, 'inventory_key': key, 'text_sha256': (e81[key] if key in e81 else u81[key])['text_sha256'], 'source_sha256': (e81[key] if key in e81 else u81[key])['source_sha256']}
    r['formal_input_predicates'] = formal_inputs(ns)
    r['scope_limits'] = scopes
    r['canonical_pair_pending'] = True
    return r

correspondences = {
    'nn-in-the-loop.html::node-1240': 'Every requirement of the exact current Source81 prompt is mapped below: actual nominal feedforward, true wrong scalar limits and rigorous offsets, general integral equilibrium tracking/existence, actual nonlinear global certificate, true derivative/spectrum/C1 and reference-target limits. The certification-domain/Pauli attribution clauses are covered only in the explicit bounded scope from the independent whole peer.',
    'nn-in-the-loop.html::node-1244': 'The held nominal network yields the exact two offset equations. Actual Banach fixed points and every scalar iterate give the wrong limits at r=1, with strict rational rounding brackets for0.1252/0.1165 and exact linearized1/8. The separate correspondence theorem exposes the actual derivative in[7/50,1/2]. The true-feedforward equivalence, two-disturbance obstruction and zero-reference exception preserve the precise transfer limits.',
    'nn-in-the-loop.html::node-1247': 'Actual general integral fixed points have x=r, and the explicit equilibrium exists for nonzero plant/integral gains. Current Source81 now states xi=-5/6 approximately-0.833 and exact spectral radii sqrt(2/5),sqrt(19/50) with their proved rounding. The actual Frechet derivative, full spectrum/C1 and physical nonlinear exponential bound establish stability; separate global storage/trajectory proofs establish distant-state convergence for the two stated gains and the printed limiting targets.',
    'nn-in-the-loop.html::node-1249': 'The actual augmented-loop storage/trajectory family provides all-reference/all-initial convergence for the two specified gains. General integral recurrence plus convergence forces zero output offset independently of plant/network weights; general equilibrium existence has its stated nonzero gains. The complete primary Pauli1/3/4 attribution/domain comparison is retained as a bounded external dependency, with no new generic research theorem or arbitrary perturbed-plant certificate inferred.',
}
for k, ix in maps.items():
    a, r = index(k)
    r = reviewed_claim(r, k, chosen(ix), correspondences[k], scope_by_key[k])
    r['kind'] = 'whole_exact_current_source_mathematical_literal'
    r['statement_in_prose'] = u81[k]['source_text']
    r['whole_exact_current_source_unit_approved'] = True
    replace('/material_claims/' + str(a), r)

exkey = 'nn-in-the-loop.html::exercise-19'
exindex = next(a for a, r in enumerate(candidate['exercises']) if r['inventory_key'] == exkey)
exercise = copy.deepcopy(candidate['exercises'][exindex])
assert len(exercise['claims']) == 5 and all(r['status'] == 'pending' for r in exercise['claims'])
requirement_maps = [[1,2,6,7,17,18], [1], map_a, map_b, map_c]
requirement_scopes = [common, common, common+scope_a, common+scope_b, common+scope_b+scope_c]
requirement_text = [
    'The actual scalarMap and augmentedStep definitions instantiate the printed scalar plant and nominal parameters; the nominal feedforward and general equilibrium identities retain the true plant/integrator equations.',
    'For every real reference, the fixed nominal network has kappa(r,r)=r/2 and the nominal scalar plant fixes r exactly.',
    correspondences['nn-in-the-loop.html::node-1244'], correspondences['nn-in-the-loop.html::node-1247'], correspondences['nn-in-the-loop.html::node-1249']]
exercise['claims'] = [reviewed_claim(r, exkey, chosen(ix), text, scopes) for r, ix, text, scopes in zip(exercise['claims'], requirement_maps, requirement_text, requirement_scopes)]
exercise['status'] = 'complete_math'
exercise['whole_exact_current_exercise_approved'] = True
exercise['independent_full_exercise_review'] = reviews
exercise['current_source81_literal_identity'] = {**identity_ref, 'inventory_key': exkey, 'text_sha256': e81[exkey]['text_sha256'], 'source_sha256': e81[exkey]['source_sha256']}
exercise['canonical_pair_pending'] = True
replace('/exercises/' + str(exindex), exercise)

proof = {'sha256': source_ref['sha256'], 'selection_scope': 'direct_reviewed_reference_provisional_owner31_pending_actual_canonical_pair', 'standalone_compile_status': 'passed_original_TMP_source_only_actual_canonical_pair_pending', 'declarations': names, 'public_theorem_names': names, 'mapped_named_declarations': names, 'theorem_count': 39, 'public_declarations': public_declarations, 'public_names': [r['name'] for r in public_declarations], 'public_name_count': 52, 'original_tmp_source': source_ref, 'original_actual_tmp_trial': peer39['actual_full_combined39_successful_native']['native'], 'original_actual_tmp_trial_scope': peer39['actual_full_combined39_successful_native'], 'independent_source_review': refs['integral35_peer'], 'full_combined39_source_review': refs['integral39_supplement'], 'four_added_correspondence_body_review': refs['integral39_increment'], 'canonical_pair_pending': True, 'actual_pair_claimed': False, 'intended_canonical_basename': 'CompleteModulesIntegralTrackingWhole31.lean', 'direct_imports': ['SafeLearning.CompleteModulesTanhChords', 'Mathlib.Topology.MetricSpace.Contracting', 'Mathlib.Analysis.SpecificLimits.Basic'], 'historical_Source79_actual_kernel_context_retained': True, 'current_Source81_author_preparation_is_not_kernel_verification': True}
add('/proof_files/' + CANONICAL.replace('~','~0').replace('/','~1'), proof)
for n in names: add('/declarations/-', n)
counts = copy.deepcopy(old['counts'])
counts['exercise_status'] = dict(__import__('collections').Counter(r['status'] for r in candidate['exercises']))
counts['exercise_claim_status'] = dict(__import__('collections').Counter(c['status'] for r in candidate['exercises'] for c in r['claims']))
counts['material_claim_status'] = dict(__import__('collections').Counter(r['status'] for r in candidate['material_claims']))
counts['new_declarations'] = len(candidate['declarations'])
assert counts == {'exercises':217,'exercise_status':{'complete_math':198,'pending':12,'partial':7},'exercise_claim_status':{'proved':798,'pending':54,'not_a_formal_claim':24},'material_claim_status':{'not_a_formal_claim':555,'pending':3517,'proved':1128},'new_declarations':4027}
replace('/counts', counts)
add('/inventory_identity_rebase81', {'status': 'prepared_exact_actual81_identity_with_historical79_owner30_preserved', 'identity': identity_ref, 'original_owner30': refs['original_owner30'], 'all_original79_historical_metadata_retained': True, 'chapter_fragments_sha256_unchanged': True, 'inventory_parser_invoked': False, 'canonical_pair_pending': True})
add('/reviewed_work_integration31_current81_provisional_candidate', {'status': 'prepared_one_whole_Integral_exercise_four_whole_literals19_NF_leaves_pending_actual39_canonical_pair_and_final_independent_mapping', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'original_owner30': refs['original_owner30'], 'actual_inventory81': refs['inventory81'], 'whole_exercises': [exkey], 'whole_material_units': list(maps), 'NF_leaves_only': [r['inventory_key'] for r in leaves], 'new_sources': [CANONICAL], 'new_public_theorem_count':39, 'new_public_name_count':52, 'old517_proof_entries_and3988_declaration_prefix_exact':True, 'whole_duality7_5_and_scenario15_5_approved':False, 'whole_shifted_temporal_Exercise14_6_approved':False, 'new_canonical_standalone_or_named_pair_claimed':False, 'canonical_pair_pending':True, 'source81_aggregate_verification_claimed':False, 'current_owner_selection_or_publication_written':False, 'coverage_complete':False, 'reviews':reviews, 'AST_peer':refs['AST_peer']})

def apply_patch(obj, ops):
    obj = copy.deepcopy(obj)
    for op in ops:
        p, k = parent_obj(obj, op['path'])
        if isinstance(p, list) and k != '-': k = int(k)
        if op['op'] == 'test': assert p[k] == op['value'], op['path']
        elif op['op'] == 'replace': p[k] = copy.deepcopy(op['value'])
        elif op['op'] == 'remove':
            if isinstance(p, list): p.pop(k)
            else: del p[k]
        elif op['op'] == 'add':
            if isinstance(p, list):
                assert k == '-'; p.append(copy.deepcopy(op['value']))
            else:
                assert k not in p; p[k] = copy.deepcopy(op['value'])
        else: raise AssertionError(op['op'])
    return obj

assert apply_patch(old, forward) == candidate
restored = apply_patch(candidate, inverse)
assert restored == old
assert candidate['declarations'][:3988] == old['declarations']
assert {k: candidate['proof_files'][k] for k in old['proof_files']} == old['proof_files']
target_materials = set(maps) | {r['inventory_key'] for r in leaves}
for before, after in zip(old['material_claims'], candidate['material_claims']):
    if not set(before.get('source_unit_keys',[])).intersection(target_materials): assert before == after
for before, after in zip(old['exercises'], candidate['exercises']):
    if before['inventory_key'] == exkey: continue
    projected = copy.deepcopy(after); projected['source_sha256'] = before['source_sha256']
    assert projected == before, before['inventory_key']
for r in data['plan2']['all_original_false_whole_flags_must_be_retained']:
    o,k=parent_obj(candidate,r['JSON_pointer']); assert o[k] is False, r['JSON_pointer']
original_bytes = path(EVIDENCE['original_owner30'][0]).read_bytes()
serializers = [a for a in [False,True] if (json.dumps(old,ensure_ascii=a,indent=2)+'\n').encode() == original_bytes]
assert serializers, 'Original serialization parameters must match before claiming exact inverse bytes'
inverse_bytes = (json.dumps(restored,ensure_ascii=serializers[0],indent=2)+'\n').encode()
assert hashlib.sha256(inverse_bytes).hexdigest() == EVIDENCE['original_owner30'][1]
candidate_ref = write('modules31-current81-Integral39-AST19-provisional-candidate-v1.json', candidate)
forward_ref = write('modules31-current81-full-typed-forward-JSONpatch-v1.json', {'format':'RFC6902_JSON_Patch_operations_with_explicit_typed_test_values','original_owner30':refs['original_owner30'],'candidate':candidate_ref,'operations':forward})
inverse_ref = write('modules31-current81-full-typed-inverse-JSONpatch-v1.json', {'format':'RFC6902_JSON_Patch_operations_with_explicit_typed_test_values','candidate':candidate_ref,'restores_original_owner30':refs['original_owner30'],'original_serialization':{'indent':2,'ensure_ascii':serializers[0],'trailing_newline':True},'operations':inverse})
association_ref = write('modules31-current81-full-explicit-Integral39-and-AST19-row-associations-v1.json', {'Integral_material_rows':[candidate['material_claims'][a] for a,r in enumerate(candidate['material_claims']) if set(r.get('source_unit_keys',[])).intersection(maps)],'entire_Integral_exercise':exercise,'AST19_material_rows':[candidate['material_claims'][a] for a,r in enumerate(candidate['material_claims']) if set(r.get('source_unit_keys',[])).intersection({d['inventory_key'] for d in leaves})],'proof_metadata':proof,'preserved_original_wholeFalse_count':len(data['plan2']['all_original_false_whole_flags_must_be_retained']),'all_old_proof_and_declaration_prefixes_exact':True})
guard()
request = {'status':'prepared_provisional_Modules_owner31_Source81_mapping_request_actual_author_preparation_native_pending','review_scope':'Independently review all exact19 NF rows, all four Integral rows and five Exercise19 requirements against closed peers/full predicates; verify forward/inverse equality, fresh81 identities, old proof/declaration prefixes and all historical wholeFalse/scopes. Canonical pair remains pending.','candidate':candidate_ref,'original_owner30':refs['original_owner30'],'forward_patch':forward_ref,'inverse_patch':inverse_ref,'identity':identity_ref,'explicit_associations':association_ref,'evidence':refs,'context':ref(str(CONTEXT)),'canonical_pair_pending':True,'all23_material_rows_and_one_exercise_only_scope':True,'old517_proof_entries_and3988_declarations_prefix_exact':True,'new39_theorem_names_only':True,'all52_public_names_retained_in_proof_metadata':True,'inverse_reconstructed_original_bytes_sha256':hashlib.sha256(inverse_bytes).hexdigest(),'canonical_path_not_written':CANONICAL,'no_Lean_HTML_parser_or_named_build_invoked':True,'coverage_complete':False}
request_ref = write('modules31-current81-provisional-independent-mapping-review-request-v1.json', request)
offer_ref = write('modules31-current81-provisional-root-offer-v1.json', {'status':'prepared_provisional_owner31_no_live_installation_actual39_pair_pending_author_native_pending','candidate':candidate_ref,'forward_patch':forward_ref,'inverse_patch':inverse_ref,'identity':identity_ref,'request':request_ref,'new_source':source_ref,'intended_canonical_path':CANONICAL,'counts':counts,'new_theorem_count':39,'public_name_count':52,'canonical_pair_pending':True,'all_current_owner_files_unchanged':True,'coverage_complete':False})
print(json.dumps({'status':'passed_isolated_author_preparation','candidate':candidate_ref,'inverse':inverse_ref,'request':request_ref,'offer':offer_ref,'forward_operations':len(forward),'inverse_operations':len(inverse),'counts':counts,'actual_guard_pin_count':len(pins),'canonical_pair_pending':True},ensure_ascii=False))
