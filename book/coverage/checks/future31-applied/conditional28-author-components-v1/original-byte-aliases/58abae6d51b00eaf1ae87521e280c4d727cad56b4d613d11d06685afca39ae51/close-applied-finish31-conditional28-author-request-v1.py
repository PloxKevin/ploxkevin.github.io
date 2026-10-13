from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, time

ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=ROOT/'book/coverage/checks/future31-applied/conditional28-author-components-v1'
SOURCE=Path('/tmp/CompleteAppliedConditionalExpectationMSEDensityWhole31-draft-v6.lean')
SOURCE_SHA='a17a13e4b8ab97a3d020061b923eb5cdf15d115d30654ddf12a968fb0c53aba6'
PROPOSAL=Path('/tmp/applied-finish31-conditional387-qualifiers-unnumbered-v1/conditional387-two-exact-qualifiers-unnumbered-author-proposal31-v2.json')
PROPOSAL_SHA='163277e38eae53c577664c5ed7cd6874f49236fbb2df37313e3f0b233616bb4e'
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def descriptor(p):
    p=Path(p)
    return {'file':str(p.relative_to(ROOT))if p.is_relative_to(ROOT)else str(p),
            'sha256':sha(p),'bytes':p.stat().st_size}

assert not OUT.exists() and sha(SOURCE)==SOURCE_SHA and sha(PROPOSAL)==PROPOSAL_SHA
OUT.mkdir(parents=True)
aliases={};required={}

def retain(p,expected=None):
    p=Path(p);h=sha(p)
    if expected is not None:assert h==expected,str(p)
    assert not p.is_symlink()
    target=OUT/'original-byte-aliases'/h/p.name
    target.parent.mkdir(parents=True,exist_ok=True)
    if not target.exists():
        with target.open('xb')as f:f.write(p.read_bytes())
    assert sha(target)==h
    z=descriptor(target);aliases[str(p)]=z;required[z['file']]=h
    return z

source=retain(SOURCE,SOURCE_SHA);proposal=retain(PROPOSAL,PROPOSAL_SHA);helper=retain(Path(__file__))
d=json.loads(PROPOSAL.read_bytes())
for path,expected in [(d['source'],d['source_sha256']),(d['candidate'],d['candidate_sha256']),
                       (d['full_prospective_inventory'],d['full_prospective_inventory_sha256']),
                       (d['previous_original_v1']['file'],d['previous_original_v1']['sha256']),
                       (d['actual_preparation_execution']['actual_helper'],d['actual_preparation_execution']['actual_helper_sha256'])]:
    retain(path,expected)
inventory_code=retain(ROOT/'book/inventory_claims.py')
parser_code=retain(ROOT/'book/validate.py')

def native(path):
    n=json.loads(Path(path).read_bytes())
    assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']
    assert n['protection_errors']==[]
    row={'native':retain(path),'actual_status':n['status'],'actual_exit_code':n['actual_exit_code'],
        'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}}
    for key,hkey in [('source','source_sha256_before'),('source_snapshot','source_snapshot_sha256'),('raw_log','raw_log_sha256')]:
        row[key]=retain(n[key],n[hkey])
    row['actual_warning_headers']=len(re.findall(r'(?m)^.*: warning:',Path(n['raw_log']).read_text()))
    for key in ['original_actual_runner','actual_source79_final_css_owner30_context','actual_source81_historical_source79_owner30_context']:
        if key in n:retain(n[key]['file'],n[key]['sha256'])
    return row

old_histories=[native('/tmp/applied-conditional-expectation13-owner30-trial'+str(i)+'.json')for i in [1,2]]
new_histories=[native('/tmp/applied-finish31-conditional-MSE-density-Source81-trial'+str(i)+'.json')for i in range(1,7)]
assert [x['actual_exit_code']for x in old_histories]==[1,0]
assert [x['actual_exit_code']for x in new_histories]==[1,1,1,0,1,0]
assert old_histories[1]['source']['sha256']=='64278bc40d8b50f6f6e5600be77dd4b98b0761d784a71f71ac642c348c9dea1f'
assert new_histories[-1]['source']['sha256']==SOURCE_SHA
axiom=native('/tmp/applied-finish31-conditional28-Source81-axiom-native-v1.json')
assert axiom['actual_exit_code']==0
base=SOURCE.read_bytes();s=base.decode()
assert Path('/tmp/applied-finish31-conditional28-axiom-inspection-v1.lean').read_bytes().startswith(base)
old=Path('/tmp/CompleteAppliedConditionalExpectationMaterial31-draft-v2.lean').read_bytes()
assert base[len(b'import Mathlib\n'):].startswith(old)
public=list(re.finditer(r'^theorem\s+(\w+)\s*',s,re.M));assert len(public)==28
names=['SafeLearning.CompleteAppliedConditionalExpectationMaterial31.'+m.group(1)for m in public]
printed=re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]+)\]",Path('/tmp/applied-finish31-conditional28-Source81-axiom-native-v1.log').read_text(),re.M)
assert [n for n,_ in printed]==names
assert all(set(re.split(r',\s*',a))=={'propext','Classical.choice','Quot.sound'}for _,a in printed)
support_names=[
    'MeasureTheory/Function/ConditionalExpectation/Basic.lean',
    'MeasureTheory/Function/ConditionalExpectation/PullOut.lean',
    'MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean',
    'MeasureTheory/Function/ConditionalExpectation/AEMeasurable.lean',
    'MeasureTheory/Function/ConditionalExpectation/Real.lean',
    'MeasureTheory/Function/L2Space.lean',
    'MeasureTheory/Function/LpSpace/Basic.lean',
    'MeasureTheory/Function/FactorsThrough.lean',
    'MeasureTheory/Integral/Bochner/SumMeasure.lean',
    'MeasureTheory/Integral/Bochner/Basic.lean',
    'Probability/Kernel/CondDistrib.lean',
    'Probability/Density.lean',
    'Probability/ConditionalProbability.lean',
    'Analysis/InnerProductSpace/Projection/Basic.lean']
support={n:retain(ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'/n)for n in support_names}
signatures=[]
for i,m in enumerate(public):
    tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|end |section |namespace |noncomputable def)',tail[1:]);body=tail[:stop.start()+1]if stop else tail
    signatures.append({'declaration':names[i],'actual_signature':body.split(':=',1)[0].strip(),
        'exact_source_block_sha256':hashlib.sha256(body.encode()).hexdigest(),
        'part_of_unchanged_original13':i<13,'authored_addition':i>=13})

correspondence={
    'observation_function_version':'actual_conditional_mean_really_is_a_function_of_the_observation',
    'mean_square_for_finite_risk_competitors':'actual_conditional_mean_minimizes_mean_squared_error',
    'finite_second_moment_L2_equivalence':'actual_finite_second_moment_is_the_exact_square_integrability_condition',
    'mean_square_all_known_predictors_including_infinite_risk':'actual_conditional_mean_minimizes_even_extended_mean_squared_error',
    'actual_regular_conditional_law_integral':'actual_conditional_mean_is_the_regular_conditional_law_integral',
    'finite_conditional_mean_almost_everywhere':'actual_conditional_law_has_finite_first_moment_at_almost_every_observation',
    'canonical_conditional_density_formula':'actual_conditional_mean_is_the_density_integral_where_a_density_exists',
    'arbitrary_given_density_version_formula':'actual_given_density_version_defines_the_conditional_mean_after_observation',
    'discrete_countable_conditional_mass_sum':'actual_discrete_conditional_mean_is_the_countable_probability_mass_sum',
    'event_conditioned_mean_ratio':'actual_event_conditioned_mean_is_the_exact_probability_ratio',
    'positive_event_normalizes_true_conditioned_law':'actual_positive_probability_event_has_a_normalized_conditional_law',
    'positive_event_printed_product_identity':'actual_positive_event_mean_has_the_printed_multiplicative_identity',
    'exact_discrete_weighted_tower_and_joint_sum':'actual_discrete_weighted_tower_has_the_exact_printed_joint_sum',
    'general_integrable_tower_rule':'actual_expected_conditional_mean_equals_original_mean',
    'measurable_pullout_with_integrable_product':'actual_take_out_a_function_of_the_observed_random_variable'
}
report={
    'status':'prepared_closed_actual_conditional28_source_components_and_two_exact387_qualifiers_for_independent_whole_review',
    'author':'/root/applied_finish31','errors':[],'final_actual_passed_complete_source':source,
    'actual_public_theorem_count':28,'all_complete_public_signatures':signatures,
    'original13_entire_passed_bytes_retained_after_one_Mathlib_import':True,
    'original13_independent_review':{'status':'passed_for_their_explicit_component_statements',
        'all13_complete_bodies_and_parameters_read':True,
        'scope':'Genuine measurability, integrable tower/known-event characterization, pull-out with explicit L1/product assumptions, nested tower and the two actual Bernoulli cost means/difference. These13 alone do not establish whole current387.'},
    'added15_components_authored_by_this_reviewer_not_third_party_independent':True,
    'entire_current387':d['entire_current387'],'entire_prospective387':d['entire_prospective387'],
    'exact_literal_clause_correspondence':correspondence,
    'manual_added_body_assessment':'L2 conditional expectation is the actual orthogonal projection; its residual is orthogonal to every known competitor residual and yields the true mean-square inequality. The extended-integral proof handles infinite-risk competitors separately and derives square integrability of finite-risk competitors. Doob-Dynkin gives the actual observation-function version. The regular conditional-law integral is a genuine disintegration theorem; density formulas follow from actual law-with-density/Radon-Nikodym identities rather than assuming the desired mean formula. Countable discrete formulas use actual atomic integrals and finite conditional first moments on non-null observations, and the weighted tower identity equals the true joint mass sum and original expectation. The event ratio uses the actual normalized restricted probability measure.',
    'private_actual_L2_norm_square_body_present':True,
    'all_two_old_genuine_compiler_histories':old_histories,'all_six_new_genuine_compiler_histories':new_histories,
    'actual_separate_all28_axiom_native':axiom,'all28_axioms':['propext','Classical.choice','Quot.sound'],
    'original_native_labels_body_times_raw_logs_warnings_or_failures_rewritten':False,
    'complete_direct_used_primary_source_texts':support,
    'two_exact_offline_qualifier_proposal':proposal,
    'author_actual_proposal_execution':d['actual_preparation_execution'],
    'actual_full29_prospective_inventory':aliases[d['full_prospective_inventory']],
    'inventory_code':inventory_code,'parser_code':parser_code,
    'actual_author_parser_changed_keys':d['exact_full29_fresh_parser_changed_keys'],
    'requested_independent_review':'Read the entire actual28 source, all original13 and new15 bodies, used primary bodies, current387/conditioning context and exact prospective387. Review density-existence, ae-version and integrability assumptions; MSE includes infinite-risk competitors. Independently regenerate the full29 prospective inventory with ROOT and OUT strictly TMP; verify only387 text changes, with all exercise keys and all tags/attributes/lines unchanged. Decide prospective whole387 only after all clauses including the exact countable tower proof and positive-event meaning are reviewed.',
    'current_whole387':False,'prospective_whole387_approved_by_author':False,
    'source_ordinal_reserved_or_current_source_style_raw_owner_selected_or_publication_mutation':False,
    'canonical_installation_or_new_aggregate_claimed':False,'coverage_complete':False,
    'actual_static_closure_execution':{'command':['python3',str(Path(__file__))],'helper':helper,
        'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
        'actual_exit_code':0,'current_guard_or_compiler_invoked_by_this_static_closure':False},
    'full_file_original_byte_aliases':aliases,'required_evidence_artifacts_sha256':required
}
p=OUT/'conditional28-full-source-current-and-prospective387-independent-review-request31-v1.json'
with p.open('x')as f:f.write(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':descriptor(p),'full_file_aliases':len(aliases),'package_bytes':sum(q.stat().st_size for q in OUT.rglob('*')if q.is_file())}))
