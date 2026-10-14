"""Freeze explicit Source91 part-(i) correspondence; later subparts stay pending."""
import sys
import argparse
from pathlib import Path
import common as c

sys.path.insert(0,str(c.ROOT/'book/solutions'))
import solution_review as html

INVENTORY='book/solutions/releases/source91-v1/source91-inventory/inventory.json'
PACKET='book/coverage/source91-piece01/claims-v1.json'
P='SafeLearning.CompleteModulesLandscapeSource91ARPartI.'
L='SafeLearning.CompleteModulesLandscapeARLawLimit.'
S='SafeLearning.CompleteModulesLandscapeARStableMoments.'
C='SafeLearning.CompleteModulesLandscapeStationaryCharacterization.'
F='SafeLearning.CompleteModulesLandscapeARPathFluctuation.'

# Each row is a manually reviewed mathematical implication, not an automatic
# inference from a matching string or successful compiler result.
CLAIMS=[
 ('centering',0,'The centered initial state is -goal and e(t+1)=(1-k)e(t)+sigma*w(t).',
  [P+'actual_centered_infinite_state_has_the_printed_initial_value_and_recursion'],
  'The infinite trajectory is the literal original recurrence with x(0)=0; subtraction is an exact real identity.'),
 ('stability-iff',0,'The source condition 0<k<2 is equivalent to |1-k|<1.',
  [P+'source_stability_interval_is_exactly_the_strict_absolute_multiplier_condition'],
  'Both directions of the stated real inequality are proved.'),
 ('first-two-substitutions',0,'The first two centered states equal a*e(0)+sigma*w(0) and a^2*e(0)+sigma*(a*w(0)+w(1)).',
  [P+'actual_first_two_centered_substitutions_are_the_printed_values'],
  'Here a=1-k and e(0)=-goal; the first and second substitutions are separate conjuncts.'),
 ('unrolled-state',1,'For every natural t the centered state is a^t*(-goal)+sigma*sum(j<t,a^(t-1-j)*w(j)).',
  [P+'actual_centered_infinite_state_has_the_printed_unrolled_finite_sum'],
  'The finite sum is derived from the recurrence and includes the empty t=0 case.'),
 ('noise-moments-and-cross-covariances',2,'Each standard Gaussian noise has mean zero and variance one; distinct noise cross-covariances vanish.',
  [P+'actual_infinite_standard_noise_has_zero_mean_and_unit_variance',P+'actual_distinct_infinite_noise_cross_covariances_are_zero'],
  'The product measure supplies the independent Gaussian noises; L2 moments are derived from their actual laws.'),
 ('actual-state-moments',3,'The original state has mean goal*(1-a^t) and variance sigma^2*sum(i<t,a^(2*i)).',
  [P+'actual_infinite_state_has_the_same_internally_derived_gaussian_marginal',P+'actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas',P+'the_two_printed_variance_sums_are_equal'],
  'These are integrals and variances of the actual infinite-path state, not merely definitions assigned to a recurrence.'),
 ('positive-geometric-denominator',4,'Under 0<k<2, 1-a^2=k*(2-k)>0 and the geometric ratio a^2 is below one.',
  [P+'the_printed_denominator_factorization_is_positive_on_the_source_stability_interval'],
  'The identity and positive denominator imply a^2<1 by subtraction; square nonnegativity is standard real arithmetic.'),
 ('geometric-formula-and-limits',5,'The variance equals sigma^2*(1-(1-k)^(2*t))/(k*(2-k)); it converges to sigma^2/(k*(2-k)), and the mean converges to goal.',
  [S+'actual_true_variance_has_the_printed_closed_geometric_formula',S+'actual_state_mean_converges_to_the_goal_for_every_stable_source_gain',S+'actual_state_variance_converges_to_the_printed_stationary_variance',P+'actual_infinite_state_mean_and_variance_are_the_printed_finite_formulas'],
  'The printed mean/variance are identified with the actual process moments; limits hold for all stable real gains, including k>1.'),
 ('gaussian-update',6,'Updating a mean-goal Gaussian state with independent standard noise produces variance a^2*v+sigma^2 and the same mean.',
  [C+'actual_arbitrary_gaussian_state_and_independent_fresh_noise_have_the_source_updated_law'],
  'The measure is the independent product of the arbitrary Gaussian state and fresh standard Gaussian noise; no independence of consecutive states is assumed.'),
 ('stationary-variance-characterization',6,'The updated mean-goal Gaussian law is unchanged exactly for v=sigma^2/(1-a^2).',
  [C+'actual_gaussian_law_is_unchanged_exactly_when_the_true_variance_is_fixed',C+'actual_stable_gain_has_exactly_the_printed_gaussian_stationary_variance',P+'the_printed_denominator_factorization_is_positive_on_the_source_stability_interval'],
  'The theorem proves both directions for nonnegative Gaussian variance; 1-a^2=k*(2-k). This characterizes Gaussian laws with the source mean, not arbitrary invariant measures.'),
 ('same-process-distribution-limit',6,'The original states converge in distribution to the stated stationary Gaussian law.',
  [P+'actual_states_on_one_infinite_noise_space_converge_in_distribution_to_the_stationary_law'],
  'An explicit finite-prefix law bridge places all states on one countably infinite independent Gaussian noise space.'),
 ('no-noisy-path-limit',6,'For sigma>0 individual noisy trajectories do not settle at the goal.',
  [F+'actual_noisy_original_state_path_has_no_finite_real_limit_almost_surely'],
  'A single almost-sure event excludes every finite real limit for sigma!=0; the source sigma>0 condition implies sigma!=0. No conclusion is obtained by a union of null sets over uncountably many limits.')
]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',default=PACKET)
    args=parser.parse_args()
    inventory=c.read(INVENTORY)
    exercise=next(e for e in inventory['exercises'] if e['key']=='landscape.html::exercise-19')
    source=exercise['source'];raw=c.path(source).read_bytes()
    assert c.sha(raw)==exercise['source_sha256']==inventory['source_sha256'][source]
    doc=html.Document(raw)
    node=next(n for n in doc.exercises() if 'Exercise 1.5' in html.clean(n.child('summary').text()))
    slots=html.parts(doc,node);body=slots['solution']['html'].encode()
    start=slots['solution']['range']['start_byte']+body.index(b'<p><strong>(i)')
    end=slots['solution']['range']['start_byte']+body.index(b'<p><strong>(ii)')
    fragment=raw[start:end]
    piece=html.Document(fragment)
    nodes=[n for n in piece.root.children if isinstance(n,html.Node)]
    assert len(nodes)==7 and [n.tag for n in nodes]==['p','div','p','div','p','div','p']
    ranges=[]
    for n in nodes:
        a=start+piece.byte(n.start);b=start+piece.byte(n.end)
        text=html.clean(n.text());line=raw[:a].count(b'\n')+1
        units=[u for u in inventory['material_source_units'] if u['source']==source and u['tag']==n.tag
               and u['line']==line and html.clean(u['source_text'])==text]
        assert len(units)==1,(line,n.tag,len(units))
        ranges.append({'start_byte':a,'end_byte':b,'line':line,'html_sha256':c.sha(raw[a:b]),
                       'text':text,'source_unit':units[0]})
    proof_names=['CompleteModulesLandscapeSource91ARPartI','CompleteModulesLandscapeARLawLimit',
        'CompleteModulesLandscapeARPathFluctuation','CompleteModulesLandscapeStationaryCharacterization',
        'CompleteModulesLandscapeARGaussianAlgebra','CompleteModulesLandscapeARGaussianLaw',
        'CompleteModulesLandscapeARStableMoments','CompleteModulesLandscapeARStationaryGaussian']
    claims=[]
    for key,index,statement,declarations,correspondence in CLAIMS:
        claims.append({'id':'landscape-1.5-part-i::'+key,'status':'candidate_pending_independent_review_and_native_audit',
            'statement_in_prose':statement,'source_fragment':ranges[index],
            'lean_declarations':declarations,'hypotheses':['The original scalar recurrence starts at x(0)=0.',
                'Noises are independent standard Gaussian coordinates.',
                '0<k<2 for stability, stationary-variance uniqueness and distribution limits.',
                'sigma>0 only for the printed noisy-path nonconvergence conclusion.'],
            'correspondence':correspondence,'remaining_gaps':[]})
    value={'schema':'formal-source91-bounded-piece.v1','status':'candidate_explicit_source_correspondence_pending_audit_and_independent_review',
        'piece':1,'inventory':c.ref(INVENTORY),'exercise':exercise,'reader_source':c.ref(source),
        'part_i':{'start_byte':start,'end_byte':end,'sha256':c.sha(fragment),'html':fragment.decode()},
        'source_units':ranges,'claims':claims,'proof_sources':[c.ref('verification/lean/SafeLearning/'+n+'.lean') for n in proof_names],
        'candidate_additions':proof_names[:4],'historical_Source90_coverage_retained':True,
        'whole_exercise_status_after_success':'partial','whole_exercise_completion_claimed':False,
        'parts_ii_and_iii':'pending_fresh_Source91_correspondence_in_later_pieces',
        'other_source_units':'unreviewed_for_Source91_except_this_exact_part_i_fragment',
        'formal_coverage_complete':False}
    c.json_put(args.report,value)
    print({'packet':c.ref(args.report),'claims':len(claims),'whole_source_units':len(ranges),'whole_exercise_complete':False})


if __name__=='__main__':main()
