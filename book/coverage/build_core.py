#!/usr/bin/env python3
"""Maintain exact source correspondences for the core control chapters.

Unreviewed exercises and material remain explicit pending records. A component
proof never closes the whole question unless its full correspondence was reviewed.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
INV = json.loads((ROOT/'book/coverage/inventory.json').read_text())
PAGES = {'barriers','case-studies','cmdp','lyapunov-mpc','policy-optimization',
         'book','formulas','glossary','index','open-problems','papers','study-guide'}
SOURCES = {f'SafeLearning/{p}.html' for p in PAGES}
P = 'SafeLearning.CompleteBookProjects.'
C = 'SafeLearning.CompleteCoreControl.'
B = 'SafeLearning.CompleteCoreBook.'
Q = 'SafeLearning.CompleteCoreProbability.'
W = 'SafeLearning.CompleteWeightedProjection.'
F = 'SafeLearning.CompleteConformal.'
T = 'SafeLearning.CompleteCoreReturns.'
V = 'SafeLearning.CompleteBudgetValue.'
D = 'SafeLearning.CompleteDuality.'
E = 'SafeLearning.CompleteCoreEntryModel.'
A = 'SafeLearning.BookApplications.'
M = 'SafeLearning.CoreModules.'
R = 'SafeLearning.CoreAnalysis.'

# Each entry describes the actual encoded conclusions, not the title of a
# broadly related theorem. Explanatory/model-validity limitations stay explicit.
MAP = {}
def add(key, names, statement, hypotheses, gaps=()):
    MAP[key] = dict(lean_declarations=names,statement_in_prose=statement,
                    hypotheses=hypotheses,remaining_gaps=list(gaps))

add('barriers.html#book-m10-b1',
    [C+n for n in ['noisier_barrier_command','noisy_projection_optimal','held_clearance_safety']],
    'The lower clearance is .27; the robust half-second threshold and nearest actuator command are -.44, correction .36, terminal bound0. Reusing-.5 gives-.03. The ODE derivative inequality proves nonnegative clearance at every intermediate time.',
    ['The stated scalar clearance dynamics, pointwise disturbance>=-.1, initial measurement error<=.08, actuator bounds[-.8,.8], half-second hold; the trajectory is continuous and differentiable in the interval.'])
add('barriers.html#book-m10-b2',
    [C+n for n in ['failed_drive_feasible','failed_drive_boundary_impossible','failed_drive_eventual_escape','failed_drive_critical_only_zero','nonpositive_time_varying_drive_eventual_escape']],
    'With u in[-.8,0], the robust action set is nonempty iff lower clearance>=.05; at.05 its only feasible input is0. At zero, every positive holding time is impossible under the constant worst disturbance. Every finite clearance eventually escapes if u<=0.',
    ['Worst disturbance-.1; held scalar dynamics and positive hold length; the eventual-escape theorem uses a constant admissible command.'],
    [])
add('barriers.html#book-m10-b3',
    [C+n for n in ['clearance_from_derivative','delayed_measurement_error','delayed_barrier_command','delayed_projection_optimal','held_clearance_safety']],
    'A speed bound.9 throughout a.1-second delay implies displacement<=.09; adding sensor error.05 gives present error.14, lower clearance.21, nearest half-second command-.32. Reusing-.5 gives terminal lower bound-.09.',
    ['The speed is bounded throughout the delay, with an integrable derivative; the held dynamics and disturbance bounds are as in the application.'])
for key,names,statement,gaps in [
 ('book-project-tank-b1',['tank_upper_decision','tank_robust_interval_iff','projectInterval_optimal'],
  'The upper-bound filter has the displayed exact command and terminal upper bound; projection is globally distance-minimizing over the robust admissible interval.',[]),
 ('book-project-tank-b2',['tank_large_disturbance_interval','tank_large_disturbance_empty','tank_large_disturbance_valid_counterexample'],
  'For inflow magnitude1.2 the robust interval is exactly the stated interval, is empty at the boundary measurement, and every actuator input admits a valid physical failing successor.',[]),
 ('book-project-tank-b3',['tank_feedback_quantifiers'],
  'For every allowed reading there exists an admissible action safe for every compatible state and disturbance; no single shared action works over the whole physical state interval.',[]),
 ('book-project-tuning-b1',['tuning_noisier_set','tuning_noisier_query'],
  'With observation error.05 the first certified interval is[0,.46], its largest endpoint is.46, and.5 fails the certificate.',[]),
 ('book-project-tuning-b2',['tuning_performance_underdetermined'],
  'Two certified feasible points.6,.7 are ranked in opposite orders by two possible performance functions; safety observations alone do not determine that ranking.',[]),
 ('book-project-tuning-b3',['zero_lipschitz_constant','zero_lipschitz_lower_certificate','negative_lower_underdetermined'],
  'A zero-Lipschitz function is constant on its domain. A nonnegative known lower value certifies all points; a negative lower value is consistent with both an everywhere-positive and an everywhere-negative constant function.',[]),
 ('book-project-score-b1',['normalized_physical_box','normalized_score_lower','unnormalized_radius_is_different'],
  'The physical box(|e1|<=.1,|e2|<=.4) normalizes to the exact coordinate box .2/.2, with score gap at least0 and an attained tie, so no strict positive certificate follows. The actual physical point(.2,0) lies within the Euclidean physical radius.2 but its normalized image lies outside the normalized Euclidean radius.2; these are different unit balls.',[]),
]:
    add('case-studies.html#'+key,[P+n for n in names],statement,
        ['The exact project model, units and bounds stated in the source.'],gaps)
add('case-studies.html#book-project-score-b2',
    [F+n for n in ['split_conformal_coverage','rank_nineteen_one_percent','nineteen_one_percent_infinite']] +
    ['SafeLearning.CompleteConformalCounterexample.'+n for n in
     ['absolute_residual_realization','uniform_permutation','scores_exchangeable',
      'clipped_failure_iff','actual_clipped_failure_probability','clipped_maximum_fails_ninety_nine_percent']],
    'With19calibration points andalpha=.01, the required rank is20. The augmented calibration order statistic is infinity, and exchangeable-score coverage remains valid with ties. An actual uniform law over20possible positions of a sole unit residual is exchangeable; a fixed zero predictor realizes these absolute residuals. Clipping to the actual19-point calibration maximum succeeds with probability19/20=.95, below.99.',
    ['Measurable exchangeable joint scores, a probability measure, and the augmented-infinity order-statistic convention. The counterexample uses a genuine finite exchangeable law; dependence is allowed by the asserted unconditional guarantee.'])
add('case-studies.html#book-project-score-b3',
    [Q+n for n in ['four_success_union_bound','four_success_allocated_bound','four_independent_successes','four_independent_success_lower_bound','disjoint_failure_probabilities','disjoint_joint_success','multiplying_marginals_invalid']],
    'Four marginal90%success statements imply joint success>=.6 without independence. Under actual joint independence the joint success is at least.9^4=.6561, with equality when all four success marginals equal.9. Four failure allocations.025 imply joint success>=.9. An explicit normalized five-outcome law with disjoint.1failures refutes multiplication without independence.',
    ['Measurable failure events on a probability space; independence only for the product theorem.'])
add('cmdp.html#book-m8-b1',[B+n for n in ['mode_expectation','original_reward_semantics','original_cost_semantics','tighter_budget_optimum','tighter_budget_attained','tighter_budget_unique_reward','interior_budget_multiplier']],
    'The normalized two-action PMF and genuine infinite discounted expected one-step sums give reward20+30p,cost.2+1.8p. At budget.65 the unique increasing-reward optimum is p=.25, reward27.5,cost.65; the interior budget marginal slope and flat Lagrangian multiplier are50/3.',
    ['A fixed two-mode mixture with the same marginal distribution at every step, discount.9, one-step rewards2,5 and costs.02,.2.'],
    ['An explicit expectation-of-pathwise-return/interchange wrapper and derivative of the budget-value function still need correspondence; the current definition is the sum of expected one-step rewards.'])
add('cmdp.html#book-m8-b2',[B+n for n in ['changed_discount_reward','changed_discount_cost','changed_discount_optimum','changed_discount_attainer_and_reuse']],
    'At discount.95 the discounted expected sums become40+60p and.4+3.6p. Budget1 gives p=1/6,reward50; reusing4/9 costs2.',
    ['Same two-mode PMF and per-step rewards/costs; discount changes to.95.'],
    ['The general effective-horizon/budget scaling correspondence and expectation-of-pathwise-return wrapper remain to be stated.'])
add('cmdp.html#book-m8-b3',[B+n for n in ['monitoring_next_action','monitoring_discounted_accounting','pathwise_resource_must_cover_realizations']]+[R+'discounted_budget_telescopes'],
    'Only cost.5 preserves nonnegative remaining budget14/27; its updated remainder is5/243. Original-time discounted spend.985 plus remainder.015 equals1. A pathwise nonnegative budget requires checking every allowed realization.',
    ['Deterministic realized costs in the trajectory example; positive discount.9.'])
add('policy-optimization.html#book-m9-b1',[B+'metric_comparison'],
    'The candidates have equal squared Euclidean length.25, quadratic trust costs.125,.5, reward improvements1,.5; only the second meets x<=.2.',
    ['H=diag(1,4), reward gradient(2,1), cost half-space x<=.2.'],
    ['An explicit Euclidean-norm square-root identity and geometric metric interpretation remain to be linked.'])
add('policy-optimization.html#book-m9-b2',[B+'ellipse_candidate_feasible',B+'ellipse_global_optimum',B+'ellipse_kkt'],
    'The optimizer(.2,sqrt6/5) attains the global reward bound(2+sqrt6)/5. Its nonnegative KKT prices5/(4sqrt6),2-1/(4sqrt6) satisfy both stationarity equations and active trust-constraint complementarity.',
    ['The exact local quadratic subproblem; this establishes no true-controller feasibility.'],
    ['The cost-constraint complementarity product and sensitivity interpretation still need explicit statements.'])
add('policy-optimization.html#book-m9-b3',[B+'sufficient_constraint_values',B+'positive_upper_bound_underdetermines_violation',B+'tightened_constraint_sufficient'],
    'The upper-bound expression is7/125at the original optimum and-3/20at the conservative point. A positive upper bound allows both safe and violating actual values; a nonpositive valid upper bound certifies feasibility. If it is the exact function, these values are the actual violation and margin.',
    ['The stated upper bound is valid for the true constraint; equality is a separately stated stronger model.'])
add('lyapunov-mpc.html#book-m11-b1',[B+'scalar_tube_iff',B+'noisier_tube_radius',B+'noisier_tube_and_band',B+'tightened_nominal_interval',A+'tube_sampled_invariance'],
    'The exact robust scalar tube radius is.18; nominal magnitude<=.82 ensures physical magnitude<=1. The physical band is invariant because the worst one-step magnitude is.59.',
    ['Closed-loop coefficient.5, pointwise disturbance<=.05 and approximation error<=.04; scalar additive dynamics.'])
add('lyapunov-mpc.html#book-m11-b2',[B+'scalar_tube_iff',B+'accuracy_error_iff',B+'tightened_nominal_interval',Q+'small_rms_does_not_bound_uniform_error'],
    'Radius.16requires approximation error<=.03 and allows nominal magnitude<=.84. An actual rare-error model has RMS below.03 while its maximum exceeds.03, so a mean-squared bound alone does not imply this pointwise specification.',
    ['The stated scalar additive model and uniform error specification.'])
add('lyapunov-mpc.html#book-m11-b3',[Q+n for n in ['uniform_test_mass','exceptional_probability','actual_mean_squared_error','maximum_error_attained','small_rms_does_not_bound_uniform_error','rms_numeric_enclosure','independent_missed_interval','miss_probability_numeric','miss_probability_real_bridge']],
    'Under the actual uniform[-1,1]measure, exceptional interval[.99,1]has mass.005, MSE.00005, RMSsqrt(.00005)in(.0070705,.0070715), maximum.1. The uniform.03bound fails. Independent200tests miss with probability.995^200in(.36695,.36705).',
    ['The specified indicator approximation error and independent test states; failure of this certificate alone is not a claim of closed-loop state violation.'])

# Additional exact reviews of the small CMDP exercises. Each mapping includes
# its general argument where the question calls for one.
add('cmdp.html#exercise-8-p1',[M+'discounted_constant',M+'cmdp_p1'],
    'The actual infinite constant-reward/cost series equals the geometric formula. At discount1/2 the reward is4 and total cost1/2<=3/5; the requirement concerns the discounted total rather than the one-step cost.',
    ['The deterministic reward2 and cost1/4 at every step, discount1/2 and budget3/5 stated in the question.'])
add('cmdp.html#exercise-8-p2',[T+'normalized_mode_occupancy',T+'mixed_occupancies_example',T+'pathwise_mode_return',M+'cmdp_p2'],
    'The normalized infinite action occupancies equal the stationary PMF weights(.7,.3), sum to1, and the actual reward/cost expected discounted sums are3.2 and1.2.',
    ['One self-looping state; each action marginal is the stated(.7,.3)PMF. Rewards1,3 and costs0,2 are deterministic given the action. The expectation interchange is proved under the probability-law assumptions, without requiring intertime independence.'])
add('cmdp.html#exercise-8-p3',[M+'cmdp_p3',D+'rewardDual',D+'reward_weak_duality'],
    'The two signed residuals give penalized values6.5 and9.5. The encoded dual takes a supremum over policies and then an infimum over nonnegative multipliers, so evaluating one policy at a fixed price alone does not evaluate that optimization.',
    ['The exact stated numerical values; bounded real returns and a nonempty feasible policy family for the general dual bound.'])
add('cmdp.html#exercise-8-p4',[M+'cmdp_p4',D+'orthant_scalar_projection',D+'strict_violation_strictly_increases_multiplier',D+'slack_decreases_projected_multiplier'],
    'The sequential updates are.3 then0. Positive step size and a strictly positive violation increase the multiplier; slack lowers a nonnegative multiplier, with projection retaining nonnegativity and minimizing squared distance to the nonnegative half-line.',
    ['Step size.2, initial multiplier.1, budget2, successive costs3 and0.'])
add('cmdp.html#exercise-8-p8',[M+'cmdp_p8',R+'discounted_budget_telescopes'],
    'The two remaining budgets are2 then1; original-time spend is1.75 and remainder.25. The general finite discounted accounting identity proves that multiplying the current remainder by gamma^n restores the original time units.',
    ['The stated deterministic realized costs, discount1/2, initial budget2 and recursive update.'])
add('cmdp.html#exercise-8-p10',[M+'cmdp_p10'],
    'The positive part of the signed average is0 while the average of the two positive parts is1/2. This explicit sequence has a positive first residual despite zero signed average, giving the required counterexample to iteratewise feasibility.',
    ['The specified exact residual sequence(1,-1); feasibility means a nonpositive residual.'])
add('cmdp.html#exercise-8-p12',[D+n for n in ['bounded_lagrangian_from_bounded_returns','feasible_reward_le_dual','reward_primal_le_each_dual','reward_weak_duality','exact_maximizer_subgradient','scalar_lagrangian_derivative','projected_descent_sign','orthant_projection_global_minimum','strict_violation_strictly_increases_multiplier','slack_decreases_projected_multiplier']],
    'For reward maximization the nonnegative penalty supplies an upper bound on every feasible return and its supremum. Taking the multiplier infimum preserves that upper bound. An actual exact inner maximizer supplies the stated subgradient inequality; projected descent has the displayed sign and is the Euclidean orthant projection.',
    ['Finite constraint index set, nonempty feasible policies and uniformly bounded real returns. The subgradient claim assumes an actual exact inner maximizer, as the source does; positive learning rate gives strict increase for strict violation.'])
add('cmdp.html::exercise-17',[D+n for n in ['reward_lagrangian_bounded_above','cost_lagrangian_bounded_below','lagrangian_affine','cost_lagrangian_affine','reward_dual_convex','cost_dual_concave','reward_weak_duality','cost_weak_duality','cost_dual_mirror','attained_reward_dual','attained_cost_dual','walk_dual_actual_supremum','walk_dual_piecewise','walk_dual_max_formula','walk_dual_convex','walk_dual_unique_minimum','walk_primal_optimum','walk_primal_attained_and_all_lagrangian_maximizers']],
    'The reward supremum dual is convex with weak upper duality; the cost infimum dual is concave with weak lower duality and the sign mirror r=-C. When an inner optimum is attained the encoded sup/inf equals that actual maximum/minimum. For the walkthrough the true supremum equals lambda+max(0,1-2lambda), is piecewise affine and convex, and uniquely attains its minimum1/2 atlambda1/2; the primal attains1/2.',
    ['Finite constraint index set, nonempty feasible policies and bounded real reward/cost returns. Sup/inf extend the prose max/min; attained-case identification is explicit.'],
    [])
MAP['cmdp.html::exercise-17']['lean_declarations'] += [D+'walk_dual_abs_form',D+'walk_dual_kink']
MAP['cmdp.html#book-m8-b1']['lean_declarations'] += [T+'pathwise_mode_return',V+'actual_interior_optimal_value',V+'actual_optimal_value_derivative',V+'mixture_dual_actual_supremum',V+'actual_dual_price_attained',V+'actual_dual_price_optimal',V+'actual_dual_price_unique']
MAP['cmdp.html#book-m8-b1']['remaining_gaps'] = [
    'Derive the actual random productivity and entry-indicator cost expectations from the stated conditional mode laws; the current pathwise wrapper uses deterministic conditional means.']
MAP['cmdp.html#book-m8-b2']['lean_declarations'] += [T+'pathwise_mode_return',T+'discounted_constant_budget_meaning']
MAP['cmdp.html#book-m8-b2']['remaining_gaps'] = [
    'Derive actual random reward and indicator-cost returns from the two-stage conditional mode model rather than only summing the action conditional means.']
MAP['cmdp.html#book-m8-b1']['lean_declarations'] += [E+n for n in ['entryLaw','actual_entry_probability','actual_pathwise_indicator_return','actual_indicator_return_equals_mode_return','tighter_budget_actual_entry_probability']]
MAP['cmdp.html#book-m8-b1']['statement_in_prose'] = (
    'The actual two-stage PMF chooses a mode then its Bernoulli entry(.02/.20). Genuine expected infinite indicator cost matches the mode conditional-mean formula, while the defined MDP reward function has the stated mode expectation. At budget.65 the unique mixture is.25, reward27.5,cost.65; its actual entry probability.065 is positive. The actual feasible-reward supremum has derivative50/3 throughout(.2,2), and the actual Lagrangian supremum has unique optimal multiplier50/3 there.')
MAP['cmdp.html#book-m8-b1']['hypotheses'] = [
    'Probability-space mode and entry processes have the stipulated stationary marginal laws; the entry law is constructed by PMF.bind from the actual conditional Bernoulli laws. The MDP reward function is the stated conditional expected reward2/5. Independence across times is not needed for expectation interchange.',
    'Discount.9 and interior budget.65; the general sensitivity and dual-price theorems use budgets in(.2,2).']
MAP['cmdp.html#book-m8-b1']['remaining_gaps'] = []
MAP['cmdp.html#book-m8-b2']['lean_declarations'] += [E+'actual_pathwise_indicator_return',E+'actual_indicator_return_equals_mode_return',T+'constant_cost_discount_doubling']
MAP['cmdp.html#book-m8-b2']['statement_in_prose'] = (
    'The actual Bernoulli-indicator expected cost and MDP expected reward at discount.95 give40+60p and.4+3.6p. Budget1 yieldsp1/6,reward50; reusing4/9costs2. A fixed constant cost has exactly doubled discounted total, and numerical budget1 changes its admissible constant rate from.1to.05; the operational meaning must therefore be reconsidered.')
MAP['cmdp.html#book-m8-b2']['hypotheses'] = MAP['cmdp.html#book-m8-b1']['hypotheses'][:1]+[
    'The same conditional mode data; discount changes to.95 and numerical budget stays1. The rate comparison concerns a constant one-step cost.']
MAP['cmdp.html#book-m8-b2']['remaining_gaps'] = []

# Original exercises receive only their new components; additional requirements
# remain pending even when the new component is a substantive general theorem.
for key,names,statement,gaps in [
 ('barriers.html::exercise-16',[C+'barrier_integrating_factor',C+'barrier_invariance'],
  'The integrating-factor argument proves eta(t)>=eta(0)exp(-beta*t), hence nonnegative eta is invariant, on every finite interval of a differentiable trajectory.',
  ['Nonlinear comparison, absolutely continuous/a.e. versions, solution-existence/uniqueness counterexamples and Filippov arguments remain.']),
 ('barriers.html::exercise-17',[W+n for n in ['weighted_halfspace_unique_minimum','inverse_denominator_positive','solution_stationarity','solution_feasible_complementarity','example_solution','example_minimum_unique']],
  'For every finite positive-definite real H and nonzero b, the displayed H-inverse projection is feasible and is the unique global minimum of the weighted quadratic energy. The diagonal example yields(1.8,1.2).',
  ['H=Ireduction/numericalcomparison, metric steepest-ascent interpretation, explicit objective factor1/2, strict convexity and necessity of KKT remain.']),
 ('barriers.html#exercise-10-p9',[C+'cube_defines_halfline',C+'cube_boundary_derivative',C+'outward_trajectory_derivative',C+'zero_gradient_does_not_imply_invariance'],
  'x^3>=0iff x>=0; its derivative at0is0while x(t)=-t has derivative-1and exits at every positive time.',[]),
 ('barriers.html#exercise-10-p10',[C+'continuous_feedback_derivative',C+'continuous_feedback_positive',C+'held_first_interval_iff',C+'held_first_interval_counterexample'],
  'The actual continuous exp(-t)trajectory solves the feedback ODE and is positive. A held input is safe exactly for nonnegative horizon<=1, and1.5gives-.5.',
  ['The held affine trajectory derivative/initial value still need an explicit exact-solution uniqueness wrapper.']),
 ('barriers.html::exercise-19',[C+'input_to_state_square',C+'input_to_state_inflated_boundary',C+'small_disturbance_boundary'],
  'Square completion yields hdot>=x-bound^2/4and the inflated boundary derivative is nonnegative; the original zero controller has strict inward drift for disturbance bound<=.25.',
  ['Finite-time escape exactODEand limit, full all-time invariant-set proof, classK identification and global ISSf theorem assumptions remain.']),
]:
    add(key,names,statement,['The exact model assumptions listed in the Lean declaration.'],gaps or
        ['Independent complete source-to-proof review is still required before promoting the whole original exercise.'])

MAP['barriers.html::exercise-17']['lean_declarations'] += [
    'SafeLearning.CompleteProjectionCharacterization.'+n for n in
    ['actual_half_objective_minimum','optimizer_is_explicit_solution','optimizer_iff_kkt',
     'strict_feasible_point','actual_dual_infimum_at_stationary_point','actual_strong_duality_attained']]
MAP['barriers.html::exercise-17']['statement_in_prose'] += (
    ' The actual half-energy objective has the same unique minimizer. For every feasible candidate, optimality is equivalent to existence of a nonnegative multiplier satisfying stationarity and complementarity. An explicit strictly feasible point has margin1; the actual Lagrangian infimum attains the primal objective at the displayed multiplier.')
MAP['barriers.html::exercise-17']['remaining_gaps'] = [
    'H=I reduction/numerical comparison, metric steepest-ascent interpretation, objective derivative and strict convexity remain to be linked.']
MAP['barriers.html::exercise-17']['lean_declarations'] += [
    'SafeLearning.CompleteProjectionGeometry.'+n for n in
    ['energy_strictly_convex','objective_strictly_convex','metric_linear_bound',
     'metric_steepest_ascent','identity_weight_solution']]+[
    'SafeLearning.CompleteProjectionDifferential.'+n for n in
    ['objective_line_derivative','objective_differentiable','actual_objective_gradient',
     'identity_example_multiplier','identity_example_solution','actual_numeric_comparison']]
MAP['barriers.html::exercise-17']['statement_in_prose'] += (
    ' The actual Frechet derivative is the dot product with H(u-u_nom), and the half-objective is strictly convex. The normalized H-inverse direction attains the global maximum of the linear constraint over the weighted energy unit ball, establishing the stated steepest-ascent geometry. Identity weighting gives(1.5,1.5) and multiplier.5, versus weighted(1.8,1.2) and multiplier.8. The positive denominator and active/inactive cases are established by the closed-form projection proof.')
MAP['barriers.html::exercise-17']['remaining_gaps'] = []
MAP['case-studies.html#book-project-score-b1']['lean_declarations'] += [P+'score_box_tie']
MAP['case-studies.html#book-project-tuning-b1']['lean_declarations'] += [
    'SafeLearning.CompleteProjectDomains.noisier_strict_margin_set',
    'SafeLearning.CompleteProjectDomains.strict_margin_excludes_right_endpoint']
MAP['case-studies.html#book-project-tuning-b1']['statement_in_prose'] += (
    ' With a strict positive-margin requirement the exact interval is[0,.46), so its right endpoint is excluded.')
MAP['case-studies.html#book-project-tuning-b3']['lean_declarations'] = [
    'SafeLearning.CompleteProjectDomains.'+n for n in
    ['zero_lipschitz_on_constant','domain_lower_certificate','operating_interval_certificate',
     'negative_domain_lower_underdetermined','zero_has_no_multiplicative_inverse']]
MAP['case-studies.html#book-project-tuning-b3']['statement_in_prose'] = (
    'A zero Lipschitz bound restricted to the operating domain forces constancy on that domain. The actual lower value.16at an operating anchor certifies every point of[0,1]. For any negative lower value, two actual constant functions satisfy the same domain-local zero bound and lower observation, with opposite true signs. Zero has no multiplicative inverse, so division byL is unnecessary.')
MAP['case-studies.html#book-project-tuning-b3']['hypotheses'] = [
    'The zero Lipschitz inequality is assumed only for pairs within the operating domain; the observed anchor belongs to that domain. Nonnegative lower values certify the domain, and the contrasting-model theorem assumes the supplied lower value is negative.']
MAP['case-studies.html#book-project-tuning-b2']['lean_declarations'] += [
    'SafeLearning.CompleteProjectOptima.'+n for n in
    ['actual_certificate_set','true_safety_observations_compatible','actual_truly_safe_set',
     'certified_identity_maximum','full_identity_maximum','certified_optimum_misses_full_safe_optimum']]
MAP['case-studies.html#book-project-tuning-b2']['statement_in_prose'] += (
    ' An actual constant true margin.16satisfies both observed error intervals and the stated.5Lipschitz bound. The actual cone-certified set is[0,.74], while the true safe domain is[0,1]. With performancef(a)=a the certified optimum.74is strictly below the full-safe optimum1.')

# New exercise groups stay partial until a separate source-to-statement review
# approves every question and answer clause at these exact bytes.
J = 'SafeLearning.CompleteBarrierExamples.'
barrier_groups = [
 ('1', [M+'barrier_p1_safe_set']+[J+n for n in ['actual_safe_interval','actual_safe_boundary','barrier_values']],
  'The actual superlevel set is[-1,1], its topological frontier is exactly{-1,1}, and the three barrier values are3/4,0,-3; the sign convention includes the zero-valued boundary.'),
 ('2', [M+'barrier_p2']+[J+n for n in ['allowed_input_at_half','allowed_input_at_boundary','approaching_boundary_restricts_inputs']],
  'The input inequality is exactlyu>=-2x, atx=.5it isu>=-1, and at0it isu>=0. Ordering the clearance orders the allowed input sets, establishing the shrinking admissible negative speed.'),
 ('3', [M+n for n in ['barrier_p3_optimal','barrier_p3_attained','barrier_p3_unique']]+
       ['SafeLearning.CompleteCoreMaterialLimits.'+n for n in
        ['barrier_nominal_objective_minimal','barrier_nominal_objective_unique']],
  'The actual half-squared objective over all real inputs has unique global minimizer-3. Overu>=-1it has unique global minimizer-1, objective2and correction2from nominal-3.'),
 ('4', [M+'barrier_p4_interval']+[J+n for n in ['explicit_feedback_initial','explicit_feedback_derivative','boundary_inward']],
  'The actual displayed exponential trajectory has the specified initial state and derivative1-x(t). Its values remain in[0,2] for all nonnegative times; boundary velocities are1and-1.'),
 ('6', [J+n for n in ['scalar_actuator_set','infeasible_actuator_set','all_actuators_feasible_at_two','no_global_actuator_certificate']],
  'The exact intersection is[max(-.2,1-x),.2]; at.1it is empty and at2it is the whole actuator interval. An actual nonnegative state with no admissible action refutes the global CBF feasibility assertion.'),
 ('7', [M+'barrier_p7_robust',J+'robust_input_comparison'],
  'The universal disturbance inequality for|w|<=.3is equivalent tou>=.3-x. Atx=.2the minimum is.1versus-.2without disturbance; worst-case drift at the robust minimum is-.2=-h.'),
 ('8', [C+'high_order_initial_check',J+'high_order_actual_auxiliary'],
  'Actual derivatives of the specifiedp,vtrajectories givepsi1=v+p,psi2=u+2v+p. At(1,-.4)the auxiliary value is.6and the input lower bound is-.2;(.1,-1)haspositivehbutnegativepsi1, so it fails the auxiliary initial-set requirement.'),
 ('9', [C+n for n in ['cube_defines_halfline','cube_boundary_derivative','outward_trajectory_derivative','zero_gradient_does_not_imply_invariance']]+[J+'regular_defining_function_exposes_outward_derivative'],
  'The actual cubic safe set is the nonnegative half-line and its boundary derivative vanishes. The exact outward trajectory-t exits at every positive time. The regular defining functionxhas derivative1and exposes the strict outward derivative-1.'),
 ('10', [C+n for n in ['continuous_feedback_derivative','continuous_feedback_positive','held_first_interval_iff','held_first_interval_counterexample']]+[J+n for n in ['held_affine_derivative','held_ode_unique_on_interval','actual_held_interval_safety']],
  'The continuous exponential solves the feedback equation and stays positive. Any continuous held-input solution with right derivative-1and initial1equals1-tthroughout the first interval. That actual solution is safe iff horizon<=1and takesvalue-.5at1.5.'),
 ('11', [J+n for n in ['twoStepPlan','original_and_shifted_feasible_plans','terminal_controller_invariant']],
  'The actual original and shifted two-step state/input/terminal constraints all hold. For every terminal state, the appended controller-xrespects actuator bounds and takes the successor to0in the terminal set.'),
 ('12', [J+n for n in ['robustSuccessor','exact_original_shield','exact_robust_shield','exact_winning_set']],
  'Typed finite states/actions encode the given transitions. The exact original safe pairs are(a,L),(b,L),(b,R). Universal quantification over both disturbance successors removes(b,R); the exact robust winning set is{a,b}.'),
]
N = 'SafeLearning.CompleteBarrierTrajectories.'
trajectory_additions = {
    '4': (['actual_unit_equilibrium_trajectory','unit_equilibrium_vector_field_lipschitz',
           'unit_equilibrium_vector_field_smooth'],
          ' Every continuous solution with the stated right derivative and initial value equals that trajectory; the actual vector field is globally1-Lipschitz and smooth.'),
    '8': (['counterexample_position_ode','counterexample_velocity_ode',
           'final_auxiliary_identically_zero','auxiliary_initial_assumption_is_necessary'],
          ' An actual differentiable double-integrator trajectory starts at(.1,-1), satisfies the final inequality identically for all times, and nevertheless has negative position at time1. This demonstrates why the missing auxiliary initial condition cannot be discarded.'),
    '9': (['cubic_actual_derivative'],
          ' The actual cubic derivative3x^2is established at every realx, not just the boundary.'),
    '10': (['actual_zero_equilibrium_trajectory'],
           ' Every continuous solution of the stipulated continuous-feedback ODE with initial1equals the displayed exponential, by a proved integrating-factor uniqueness argument.'),
}
barrier_groups = [(number, names+[N+n for n in trajectory_additions.get(number,([],''))[0]],
                   statement+trajectory_additions.get(number,([],''))[1])
                  for number,names,statement in barrier_groups]
barrier_review_path = ROOT/'book/coverage/checks/barrier-examples-source-review.json'
barrier_reviews = {}
if barrier_review_path.exists():
    barrier_review = json.loads(barrier_review_path.read_text())
    if barrier_review['source_sha256']['SafeLearning/barriers.html'] != INV['source_sha256']['SafeLearning/barriers.html']:
        raise ValueError('Barrier exercise review has stale teaching source.')
    for name, expected in barrier_review['proof_source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
            raise ValueError('Barrier exercise review has stale proof: '+name)
    barrier_reviews = {r['exercise_key']: r for r in barrier_review['records']}
for number, names, statement in barrier_groups:
    key = 'barriers.html#exercise-10-p'+number
    review = barrier_reviews.get(key)
    full = bool(review and review['review_status']=='approved_complete_source' and
                not review['missing_clauses'] and review['per_exercise_reason'])
    gaps = [] if full else (review['missing_clauses'] if review and review['missing_clauses'] else
                           ['Independent atomwise review of every question and answer clause remains.'])
    add(key, names, statement, ['The exact real-valued, actuator or finite-state model in the source. Continuous ODE statements assume the encoded differentiability/continuity on the actual interval; predictive statements require the predicted first successor to match the realized one.'], gaps)

lyapunov_review_path = ROOT/'book/coverage/checks/compact-lyapunov-source-review.json'
lyapunov_full = False
if lyapunov_review_path.exists():
    lr = json.loads(lyapunov_review_path.read_text())
    if lr['source_sha256']['SafeLearning/lyapunov-mpc.html'] != INV['source_sha256']['SafeLearning/lyapunov-mpc.html']:
        raise ValueError('Stale compact Lyapunov teaching-source review.')
    original = next(e for e in INV['exercises'] if e['key']=='lyapunov-mpc.html::exercise-16')
    if lr['exercise_text_sha256'] != original['text_sha256']:
        raise ValueError('Stale compact Lyapunov exercise review.')
    for name, expected in lr['proof_source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
            raise ValueError('Stale compact Lyapunov proof review: '+name)
    lyapunov_full = lr['status']=='approved_complete_source' and not lr['remaining_gaps']
add('lyapunov-mpc.html::exercise-16',
    ['SafeLearning.CompleteCompactLyapunov.'+n for n in
     ['sublevel_forward_invariance','trajectory_values_antitone',
      'compact_strict_lyapunov_convergence','actual_lyapunov_values_converge_to_zero']]+[
     'SafeLearning.CompleteLyapunovMargins.'+n for n in
     ['uniform_strict_descent_on_compact','positive_minimum_on_compact',
      'compact_positive_value_slice','linear_lyapunov_descent_bound',
      'uniform_descent_incompatible_with_nonnegative_values']]+[
     'SafeLearning.CompleteLyapunovCounterexample.'+n for n in
     ['square_positive_definite','all_square_sublevels_compact','bad_map_fixes_zero',
      'strict_square_decrease_everywhere_off_zero','actual_orbit_initial',
      'actual_orbit_strictly_above_one','actual_orbit_step','actual_orbit_converges_to_one',
      'actual_images_converge_to_one','actual_orbit_does_not_converge_to_zero',
      'actual_map_discontinuous_at_one','actual_orbit_in_annulus',
      'increments_strictly_negative_on_annulus','actual_annulus_compact',
      'actual_increment_sequence_converges_to_zero','actual_increment_supremum_is_zero',
      'actual_increment_supremum_not_attained','actual_boundary_increment']]+
     ['SafeLearning.CompleteCoreMaterialLimits.actual_increment_right_limit_at_one'],
    'Actual sublevel trajectories are invariant with antitone nonnegative values; compactness, continuity and strict decrease imply state convergence to0and, whenV(0)=0,value convergence to0. Actual compact positive slices admit a uniform negative decrement and positive minimum; finite telescoping contradicts all-time nonnegativity. The exact source discontinuous piecewiseF fixes0and strictly decreasesV=x²off0with all sublevels compact, yet its actual trajectory from2is1+2^-nwith limit1. Its actual increment function has right-limit0at1, and least upper bound0on1<=|x|<=2, with no attaining point and boundary increment-3/4.',
    ['A continuous map and continuous nonnegative realV on a normed additive group; compact source sublevel, equilibriumF(0)=0, actual successor recurrence, initial sublevel membership and strict decrease off0. Source positive definiteness implies these sufficient assumptions. Uniform-margin and positive-minimum statements use the actual compact nonempty slices and their pointwise strict signs; no uniform margin is assumed.',
     'The counterexample is the exact scalar source model, without a continuity assumption; its discontinuity and nonzero limit are proved.'],
    [] if lyapunov_full else (lr['remaining_gaps'] if lyapunov_review_path.exists()
                             and lr['remaining_gaps'] else
                             ['Independent complete question/answer correspondence review remains.']))

lyapunov_hypotheses = {
    '1': 'The exact scalar functions F(x)=.6x and V(x)=x².',
    '2': 'The exact two-coordinate real matrix diag(4,1), with its actual quadratic form.',
    '3': 'The actual scalar successor .5x+w, with the stated absolute disturbance bound. The nonconverging counterexample supplies its actual constant disturbance and actual all-time trajectory.',
    '4': 'The stated immediate expected cost, discount and expected next budget are supplied numbers; no state convergence or pathwise-cost conclusion is inferred.',
    '5': 'An arbitrary pseudometric state space with the same distance throughout, actual5-Lipschitz decrease function, the stated sample error and upper estimate, and actual covering radius. The opposite-sign witnesses are actual compatible scalar decrease functions.',
    '6': 'The actual scalar error recurrence and all-time disturbance bound, initial tube membership, actual state x=z+e and actual input v-.5e.',
    '7': 'The exact finite-horizon real objective and input interval; no terminal, recursive-feasibility or infinite-horizon stability guarantee is inferred.',
    '9': 'The actual scalar polynomial map x-x³ and V=x²; c>0 for the complete sublevel characterization. Convergence assumes the actual successor recurrence and initial membership of the unit sublevel.',
    '10': 'The actual plant and approximate policy recurrence. Relative-error statements assume the supplied state-dependent pointwise error bound; the absolute-error counterexample supplies a genuine permitted constant error and its nonzero equilibrium trajectory.'}
for review_name in ['lyapunov-exercise-models-source-review.json',
                    'lyapunov-nonlinear-models-source-review.json']:
    path = ROOT/'book/coverage/checks'/review_name
    if not path.exists():
        continue
    review = json.loads(path.read_text())
    expected = INV['source_sha256']['SafeLearning/lyapunov-mpc.html']
    if review['source_sha256'] != expected:
        raise ValueError('Stale Lyapunov exercise teaching-source review: '+review_name)
    for name, value in review['proof_source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != value:
            raise ValueError('Stale Lyapunov exercise proof review: '+name)
    for record in review['records']:
        key = record['exercise_key']
        original = next(e for e in INV['exercises'] if e['key']==key)
        if record['exercise_text_sha256'] != original['text_sha256']:
            raise ValueError('Stale Lyapunov exercise text review: '+key)
        full = (record['review_status']=='approved_complete_source' and
                not record['missing_clauses'] and bool(record['per_exercise_reason']))
        number = key.rsplit('-p',1)[1]
        add(key, record['lean_declarations'], record['per_exercise_reason'],
            [lyapunov_hypotheses[number]], [] if full else record['missing_clauses'])
        MAP[key]['source_review'] = dict(
            file=str(path.relative_to(ROOT)),
            sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            nonformal_scope_clauses=record.get('nonformal_scope_clauses',[]))

def sha(p):
    return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

practice_hypotheses = {
    'barriers.html#exercise-10-p5': ['The actual real two-input objective and half-space constraint; KKT stationarity uses the actual coordinate derivatives.'],
    'cmdp.html#exercise-8-p6': ['One self-looping state and the stated stationary two-action marginal PMF, with deterministic reward/cost given the action, discount1/2 and budget1. The expectation of the infinite random return is derived without intertime independence.'],
    'cmdp.html#exercise-8-p9': ['The same actual policy-probability domain[0,1], reward2+6p and cost4p. The unique dual minimum belongs to the nonnegative multiplier domain.'],
    'cmdp.html#exercise-8-p5': ['The actual deterministic two-state path starts at0, moves to1 and stays there; discount1/2 and rewards0,2.'],
    'barriers.html::exercise-20': ['The actual three-state min/max safety operator, margins2/1/-1 and discount1/2. The general interpolation statement assumes a discount in[0,1] and interpolates current and clipped future margin.']}
for review_name in ['two-input-projection-source-review.json',
                    'policy-mixing-source-review.json',
                    'discounted-flow-source-review.json',
                    'safety-bellman-source-review.json']:
    path = ROOT/'book/coverage/checks'/review_name
    if not path.exists():
        continue
    review = json.loads(path.read_text())
    if review['source_sha256'] != INV['source_sha256'][review['source']]:
        raise ValueError('Stale practice source review: '+review_name)
    for name, expected in review['proof_sha256'].items():
        if sha(name) != expected:
            raise ValueError('Stale practice proof review: '+name)
    for record in review.get('exercises', [review]):
        key = record['exercise_key']
        original = next(e for e in INV['exercises'] if e['key']==key)
        if record['exercise_text_sha256'] != original['text_sha256']:
            raise ValueError('Stale practice text review: '+key)
        clauses = record['reviewed_clauses']
        mathematical = [c for c in clauses if c['status']=='approved']
        gaps = record.get('missing_clauses', review['missing_clauses'])
        if (review['status']!='independent_source_correspondence_review_passed' or
                any(c['status'] not in ('approved','not_a_formal_claim') for c in clauses) or
                not mathematical):
            raise ValueError('Unapproved practice source clauses: '+key)
        names = list(dict.fromkeys(n for c in mathematical for n in c['lean_declarations']))
        if not names or any(not c['reason'] for c in clauses):
            raise ValueError('Missing practice correspondence: '+key)
        add(key, names, ' '.join(c['reason'] for c in mathematical),
            practice_hypotheses[key], gaps)
        MAP[key]['source_review'] = dict(file=str(path.relative_to(ROOT)),
            sha256=sha(str(path.relative_to(ROOT))),
            nonformal_scope_clauses=[c for c in clauses if c['status']=='not_a_formal_claim'])

confidence_path = ROOT/'book/coverage/checks/lyapunov-confidence-source-review.json'
if confidence_path.exists():
    review = json.loads(confidence_path.read_text())
    if review['status']!='approved_complete_source' or review['missing_clauses']:
        raise ValueError('Unresolved independent validation-confidence review.')
    for name, expected in review['source_sha256'].items():
        if INV['source_sha256'][name] != expected:
            raise ValueError('Stale confidence teaching source: '+name)
    for name, expected in review['proof_source_sha256'].items():
        if sha(name) != expected:
            raise ValueError('Stale confidence proof review: '+name)
    for evidence in review['actual_compiler_evidence']:
        if (evidence['actual_exit_code'] != 0 or
                sha(evidence['standalone_manifest']) != evidence['standalone_manifest_sha256'] or
                sha(evidence['raw_log']) != evidence['raw_log_sha256']):
            raise ValueError('Changed actual confidence compiler evidence.')
    for key, expected in review['exercise_text_sha256'].items():
        original = next(e for e in INV['exercises'] if e['key']==key)
        if original['text_sha256'] != expected:
            raise ValueError('Stale confidence question/hint/answer: '+key)
        components = [c for c in review['components'] if c['exercise_key']==key]
        if not components or any(c['status']!='approved_precise_component' or
                c['missing_clauses'] or not c['scope_and_reason'] for c in components):
            raise ValueError('Unapproved confidence source component: '+key)
        names = list(dict.fromkeys(n for c in components for n in c['lean_declarations']))
        hypotheses = {
            '8': 'A fixed controller and sample size1000; actual IID measurable Bernoulli failure trials with common population probabilityp. The confidence event is over repeated validation samples, and no posterior interpretation is inferred.',
            '11': 'Actual IID Bernoulli trials for each fixed controller. The twenty-controller family is fixed before validation; within-controller IID sampling is required, while independence across controllers is not. Outcome-based selection is restricted to that fixed family.',
            '12': 'Actual robust safety holds for every model in the learned uncertainty set and every relevant state; the true-model membership event then implies actual safety. The two-event bound needs no independence. The counterexample constructs actual random learned function sets under the uniform Fin100 law.'}
        add(key, names, ' '.join(c['scope_and_reason'] for c in components),
            [hypotheses[key.rsplit('-p',1)[1]]])
        MAP[key]['source_review'] = dict(file=str(confidence_path.relative_to(ROOT)),
            sha256=sha(str(confidence_path.relative_to(ROOT))),
            nonformal_scope_clauses=[c for c in review['individual_scope_and_nonformal_classifications']
                                    if c['exercise_key']==key])

rows=[]
for e in INV['exercises']:
    if e['source'] not in SOURCES:
        continue
    m=MAP.get(e['key'])
    full=bool(m and not m['remaining_gaps'])
    claims=[]
    if m:
        claims.append(dict(id=e['key']+'::reviewed-component',kind='reviewed_mathematical_claim_group',
            status='proved',correspondence='The named declarations establish this precise group under the listed assumptions; any broader omissions are recorded below.',
            **{k:v for k,v in m.items() if k!='remaining_gaps'},remaining_gaps=[]))
    if not full:
        claims.append(dict(id=e['key']+'::remaining-source-review',statement_in_prose=e['source_text'],
            kind='remaining_exact_source_requirements',status='pending',lean_declarations=[],
            hypotheses=[],correspondence='Exact complete question and solution preserved for the remaining subclaim review.',
            remaining_gaps=m['remaining_gaps'] if m else ['Every mathematical question/solution conclusion needs atom-by-atom review and exact correspondence.']))
    rows.append(dict(inventory_key=e['key'],source=e['source'],locator=e['locator'],label=e['label'],
        source_sha256=e['source_sha256'],text_sha256=e['text_sha256'],source_text=e['source_text'],
        status='complete_math' if full else ('partial' if m else 'pending'),claims=claims))

MATERIAL_REVIEW = {
    'cmdp.html::node-297': dict(
        names=['reward_lagrangian_bounded_above','lagrangian_affine','reward_dual_convex','reward_primal_le_each_dual','reward_weak_duality','cost_dual_concave','cost_weak_duality'],
        statement='The bounded-return Lagrangian is affine in finitely many multipliers. Its reward supremum dual is convex, bounds every feasible return and the primal supremum, and remains an upper bound after multiplier minimization. The cost infimum convention is concave and supplies a lower bound after multiplier maximization.'),
    'cmdp.html::node-1074': dict(
        names=['exact_maximizer_subgradient','scalar_lagrangian_derivative','projected_descent_sign','orthant_projection_global_minimum','strict_violation_strictly_increases_multiplier','slack_decreases_projected_multiplier'],
        statement='An exact maximizing policy supplies the stated dual subgradient. Projected descent equals the displayed violation update; the entrywise max is a global Euclidean orthant projection. Positive step size and strict violation increase the multiplier, and slack lowers it while preserving nonnegativity.'),
    'cmdp.html::node-1095': dict(
        names=['lagrangian_affine','reward_lagrangian_bounded_above','reward_dual_convex','feasible_reward_le_dual','reward_primal_le_each_dual','attained_reward_dual'],
        statement='Finite-coordinate affinity, the supremum convexity inequality, and the pointwise/primal weak upper duality argument are established generally; at an attained inner optimum the supremum equals the actual maximum.'),
    'cmdp.html::node-1096': dict(
        names=['cost_lagrangian_affine','cost_lagrangian_bounded_below','cost_dual_concave','cost_dual_le_feasible_cost','cost_each_dual_le_primal','cost_weak_duality','cost_dual_mirror','attained_cost_dual'],
        statement='The cost infimum dual satisfies the displayed concavity inequality and weak lower bounds, including its multiplier supremum. Negating the objective gives exactly the reward-dual sign mirror. At an attained inner minimum the infimum equals that value.'),
    'cmdp.html::node-1097': dict(
        names=['walk_dual_actual_supremum','walk_dual_max_formula','walk_dual_piecewise','walk_dual_convex','walk_dual_abs_form','walk_dual_kink','walk_dual_unique_minimum','walk_primal_optimum','walk_primal_attained_and_all_lagrangian_maximizers'],
        statement='The actual walkthrough supremum equals lambda+max(0,1-2lambda), with the stated two affine pieces. It is convex, non-differentiable at1/2, and its unique dual minimum and attained primal maximum both equal1/2.'),
}
# These approvals come from an independent, per-paragraph semantic review.
# DOM containment proposes candidates; it does not establish correspondence.
overlap_path = ROOT/'book/coverage/core-material-overlap-review.json'
for checkpoint in (8, 9):
    candidate_review = ROOT/f'book/coverage/core-material-overlap-review-{checkpoint}.json'
    if candidate_review.exists():
        overlap_path = candidate_review
overlaps = {}
if overlap_path.exists():
    review = json.loads(overlap_path.read_text())
    candidate_path = review['candidate_source']
    if sha(candidate_path) != review['candidate_sha256']:
        raise ValueError('Stale independent overlap candidates; repeat their review.')
    candidates = {c['source_unit_key']: c for c in
                  json.loads((ROOT/candidate_path).read_text())['records']}
    owners = {e['inventory_key']: e for e in rows}
    units = {u['key']: u for u in INV['material_source_units']}
    for name, expected in review['proof_source_sha256'].items():
        if sha(name) != expected:
            raise ValueError('Independently reviewed proof changed: '+name)
    for record in review['records']:
        accepted = {
            'approved_exact_overlap': ('approved_source_unit_keys', 'proved'),
            'approved_pedagogical_classification':
                ('classified_source_unit_keys', 'not_a_formal_claim'),
        }
        if record['review_status'] not in accepted:
            continue
        approved_list, material_status = accepted[record['review_status']]
        key = record['source_unit_key']
        if key in overlaps or key not in review[approved_list]:
            raise ValueError('Duplicate or unlisted overlap approval: '+key)
        candidate = candidates[key]
        unit = units[key]
        owner = owners[record['exercise_key']]
        if owner['status'] != 'complete_math' or record['missing_clauses']:
            raise ValueError('Overlap has an unresolved parent or clause: '+key)
        for field in ('exercise_key','source','source_sha256','unit_text_sha256',
                      'exercise_text_sha256'):
            if record[field] != candidate[field]:
                raise ValueError('Changed overlap '+field+': '+key)
        if (unit['source_sha256'] != record['source_sha256'] or
                unit['text_sha256'] != record['unit_text_sha256'] or
                owner['text_sha256'] != record['exercise_text_sha256']):
            raise ValueError('Changed overlap source: '+key)
        parent_hash = hashlib.sha256(json.dumps(owner['claims'], sort_keys=True).encode()).hexdigest()
        if parent_hash != record['reviewed_parent_claims_sha256']:
            raise ValueError('Changed independently reviewed parent claims: '+key)
        parent_refs = {n for c in owner['claims'] for n in c['lean_declarations']}
        if material_status == 'proved':
            if not record['lean_declarations'] or not set(record['lean_declarations']) <= parent_refs:
                raise ValueError('Overlap names declarations outside its reviewed parent: '+key)
        elif (record['lean_declarations'] or
              record.get('semantic_kind') != 'pedagogical_navigation' or
              record.get('material_status') != 'not_formalizable'):
            raise ValueError('Invalid individual pedagogical classification: '+key)
        if not record['per_unit_reason']:
            raise ValueError('Overlap lacks a specific semantic reason: '+key)
        overlaps[key] = dict(record=record, owner=owner, status=material_status)
material=[]
for u in INV['material_source_units']:
    if u['source'] not in SOURCES:
        continue
    reviewed=MATERIAL_REVIEW.get(u['key'])
    claim=dict(id=u['key']+'::semantic-review',source_unit_keys=[u['key']],
        source=u['source'],source_sha256=u['source_sha256'],text_sha256=u['text_sha256'],
        source_text=u['source_text'],
        statement_in_prose=reviewed['statement'] if reviewed else u['source_text'],
        kind='reviewed_mathematical_source_unit' if reviewed else 'mathematical_source_unit_review',
        status='proved' if reviewed else 'pending',
        lean_declarations=[D+n for n in reviewed['names']] if reviewed else [],
        hypotheses=['Finite constraint index set, bounded real returns and nonempty feasible policy family; an exact maximizer only for the subgradient and attained-case identification.'] if reviewed else [],
        correspondence='Exact source paragraph reviewed atomwise. The supremum/infimum statements extend the max/min convention, with explicit attained-case identification; no broader cited theorem is inferred.' if reviewed else 'Overlapping source unit retained; no proof inferred from keywords or theorem counts.',
        remaining_gaps=[] if reviewed else ['Split every mathematical assertion, including surrounding prose, into precise reviewed correspondences.'])
    if u['key'] in overlaps:
        entry = overlaps[u['key']]
        record, owner = entry['record'], entry['owner']
        claim.update(statement_in_prose=u['source_text'],
            kind=('independently_reviewed_exact_exercise_overlap'
                  if entry['status']=='proved' else 'reviewed_pedagogical_navigation'),
            status=entry['status'],
            lean_declarations=record['lean_declarations'],
            hypotheses=(list(dict.fromkeys(h for c in owner['claims'] for h in c['hypotheses']))
                        if entry['status']=='proved' else []),
            correspondence=record['per_unit_reason'], remaining_gaps=[],
            independent_review=dict(source=str(overlap_path.relative_to(ROOT)),
                sha256=sha(str(overlap_path.relative_to(ROOT))),
                exercise_key=record['exercise_key'],
                parent_claims_sha256=record['reviewed_parent_claims_sha256']))
    material.append(claim)

proofs=['CompleteBookProjects','CompleteConformal','CompleteCoreControl','CompleteCoreBook',
        'CompleteCoreProbability','CompleteWeightedProjection','CompleteCoreReturns','CompleteBudgetValue','CompleteDuality','CompleteCoreEntryModel','CompleteConformalCounterexample','CompleteProjectionCharacterization','CompleteProjectionGeometry','CompleteProjectionDifferential','CompleteProjectDomains','CompleteProjectOptima','CompleteBarrierExamples','CompleteBarrierTrajectories','CompleteCompactLyapunov','CompleteLyapunovMargins','CompleteLyapunovCounterexample','CompleteCoreMaterialLimits','CompleteLyapunovExerciseModels','CompleteLyapunovMetricModels','CompleteLyapunovNonlinearModels','CompleteTwoInputProjection','CompletePolicyMixing','CompleteDiscountedFlow','CompleteSafetyBellman','CompleteSafetyBellmanConsequences']
proof_files={f'verification/lean/SafeLearning/{p}.lean':sha(f'verification/lean/SafeLearning/{p}.lean') for p in proofs}
out=dict(schema_version=1,owner='core',status='in_progress_partial_coverage',
    generated_at_utc=datetime.now(timezone.utc).isoformat(),scope_pages=sorted(SOURCES),
    source_sha256={s:INV['source_sha256'][s] for s in sorted(SOURCES)},proof_files=proof_files,
    exercises=rows,material_claims=material,
    counts=dict(exercises=len(rows),exercise_statuses=dict(Counter(e['status'] for e in rows)),
                material_source_units=len(material)),
    limits=['This is a conservative work ledger, not a full coverage or current aggregate verification report.',
            'Original selected proofs remain available but are not automatically promoted to complete mathematical coverage.',
            'Physical model validity, research hypotheses and pedagogical advice require specific classification.'])
(ROOT/'book/coverage/core.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out['counts']))
