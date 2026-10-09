"""Exact reviewed foundations additions after the eight-module checkpoint.

Only entries in COMPLETE_EXERCISES close a whole exercise. Partial examples and
teaching assertions stay individually mapped; their surrounding units remain
pending when another mathematical assertion has not yet been encoded.
"""
from foundations_review import refs

def claim(statement, group, *names, hypotheses, correspondence):
    return dict(statement_in_prose=statement, lean_declarations=refs(group,*names),
                hypotheses=hypotheses, correspondence=correspondence)

COMPLETE_EXERCISES = {
 'mb-ex-f1':[
  claim('The square map has the declared five-element domain and four-element codomain, with image exactly {0,1,4}.',
        'CompleteFoundationsLogic','finite_square_image',
        hypotheses='The specified finite integer sets and square map.',
        correspondence='Exact finite evaluation establishes the image; the corresponding typed function is finiteSquare with squareDomain and squareCodomain in CompleteFoundationsTeaching.'),
  claim('The specified typed square map is neither injective nor surjective; -1 and 1 have equal square, and output 9 is unreachable.',
        'CompleteFoundationsTeaching','finite_square_classification','finiteSquare','squareDomain','squareCodomain',
        hypotheses='Exactly the declared finite domain and codomain, not the entire real square map.',
        correspondence='The noninjectivity and nonsurjectivity proof uses actual inhabitants of the declared subtype sets.')],
 'mb-ex-f8':[
  claim('The first two set iterates are {0,1} and {0,1,2}, with two strict increases and final fixed set {0,1,2}.',
        'PrimersFoundations','reachFive_iterates',
        hypotheses='The exact five-state fixed deterministic successor table and singleton seed 0.',
        correspondence='Exact finite successor computations; the two strict inclusions are separately checked by ExerciseBridges.reach_five_strict_increases.'),
  claim('Every iterate from index 2 onward equals {0,1,2}.',
        'CompleteFoundationsTeaching','stabilized_reachFive',
        hypotheses='The same exact reachFive map and seed.',
        correspondence='A quantified all-index result follows from the actual fixed-point iterate identity.'),
  claim('Union with the successor image is monotone on finite state sets; neither 3 nor 4 occurs at any iteration.',
        'CompleteFoundationsExerciseBridges','grow_image_monotone','reach_five_unreachable','reach_five_strict_increases',
        hypotheses='Arbitrary finite input subsets for monotonicity; the given table and seed for unreachability.',
        correspondence='The Finset image/union operator is proved monotone, and an all-time subset invariant excludes 3 and 4.')],
 'mb-ex-f9':[
  claim('The half-open interval is not closed; the halving self-map contracts by one half and has no fixed point there. Its sequence 1,1/2,... tends to excluded 0.',
        'CompleteFoundationsLogic','half_open_contraction_counterexample',
        hypotheses='X=(0,1] and g(x)=x/2.',
        correspondence='The exact self-map, contraction equality and absent fixed point are proved; Teaching.half_open_not_closed and half_open_counterexample_limit separately encode the missing hypothesis and limit.'),
  claim('The shifted halving map contracts by one half, has fixed equation exactly x=2, and fails to map [0,1] into itself despite that interval being closed.',
        'CompleteFoundationsExerciseBridges','half_shift_contraction','half_shift_fixed_point','closed_intervals_for_contraction',
        hypotheses='X=[0,1] and g(x)=x/2+1.',
        correspondence='The actual derivative-free distance identity and fixed equation are proved; Logic.selfmap_counterexample checks the exact failing endpoint and absence of a permitted fixed point.'),
  claim('Negation preserves [-1,1], is distance preserving without a contraction factor below 1, and has unique fixed point 0; from 1 the iterates are (-1)^n and do not converge.',
        'CompleteFoundationsExerciseBridges','negation_selfmap','negation_fixed_point','negation_iteration','closed_intervals_for_contraction',
        hypotheses='X=[-1,1] and g(x)=-x.',
        correspondence='The exact self-map, fixed equation and iteration are encoded; Logic.strict_contraction_counterexample and alternating_unit_sequence_not_convergent prove the remaining assertions. The existing fixed point witnesses that a missing assumption need not falsify every conclusion.')],
 'mb-ex-p7':[
  claim('A real-subtype self-map with the given one-third distance bound has at most one fixed point, without needing closedness or an existence premise.',
        'CompleteFoundationsExerciseBridges','subtype_contraction_uniqueness',
        hypotheses='Any real subset X, g:X->X, and the stated pairwise absolute-value inequality.',
        correspondence='The exact source subtype hypothesis implies uniqueness; no ContractingWith object or existing fixed point is silently assumed.'),
  claim('On (0,1], dividing by 3 is a one-third contraction self-map with no fixed point; the missing endpoint is precisely the closedness failure.',
        'CompleteFoundationsLogic','missing_endpoint_contraction',
        hypotheses='The displayed counterexample X=(0,1].',
        correspondence='Exact quantified self-map and distance identities plus the absent fixed point; Teaching.half_open_not_closed establishes the failed closedness hypothesis.')],
 'mb-ex-sequences-1':[
  claim('The first four values of 3/(t+1) are 3,3/2,1,3/4 and its limit is 0.',
        'CompleteFoundationsTeaching','sequence_initial_values',
        hypotheses='Natural-number indices including zero.',
        correspondence='Exact initial values; Limits.reciprocal_sequence_limit proves actual filter convergence.'),
  claim('The strict tolerance holds for every t>=T exactly when T>=30; the preceding term equals 0.1 and the next is 3/31, approximated by 0.09677 within 0.000005.',
        'CompleteFoundationsSequences','tolerance_all_future',
        hypotheses='The exact strict target 1/10 and sequence 3/(t+1).',
        correspondence='This proves the full all-future quantifier and necessity, using the pointwise iff. ExerciseBridges.reciprocal_decimal_enclosure checks the printed rounded approximation.')],
 'mb-ex-sequences-2':[
  claim('Every permitted reward sequence has an absolutely convergent discounted return of absolute value at most 4, and constant rewards 2 attain it.',
        'CompleteFoundationsSeries','discounted_return_bound',
        hypotheses='Discount=1/2 and |r_n|<=2 for every n.',
        correspondence='Actual infinite sum and summability, with ExerciseBridges.constant_discounted_return_attains supplying attainment.'),
  claim('Four terms of constant reward 2 sum to 15/4 and the actual omitted infinite tail is 1/4; at 8 and 9 terms the tails are 1/64 and 1/128.',
        'CompleteFoundationsSeries','half_discount_numbers','constant_discounted_tail',
        hypotheses='The same exact geometric discount, constant reward sequence and count-of-terms convention.',
        correspondence='Finite sum and actual shifted infinite sum are encoded, rather than a formula assumed to be a tail.'),
  claim('Uniformly over every permitted reward sequence the tail is at most 0.01 exactly when at least 9 terms are retained.',
        'CompleteFoundationsExerciseBridges','half_discount_uniform_minimal',
        hypotheses='T is a natural number and rewards obey the absolute bound 2.',
        correspondence='Sufficiency follows from the proved infinite-sum tail bound; necessity uses the actual constant-reward tail attainer.')],
 'mb-ex-sequences-3':[
  claim('The original V/x dissipation model with V0=3 implies x_t->0, at most 150 indices with norm at least 0.2, and an eventual index after all such excursions.',
        'CompleteFoundationsExerciseBridges','modeled_energy_conclusions',
        hypotheses='Any normed additive group, nonnegative V, V0=3 and the original all-index dissipation inequality.',
        correspondence='The exact model implies convergence and finite all-time excursion cardinality; the norm-threshold/squared-energy equivalence is checked rather than presumed.'),
  claim('No index bound follows solely from this budget: for every N the original model admits a trajectory with its sole norm-0.2 excursion at N.',
        'CompleteFoundationsExerciseBridges','arbitrarily_late_modeled_excursion',
        hypotheses='Scalar normed real states, which instantiate the original model.',
        correspondence='An explicit V and x satisfy V0=3, nonnegativity and the entire dissipation recurrence, with the unique excursion at arbitrary N.')],
 'mb-ex-bounds-2':[
  claim('For (-1)^t+1/(t+1), the supremum is 2 attained at 0, and the infimum is -1 and is never attained.',
        'CompleteFoundationsSequences','additive_alternation_extrema','additive_alternation_bounds','additiveAlternation',
        hypotheses='Every natural index, including the initial value.',
        correspondence='Actual IsLUB/IsGLB of the sequence range plus membership/nonmembership of the endpoints.'),
  claim('Its even and odd subsequences tend to 1 and -1; the actual limsup and liminf are respectively 1 and -1, and there is no limit.',
        'CompleteFoundationsSequences','additive_alternation_subsequences','additive_alternation_lims','alternating_limits',
        hypotheses='The exact additive alternation sequence.',
        correspondence='Order-theoretic Filter.limsup/liminf are bounded through vanishing perturbation and subsequence cluster points; nonconvergence follows by unique limits.')],
 'mb-ex-topology-3':[
  claim('The fine six-point grid has exact covering radius 0.1 and the coarse four-point grid exact radius 0.2 on [0,1].',
        'CompleteFoundationsGridExamples','fine_grid_covers','coarse_grid_covers','fine_grid_midpoint_distance','coarse_grid_midpoint_distance',
        hypotheses='Exactly the stated grid points and full real interval, not a sampled mesh.',
        correspondence='Every real point has the required grid witness; actual infimum distance at a midpoint proves sharpness.'),
  claim('The stipulated interval-local 3-Lipschitz inequality and sample margin 0.35 imply uniform lower margins 0.05 and -0.25 for the two grids.',
        'CompleteFoundationsGridExamples','exact_fine_grid_margin','exact_coarse_grid_margin',
        hypotheses='Only pairwise Lipschitz control within [0,1] and the exact sample inequalities.',
        correspondence='Universal interval certificates use actual covering witnesses; no stronger global Lipschitz hypothesis is substituted.'),
  claim('The actual function 0.35-3*infDist(x,coarseGrid) is globally 3-Lipschitz, equals 0.35 on every coarse node, and equals -0.25 at x=0.2.',
        'CompleteFoundationsGridExamples','coarseCounterexample','coarse_counterexample_lipschitz','coarse_counterexample_samples','coarse_counterexample_failure',
        hypotheses='Distance is the standard real metric infimum distance to the specified nonempty set.',
        correspondence='The precise distance function is used, with a checked exact midpoint infimum and all-node values, making the counterexample realizable.')],
 'mb-ex-asymptotics-1':[
  claim('For all n>=1, 2n^2 <= 2n^2+3n+1 <= 6n^2; the polynomial is Theta(n^2) with the stated constants.',
        'CompleteFoundationsRates','polynomial_explicit_growth','polynomial_bigO_with_six','polynomial_reciprocal_bigO_with_half','polynomial_theta',
        hypotheses='Natural n>=1, standard norm-based Asymptotics definitions atTop.',
        correspondence='Both explicit all-index inequalities and actual IsBigOWith/IsTheta objects are proved.'),
  claim('The true ratio tends to 2 and the polynomial is not little-o of n^2.',
        'CompleteFoundationsRates','polynomial_exact_ratio_limit','polynomial_not_littleO',
        hypotheses='The exact polynomial and n^2 denominator atTop; the zero initial denominator is excluded only eventually, as asymptotics requires.',
        correspondence='Actual ratio convergence implies failure of the actual IsLittleO predicate, with no shifted substitute for the source function.')],
 'mb-ex-asymptotics-2':[
  claim('For every integer T>=1, the two guaranteed errors are at most 0.1 exactly for T>=1600 and T>=80.',
        'CompleteFoundationsGridExamples','square_root_budget_iff','reciprocal_budget_iff',
        hypotheses='The specified mathematical error bounds and positive integer iteration count.',
        correspondence='The exact square-root and reciprocal inequalities are solved in both directions.'),
  claim('Under the stipulated operation costs the sufficient budgets are 160000 and 80000; B costs half as much despite tenfold per-iteration cost.',
        'CompleteFoundationsGridExamples','exact_budget_comparison',
        hypotheses='Exactly the stipulated constant operation costs 100 and 1000; no empirical wall-time model is inferred.',
        correspondence='Exact integer budgets and ratio. These are sufficient budgets under the given guarantees, not claims of exact realized errors.')],
}

COMPANIONS = {
 ('mb-ex-f8',0):refs('CompleteFoundationsExerciseBridges','reach_five_strict_increases'),
 ('mb-ex-f9',0):refs('CompleteFoundationsTeaching','half_open_not_closed','half_open_counterexample_limit'),
 ('mb-ex-f9',1):refs('CompleteFoundationsLogic','selfmap_counterexample'),
 ('mb-ex-f9',2):refs('CompleteFoundationsLogic','strict_contraction_counterexample','alternating_unit_sequence_not_convergent'),
 ('mb-ex-p7',1):refs('CompleteFoundationsTeaching','half_open_not_closed'),
 ('mb-ex-sequences-1',0):refs('CompleteFoundationsLimits','reciprocal_sequence_limit'),
 ('mb-ex-sequences-1',1):refs('CompleteFoundationsExerciseBridges','reciprocal_decimal_enclosure')+
    refs('PrimersFoundations','sequence_threshold')+refs('CompleteFoundationsTeaching','sequence_initial_values'),
 ('mb-ex-sequences-2',0):refs('CompleteFoundationsExerciseBridges','constant_discounted_return_attains'),
 ('mb-ex-sequences-3',0):refs('CompleteFoundationsLogic','telescoping_energy_budget','telescoping_summability','telescoping_state_convergence'),
}
for (anchor,index),names in COMPANIONS.items():
    COMPLETE_EXERCISES[anchor][index]['lean_declarations'] += names

COMPLETE_EXERCISES['primer-basics.html::exercise-47'] = [
 claim('The image of x/(1+x) on nonnegative reals is exactly [0,1); it strictly increases and tends to 1 at infinity. Thus the infimum/minimum is 0, supremum is 1, and there is no maximum.',
       'CompleteFoundationsExtrema','fraction_image','fraction_strictly_increases','fraction_extrema','fraction_limit_at_infinity',
       hypotheses='The exact nonnegative real domain in part (a).',
       correspondence='Actual set image and IsGLB/IsLUB, attained/nonattained endpoint membership, StrictMonoOn and filter limit; no numerical sequence substitutes for the continuous domain.'),
 claim('The multiplicative alternating sequence has the four printed initial values, even terms decreasing to 1 and odd terms increasing to -1; both range extrema 2 and -3/2 are attained, and actual limsup/liminf are 1 and -1.',
       'CompleteFoundationsSequences','multiplicative_alternation_extrema','multiplicative_alternation_lims','multiplicative_alternation_subsequences','multiplicativeAlternation',
       hypotheses='The exact multiplicative sequence in part (b), distinct from the additive sequence of exercise0.5b.',
       correspondence='Order-theoretic extrema and limsup/liminf and actual subsequence limits; Extrema.multiplicative_initial_values and even_odd_monotonicity encode the remaining finite and monotonicity assertions.'),
 claim('The supremum of sin(x)+cos(x) is sqrt(2), attained at pi/4, with the exact shifted-sine identity. The individual suprema are both 1, cannot be simultaneously attained, and sqrt(2) rounds to 1.414 and is less than 2.',
       'CompleteFoundationsExtrema','sine_cosine_supremum','sine_cosine_attains','sine_cosine_shift','individual_trig_suprema','trig_decimal_and_strict_gap',
       hypotheses='The whole real domain and ordinary real sine and cosine.',
       correspondence='Actual range least upper bounds and attainers, plus a rational rounded-decimal enclosure and strict gap. The bound on the sum is proved without assuming its optimum.'),
 claim('For xy on [-1,1]^2 the inner supremum is |x| and inner infimum is -|y|, both nested extrema equal 0, and (0,0) satisfies the saddle inequalities.',
       'CompleteFoundationsExtrema','bilinear_inner_supremum','bilinear_inner_infimum','bilinear_outer_values','actual_bilinear_minimax_values',
       hypotheses='Both exact closed intervals; the inner statements actually hold for any fixed real coefficient.',
       correspondence='Actual IsLUB/IsGLB are converted to actual nested sInf/sSup expressions, and saddle inequalities are encoded separately.')]
COMPLETE_EXERCISES['primer-basics.html::exercise-47'][1]['lean_declarations'] += refs(
    'CompleteFoundationsExtrema','multiplicative_initial_values','even_odd_monotonicity')

# Full source-unit promotions only after checking every contained assertion.
FULL_MATERIAL = {
 'primer-basics.html::node-822':refs('CompleteFoundationsConvergence',
   'real_convergence_definition','vector_convergence_definition','euclidean_coordinatewise_convergence',
   'real_divergence_to_infinity_definition','real_cauchy_definition','complete_converges_iff_cauchy'),
 'primer-basics.html::node-826':refs('CompleteFoundationsConvergence','real_convergence_definition'),
 'primer-basics.html::node-829':refs('CompleteFoundationsConvergence','reciprocal_tolerance_choice','reciprocal_strictness_disappears')+
   refs('CompleteFoundationsLogic','alternating_unit_sequence_not_convergent'),
 'primer-basics.html::node-831':refs('CompleteFoundationsTeaching','limit_arithmetic','continuous_limits')+
   refs('CompleteFoundationsConvergence','limits_preserve_weak_order','limit_squeeze','reciprocal_strictness_disappears'),
}
PARTIAL_MATERIAL = {
 'primer-basics.html::node-839':[
  ('On a finite domain, pointwise convergence implies the uniform epsilon/T quantifier.',
   refs('CompleteFoundationsConvergence','finite_pointwise_uniform_tolerance'))],
 'primer-basics.html::node-922':[
  ('For 0<q<1 and positive initial error and tolerance, q^n*e0<=epsilon iff n>=log(e0/epsilon)/log(1/q).',
   refs('CompleteFoundationsGridExamples','geometric_accuracy_log_iff'))],
 'primer-optimization.html::node-817':[
  ('For the scalar quadratic with curvature4 and nonzero start, the actual gradient iteration tends to zero iff0<eta<1/2; expanding factors give divergent norms.',
   refs('CompleteFoundationsAlgorithms','scalar_gradient_converges_iff','expanding_scaling_norm','scaling_iteration')),
  ('For the exact two-curvature quadratic, all coordinate iterates and objective values at steps1/10 and2/11 are encoded, and step2/11 uniquely minimizes the largest coordinate contraction factor.',
   refs('CompleteFoundationsAlgorithms','diagonal_iteration','slow_coordinate_objective','balanced_step_objective','best_constant_diagonal_step'))],
 'primer-optimization.html::node-838':[
  ('On a diagonal quadratic with nonzero diagonal curvatures, the Newton correction divides each gradient coordinate by its actual curvature and reaches zero in one step, independently of the condition ratio.',
   refs('CompleteFoundationsAlgorithms','diagonal_gradient_and_hessian','newton_diagonal_independent_of_conditioning'))],
}

PARTIAL_EXERCISES = {
 'primer-optimization.html#opt-ex-descent-1':[
  claim('The actual scalar gradient-update trajectory converges to the minimizer from a nonzero start exactly for0<eta<1/2; outside the unit-factor range norms expand, and within it the quadratic objective does not increase.',
        'CompleteFoundationsAlgorithms','scalar_gradient_converges_iff','scalar_gradient_objective_decreases','expanding_scaling_norm','scaling_iteration',
        hypotheses='The exact curvature4 model and actual functional iterates; nonzero-start necessity is explicit.',
        correspondence='This is a genuine convergence iff and actual dynamics, not merely the algebraic inequality|1-4eta|<1. Source derivative and every printed finite case remain conservatively pending for full clause review.')],
 'primer-optimization.html::exercise-33':[
  claim('For the exact diagonal quadratic from start(10,1), the actual objective first drops below1e-6 at iterations85 for eta1/10 and45 for eta2/11; the latter step uniquely minimizes the largest coordinate contraction factor.',
        'CompleteFoundationsAlgorithms','diagonal_iteration','slow_coordinate_objective','balanced_step_objective','slow_coordinate_minimal_budget','balanced_step_minimal_budget','best_constant_diagonal_step',
        hypotheses='The exact original function, initial point and constant steps.',
        correspondence='Generic iterates derive the true objective formulas, which are solved with universal integer iff statements, including the index-zero exception for the first formula.'),
  claim('Step21/100 gives divergence of the actual second-coordinate magnitude. The actual gradient and Hessian partials are encoded and the Newton correction reaches zero independently of nonzero diagonal curvatures.',
        'CompleteFoundationsAlgorithms','unstable_diagonal_coordinate','diagonal_gradient_and_hessian','diagonal_newton_one_step','newton_diagonal_independent_of_conditioning',
        hypotheses='The source diagonal quadratic and its actual update; arbitrary nonzero curvatures only for the stronger general Newton identity.',
        correspondence='Actual divergence, derivative objects and correction identities; remaining explanation of every exact finite calculation and condition-number identification is not silently promoted.')],
}

COMPLETE_EXERCISES['opt-ex-lipschitz-1'] = [
 claim('The square map is 4-Lipschitz on [-2,2], and every valid interval Lipschitz bound is at least4.',
       'CompleteFoundationsLipschitzCalculus','square_lipschitz_on_radius','square_interval_sharp',
       hypotheses='The exact closed interval; the sharpness proof permits an arbitrary real candidate bound.',
       correspondence='All pairs in the actual interval satisfy the bound. A candidate below4 leads to an explicit violating pair, so optimality is proved without assuming a derivative supremum.'),
 claim('There is no finite real global Lipschitz constant for the square map.',
       'CompleteFoundationsLipschitzCalculus','square_not_globally_lipschitz',
       hypotheses='The entire real domain, as stated in the exercise.',
       correspondence='For every candidate constant an actual real pair violates the inequality; the growing chord-slope argument is encoded directly.'),
 claim('The actual derivative of the square map is2x and is globally2-Lipschitz; every valid bound for that derivative is at least2.',
       'CompleteFoundationsLipschitzCalculus','square_gradient_smooth','square_gradient_constant_sharp',
       hypotheses='All real points; smoothness concerns the actual derivative, not a separate proposed function.',
       correspondence='HasDerivAt identifies the derivative, a global LipschitzWith object gives sufficiency, and the pair1,0 establishes the smallest constant.')]

FULL_MATERIAL['primer-optimization.html::node-455'] = refs('CompleteFoundationsLipschitzCalculus',
 'real_lipschitz_chord_and_continuity','absolute_and_sine_lipschitz',
 'square_not_globally_lipschitz','square_lipschitz_on_radius','square_locally_lipschitz',
 'square_root_continuous_but_not_lipschitz','stepFunction','step_not_continuous_at_zero')
REVIEWED_COMPLETE_MATERIAL = {
 'primer-optimization.html::node-455':[
  claim('A real-valued Lipschitz function satisfies the displayed chord/cone inequality and is continuous.',
        'CompleteFoundationsLipschitzCalculus','real_lipschitz_chord_and_continuity',
        hypotheses='Any pseudometric input space and a finite nonnegative LipschitzWith bound; the source real interval is an instance.',
        correspondence='The inequality is the actual real metric bound, and LipschitzWith.continuous proves the continuity implication.'),
  claim('Absolute value and sine are globally1-Lipschitz on the real line.',
        'CompleteFoundationsLipschitzCalculus','absolute_and_sine_lipschitz',
        hypotheses='The standard real metric and the exact two source functions.',
        correspondence='Both actual global LipschitzWith objects are provided.'),
  claim('The square map has no finite global Lipschitz bound, is2R-Lipschitz on [-R,R] for R>=0, and is locally Lipschitz.',
        'CompleteFoundationsLipschitzCalculus','square_not_globally_lipschitz','square_lipschitz_on_radius','square_locally_lipschitz',
        hypotheses='Every nonnegative radius and all real pairs in its closed interval; the local statement is on the entire real line.',
        correspondence='The factored chord identity proves the interval bound, an explicit violating pair refutes every global constant, and the actual smooth square map gives local Lipschitz continuity.'),
  claim('The square root is continuous on [0,1] but has no Lipschitz bound there; the actual step x↦1 if x>0 and0 otherwise is discontinuous at0.',
        'CompleteFoundationsLipschitzCalculus','square_root_continuous_but_not_lipschitz','stepFunction','step_not_continuous_at_zero',
        hypotheses='The exact unit interval for square root and the ordinary real domain for the nonconstant step.',
        correspondence='Actual continuity plus failure of every candidate LipschitzWith bound proves the converse implication fails; positive reciprocal arguments tend to0 while their step values stay1.')]
}
PARTIAL_MATERIAL.setdefault('primer-optimization.html::node-460',[]).append(
 ('On an open convex domain, a differentiable function between real normed spaces is L-Lipschitz exactly when every actual Frechet derivative has operator norm at mostL; L is a finite nonnegative bound.',
  refs('CompleteFoundationsLipschitzCalculus','derivative_bound_iff_lipschitz')))
PARTIAL_MATERIAL.setdefault('primer-optimization.html::node-468',[]).extend([
 ('Composition and addition multiply/add valid Lipschitz bounds. Scaling, bounded products and reciprocals away from zero have the actual stated pairwise bounds.',
  refs('CompleteFoundationsLipschitzCalculus','composition_lipschitz','sum_lipschitz',
       'scaled_lipschitz','bounded_product_lipschitz','reciprocal_lipschitz')),
 ('C1 functions are locally Lipschitz; uniform separate Lipschitz bounds in two arguments imply the stated sum bound on simultaneous changes.',
  refs('CompleteFoundationsLipschitzCalculus','c1_locally_lipschitz','two_argument_lipschitz'))])
PARTIAL_MATERIAL.setdefault('primer-optimization.html::node-476',[]).extend([
 ('Every iterate of a non-expansive map is non-expansive. The actual scalar Euler map (1-hk)x is non-expansive exactly when0<=hk<=2.',
  refs('CompleteFoundationsLipschitzCalculus','nonexpansive_iterate','nonexpansive_scalar_euler_iff')),
 ('For nonempty bounded-below real families with bounded differences, the absolute difference of actual infima is at most the actual supremum of pointwise differences.',
  refs('CompleteFoundationsLipschitzCalculus','uniformly_close_infima','infima_difference_le_sup')),
 ('Under non-expansive dynamics and an L-Lipschitz margin function, the actual infinite trajectory infimum is L-Lipschitz in the starting point when every trajectory has a finite margin.',
  refs('CompleteFoundationsLipschitzCalculus','nonexpansive_trajectory_margin_lipschitz'))])
PARTIAL_MATERIAL['primer-optimization.html::node-817'].append(
 ('For arbitrary positive curvatureL, the actual derivative of (L/2)x^2 isLx, the exact gradient iterates are(1-eta*L)^n*x0, and convergence to zero from a nonzero start is equivalent to0<eta<2/L. A zero start stays zero and converges for every step size.',
  refs('CompleteFoundationsLipschitzCalculus','scalar_quadratic_derivative',
       'scalar_gradient_general_iteration','scalar_gradient_general_converges_iff',
       'scalar_gradient_zero_start','scalar_gradient_zero_converges')))

COMPLETE_EXERCISES['opt-ex-descent-1'] = [
 claim('The actual derivative of2x^2 is4x, its gradient is4-Lipschitz, and the actual gradient iterates from2 equal2(1-4eta)^n.',
       'CompleteFoundationsQuadraticExercises','actual_scalar_derivative','actual_scalar_second_derivative',
       'scalar_gradient_smooth','gradient_closed_form','gradient_recurrence',
       hypotheses='The exact scalar source function, real step and natural iteration index.',
       correspondence='Actual derivative objects identify the gradient; functional iteration proves both the update recurrence and the all-index closed form.'),
 claim('At eta0.4 the first iterates are-1.2 and0.72, signs alternate, magnitudes strictly shrink by0.6, and objective values decrease although the coordinate sequence is neither monotone nor antitone.',
       'CompleteFoundationsQuadraticExercises','source_initial_iterates','source_alternating_signs',
       'source_magnitude_strictly_decreases','source_coordinate_not_monotone','source_objective_decreases',
       hypotheses='Exactly eta2/5 and initial point2; all natural indices for the sign, magnitude and objective assertions.',
       correspondence='The same actual gradient trajectory supplies finite values and every all-time claim. Nonmonotonicity uses actual successive coordinates.'),
 claim('At eta0.25 every iterate from the first is the unique minimizer0; at eta0.5 the trajectory alternates forever between2 and-2 and has no limit; at eta0.6 the printed-2.8 and3.92 occur and magnitudes tend to infinity.',
       'CompleteFoundationsQuadraticExercises','quarter_step_reaches_minimum','scalar_unique_global_minimum',
       'half_step_forever_alternates','half_step_has_no_limit','source_initial_iterates','source_large_step_diverges',
       hypotheses='The exact three source steps and initial point2.',
       correspondence='All-future iteration identities and actual filter nonconvergence/divergence encode the full behavior, rather than merely inspecting the first two updates.'),
 claim('For a nonzero initial point convergence to0 holds exactly for0<eta<1/2=2/L withL4.',
       'CompleteFoundationsAlgorithms','scalar_gradient_converges_iff',
       hypotheses='The source curvature4 model and a nonzero initial point, including the given2.',
       correspondence='A genuine convergence iff proves necessity and sufficiency, with the initial-point exception explicit.')]

SURROUNDING_PROSE = {
 'primer-optimization.html::node-859': dict(
  proved=[claim('Every step eta>2/L on the actual scalar quadratic withL>0 diverges in magnitude from every nonzero initial point; a zero initial point stays0 for every step.',
                'CompleteFoundationsQuadraticExercises','generic_oversized_gradient_diverges',
                hypotheses='Positive real curvature, step greater than2/L and nonzero initial point; the zero-start statement permits every step.',
                correspondence='The actual gradient functional iterates have norm tending to infinity. LipschitzCalculus.scalar_gradient_zero_start proves the explicit zero-start exception.')],
  pending=['Constant-step SGD with persistent gradient noise generally does not converge exactly; a precise noise model and conclusion are still required.',
           'A zero gradient can be a saddle; an actual differentiable saddle example is still required.',
           'Rate notation hides constants; the exact asymptotic definitions and example correspondence remain pending for this sentence.',
           'Bisection of a monotone certificate predicate finds its largest certified radius; the convergence and incomplete-verifier interpretation remain pending.'])
}
SURROUNDING_PROSE['primer-optimization.html::node-859']['proved'][0]['lean_declarations'] += refs(
 'CompleteFoundationsLipschitzCalculus','scalar_gradient_zero_start')

COMPLETE_EXERCISES['opt-ex-descent-2'] = [
 claim('For the stated matrix quadratic the actual gradient isHx-c and its actual Hessian isH=diag(2,8); H is positive definite, Hx=c has exactly solution(1,1), and that point is the unique global minimizer.',
       'CompleteFoundationsShiftedQuadratic','objective_is_stated_matrix_quadratic','objective_frechet_derivative',
       'objective_actual_gradient','gradient_identification','gradient_is_Hx_minus_c','gradient_actual_hessian',
       'hessian_positive_definite','stationary_equation_iff','completed_square_identity','unique_global_minimum',
       hypotheses='The exact Euclidean two-dimensional function and sourceH/sourceC, on the whole real plane.',
       correspondence='Actual Frechet and gradient objects are identified for the source matrix expression. Completed squares establish a quantified unique global minimum without assuming stationarity is sufficient.'),
 claim('The Newton equation has the unique correction(1-x1,1-x2), and its full step solves this objective from every point because the quadratic Taylor model is exact. From(3,0) the gradient is(4,-8), correction(-2,1), and result(1,1).',
       'CompleteFoundationsShiftedQuadratic','quadratic_taylor_model_exact','newton_equation_unique',
       'full_newton_step_solves','source_numerical_steps',
       hypotheses='All starting points for the exact Newton solve; the stated initial point for the printed calculation.',
       correspondence='The correction solves the actual Hessian equation, with uniqueness. The exact model identity and full-step theorem prove the algorithm solves this full objective.'),
 claim('The actual gradient step1/8 from(3,0) gives(2.5,1), whose first-coordinate error is1.5 and whose positive objective gap is2.25. H has exactly eigenvalues2 and8 and its Euclidean operator condition number is4.',
       'CompleteFoundationsShiftedQuadratic','source_numerical_steps','gradient_step_remaining_error',
       'actual_eigenvalues','actual_matrix_inverse','matrix_condition_number',
       hypotheses='The exact source matrix, initial point and scalar gradient step; condition number uses the Euclidean induced operator norm.',
       correspondence='The actual gradient operation is evaluated, and the source eigenvalue claims are expressed by nonzero eigenvectors with an iff excluding other values. The actual inverse and both induced norms give the condition number.')]

PARTIAL_MATERIAL['primer-optimization.html::node-838'].append(
 ('For the source shifted diagonal quadratic, the actual Frechet Hessian ispositive definite, its Taylor quadratic model isexact, and the Hessian equation has a unique Newton correction that reaches the unique global minimizer inone full step.',
  refs('CompleteFoundationsShiftedQuadratic','gradient_actual_hessian','hessian_positive_definite',
       'quadratic_taylor_model_exact','newton_equation_unique','full_newton_step_solves','unique_global_minimum')))

COMPLETE_EXERCISES['opt-ex-lipschitz-3'] = [
 claim('The entire recurrence is bounded by the actual finite geometric sum; from the common start its envelope equals0.05(1.2^t-1).',
       'CompleteFoundationsModelErrors','errorEnvelope','recurrence_envelope','envelope_geometric_form','exact_source_error_envelope',
       hypotheses='The specified all-index recurrence and zero initial distance; generic proof assumes only a nonnegative multiplier.',
       correspondence='Induction proves the actual all-time bound, the finite sum is evaluated by the geometric identity, and zero initial distance removes the initial-state term.'),
 claim('The source powers at indices5 and6 equal2.48832 and2.985984; the guaranteed distance bounds are0.074416 and0.0992992.',
       'CompleteFoundationsModelErrors','source_error_numbers','recurrence_envelope',
       hypotheses='Exact rational constants6/5 and1/100, not floating point approximations.',
       correspondence='The printed finite powers and evaluated envelopes are checked exactly; the universal recurrence theorem transfers them to every permitted distance sequence.'),
 claim('For any actual metric trajectories and globally2-Lipschitz h, the corresponding predicted margin0.2 implies true margins at least0.051168 and0.0014016 at steps5 and6, both positive.',
       'CompleteFoundationsModelErrors','source_true_margin_bounds','source_bounds_nonnegative',
       hypotheses='Exactly the given common starting point, distance recurrence, global Lipschitz margin bound and predicted margin values.',
       correspondence='The actual distances between the two trajectories enter the recurrence, and the actual Lipschitz inequality transfers both guaranteed bounds to h of the true states.'),
 claim('The scalar true model1.2x+0.01 and predictor1.2x starting at0 attain the full accumulated envelope at every time; the predictor stays0, the true state stays nonnegative, and error at step5 exceeds0.01.',
       'CompleteFoundationsModelErrors','affine_iterations','zero_predictor_iterations','nonnegative_error_envelope','actual_affine_model_attains_bound','affine_model_one_step_error','affine_model_lipschitz','source_bounds_nonnegative',
       hypotheses='The exact source scalar model; the stronger generic attainer is proved for every nonnegative multiplier and disturbance.',
       correspondence='Functional iterates encode the actual dynamics. The model has the stipulated one-step error and Lipschitz constant, and its actual metric state error equals the envelope, so tightness is not merely an equality recurrence assumed separately.')]
PARTIAL_MATERIAL['primer-optimization.html::node-476'].extend([
 ('Actual Lipschitz true dynamics and a uniformly close predictor imply the stated distance-error recurrence and its all-time geometric envelope, including nonzero initial error and the unit-multiplier case.',
  refs('CompleteFoundationsModelErrors','model_distance_recurrence','model_distance_envelope','recurrence_envelope','envelope_geometric_form','envelope_unit_factor')),
 ('For one-step error0.01 and multiplier1.1 the exact ten-step envelope is0.15937424601 and is at most the corrected upward-rounded bound0.159375. Nonnegative affine true dynamics and zero-start linear prediction attain this envelope.',
  refs('CompleteFoundationsModelErrors','source_teaching_ten_step_bound','actual_affine_model_attains_bound','affine_model_one_step_error','affine_model_lipschitz'))])

COMPLETE_EXERCISES['opt-ex-lipschitz-2'] = [
 claim('An actual endpoint cubic grid with integer reciprocal spacing has sharp covering radius sqrt(d)/(2N), proved on the entire real cube. In particular the radii are0.05 in dimension1 and sqrt(3)/20 in dimension3 at spacing0.1.',
       'CompleteFoundationsCubicGrids','unitCube','unitGrid','gridPoint','nearest_coordinate','cube_grid_covers','cell_center_distance_lower','exact_cube_covering_radius','one_dimensional_distance',
       hypotheses='Positive integer N; actual Euclidean norm on the complete cube and the full tensor product grid, including endpoints.',
       correspondence='Coordinate rounding covers every real cube point; a cell center forces the opposite radius bound. IsLeast of the set of valid covering radii proves exactness. The dimension1 metric is explicitly identified with the real coordinate metric.'),
 claim('Interval-local2-Lipschitz control and lower samples0.15 give the uniform real lower margin0.05; in dimension3 the guaranteed lower bound is0.15-0.1sqrt(3).',
       'CompleteFoundationsCubicGrids','grid_margin','real_one_dimension_source_margin','three_dimension_source_margin',
       hypotheses='Exactly the local Lipschitz control inside the interval/cube and all actual grid sample inequalities.',
       correspondence='The actual grid covering witnesses and the actual pairwise Lipschitz inequalities derive the certificates, without substituting a stronger global bound.'),
 claim('The dimension3 margin is approximately-0.023205 and the spacing threshold0.15/sqrt(3) approximately0.086603;1/12 approximates0.083333, each within half a unit of the printed last decimal.',
       'CompleteFoundationsCubicGrids','sqrt_three_enclosure','source_grid_decimal_enclosures',
       hypotheses='Exact real square roots and rational printed decimals.',
       correspondence='Rational square-root enclosures establish absolute-error bounds for every printed approximation; no floating point oracle is used.'),
 claim('The certificate is nonnegative exactly for Delta<=0.15/sqrt(3). The actual equal-step grid with N=12 has2197 points and universally certifies nonnegativity under the given sample and Lipschitz bounds.',
       'CompleteFoundationsCubicGrids','required_three_dimension_spacing','grid_cardinality','grid_spacing_formula','twelve_step_grid_suffices','twelve_grid_certifies',
       hypotheses='The arithmetic threshold applies to the actual covering-radius certificate; equal endpoint steps correspond to positive integer N.',
       correspondence='Both directions of the threshold are proved, and the actual13^3 Finset cardinality and the universal12-step-grid certificate are encoded.'),
 claim('The coarse samples do not force a nonnegative function: an actual globally2-Lipschitz distance-to-grid function has exactly those samples and a negative cell-center value. The constant0.15 function is positive and also satisfies all coarse assumptions, so coarse-certificate failure does not prove the actual function is negative.',
       'CompleteFoundationsCubicGrids','cell_center_infimum_distance','gridMarginExample','grid_margin_example_lipschitz','grid_margin_example_samples','grid_margin_example_center','coarse_grid_cannot_certify_nonnegative','positive_function_consistent_with_coarse_samples',
       hypotheses='Actual Euclidean distance to the specified nonempty cubic grid and the complete cube.',
       correspondence='Both negative and positive compatible functions are constructed, rather than inferring logical impossibility merely from a negative numerical lower bound.')]
PARTIAL_MATERIAL.setdefault('primer-optimization.html::node-484',[]).extend([
 ('For every positive integerN and dimensiond, the actual full endpoint cubic grid of spacing1/N has exactly(N+1)^d points and sharp Euclidean covering radius sqrt(d)/(2N), equivalently sqrt(d)*Delta/2.',
  refs('CompleteFoundationsCubicGrids','unitCube','unitGrid','gridPoint','grid_cardinality','grid_spacing_formula','cube_grid_covers','exact_cube_covering_radius')),
 ('For those actual cubic grids, local L-Lipschitz control and grid samples at leasts imply a universal cube lower bound s-L*radius, and the distance-to-grid function realizes that bound at a cell center.',
  refs('CompleteFoundationsCubicGrids','grid_margin','gridMarginExample','grid_margin_example_lipschitz','grid_margin_example_samples','grid_margin_example_center')),
 ('The spacing0.1 cubic grid has11 points in dimension1 and1771561 points in dimension6, which rounds to1.8million.',
  refs('CompleteFoundationsCubicGrids','teaching_grid_cardinalities'))])

COMPLETE_EXERCISES['la-ex-norms-1'] = [
 claim('The actual three coordinate vector has l1 norm5, Euclidean norm3 and infinity norm2; its standard inner product with(1,2,0) is0 and both vectors are nonzero.',
       'CompleteFoundationsVectorModels','vector3','source_three_lengths','source_three_perpendicular',
       hypotheses='The exact source vectors, PiLp1, EuclideanSpace and the coordinate-function infinity norm respectively.',
       correspondence='Actual norm objects and the actual Euclidean inner product are evaluated, so perpendicularity is the standard zero-inner-product assertion rather than a detached arithmetic identity.'),
 claim('The computed lengths satisfy2<=3<=5<=3sqrt(3).',
       'CompleteFoundationsVectorModels','source_three_length_comparison','source_three_lengths',
       hypotheses='The source dimension3 and the actual three norm values.',
       correspondence='The printed comparison is checked with an exact real square-root argument.')]
COMPLETE_EXERCISES['la-ex-norms-2'] = [
 claim('For the actual infinity-norm ball of radius0.2 the linear objective w dot delta has greatest value1.4, attained at(0.2,-0.2).',
       'CompleteFoundationsVectorModels','box_objective_equals_dot','box_objective_upper','box_maximum',
       hypotheses='Exactly w=(3,-4), the complete real coordinate-function norm ball, and the standard dot product.',
       correspondence='A universal bound on the actual norm ball and an actual feasible attainer prove IsGreatest of the complete objective image.'),
 claim('For the actual Euclidean ball of radius0.2 the same linear objective has greatest value1, attained at(0.12,-0.16).',
       'CompleteFoundationsVectorModels','vector2','vector_two_norm','vector_two_inner','euclidean_objective_upper','euclidean_maximum',
       hypotheses='The actual Euclidean inner product with the source w, on the complete real ball.',
       correspondence='Cauchy-Schwarz gives the universal bound, and exact Euclidean norm and inner-product calculations verify the source attainer.'),
 claim('The Euclidean radius0.2 ball lies inside the radius0.2 infinity-norm box, whose stated corner lies outside that Euclidean ball.',
       'CompleteFoundationsVectorModels','euclidean_ball_inside_box','source_box_corner_outside_euclidean_ball',
       hypotheses='The same numerical radius in the two actual finite-dimensional norm models.',
       correspondence='All-coordinate norm control proves inclusion, and the actual corner norm proves strict difference of the feasible regions.')]
COMPLETE_EXERCISES['la-ex-norms-3'] = [
 claim('Distance to any set in a normed group is1-Lipschitz, including nonclosed sets. In a proper metric space a nonempty closed set has an actual nearest point, and the one-direction triangle argument gives the stated bound.',
       'CompleteFoundationsVectorModels','distance_to_any_set_lipschitz','nearest_point_exists','distance_one_direction_via_nearest',
       hypotheses='The Lipschitz bound does not require closedness; nearest-point existence uses properness, which holds in finite-dimensional Euclidean space.',
       correspondence='The actual Metric.infDist function is used. The source closest-point proof is encoded separately from the stronger bound that also handles nonclosed sets.'),
 claim('The actual distance from(3,4) to the closed Euclidean unit disc is4, attained at(3/5,4/5).',
       'CompleteFoundationsVectorModels','unitDisc','source_radial_point_attains','source_disc_distance','vector_two_norm',
       hypotheses='The actual Euclidean closed unit ball and the precise source vectors.',
       correspondence='A universal reverse-triangle lower bound and actual radial membership/distance give equality for the real infimum distance.'),
 claim('Every actual Euclidean displacement of norm at most0.1 puts the new distance in[3.9,4.1].',
       'CompleteFoundationsVectorModels','source_disc_perturbation','distance_to_any_set_lipschitz','source_disc_distance',
       hypotheses='Every direction of the displacement, with only the stated norm bound.',
       correspondence='The actual point after addition is compared through the proved set-distance Lipschitz inequality; both interval endpoints are derived.')]

COMPLETE_EXERCISES['la-ex-matrix-norms-1'] = [
 claim('For the actual matrix[[1,-2],[0,3]], the l1 induced operator norm is5, the infinity induced norm is3 and the Frobenius norm is sqrt(14). The source column sums are1,5, row sums3,3 and squared-entry sum14.',
       'CompleteFoundationsMatrixNormModels','smallMatrix','l1Map','small_matrix_l1_apply','small_matrix_l1_norm','small_matrix_infinity_norm','small_matrix_frobenius_norm','small_matrix_entry_sums',
       hypotheses='The l1 map acts between actual PiLp1 spaces; the other matrix norms explicitly use the Operator and Frobenius scopes.',
       correspondence='A universal l1 bound and actual attaining input identify the actual CLM operator norm. The two other actual norm objects and every printed entry sum are evaluated under the intended norm, not the default matrix norm.'),
 claim('The actual input(0,1) has l1 norm1, its actual image is(-2,3) with l1 norm5, and attains the operator bound.',
       'CompleteFoundationsMatrixNormModels','small_matrix_l1_attainment','small_matrix_l1_norm',
       hypotheses='Exactly the given actual matrix map and input.',
       correspondence='The finite matrix-vector product and both actual l1 norms are encoded, proving the bound is tight.')]
COMPLETE_EXERCISES['la-ex-matrix-norms-2'] = [
 claim('The actual diagonal matrices have spectral norms3 and3; their product is(3/2)I and has spectral norm3/2, strictly below the valid product bound9.',
       'CompleteFoundationsMatrixNormModels','firstStretch','secondStretch','diagonal_two_spectral_norm','stretch_individual_norms','actual_stretch_product','stretch_product_norm_and_bound',
       hypotheses='The actual Euclidean induced matrix norms use Matrix.Norms.L2Operator.',
       correspondence='The actual matrices, their actual product and actual induced norms are proved, including both validity and strictness of the bound.'),
 claim('Every actual Euclidean vector is scaled in length by3/2 under the composition. The first matrix maximally stretches the first coordinate, the second maximally stretches the second, and the first shrinks that second coordinate by1/2.',
       'CompleteFoundationsMatrixNormModels','stretch_product_every_vector','individual_stretch_directions','stretch_individual_norms',
       hypotheses='All actual Euclidean vectors for the length identity and the exact coordinate basis vectors for the directional explanation.',
       correspondence='Actual toEuclideanCLM actions establish the universal equality and the three directional stretches, explaining why the maximising directions fail to align.')]
COMPLETE_EXERCISES['la-ex-matrix-norms-3'] = [
 claim('The actual inverse of I-diag(1/2,1/4) is diag(2,4/3), and the actual spectral norm1/2 satisfies the Neumann hypothesis.',
       'CompleteFoundationsMatrixNormModels','tailMatrix','actual_tail_inverse','tail_source_numbers_and_neumann_hypothesis',
       hypotheses='The precise matrix and actual Euclidean induced norm.',
       correspondence='A verified inverse-product identity establishes the actual nonsingular inverse; the hypothesis is checked for the intended operator norm.'),
 claim('Subtracting the actual finite matrix power sum gives diag(2*(1/2)^T,(4/3)*(1/4)^T) for every naturalT. Its first coordinate dominates by the exact ratio(3/2)*2^T>=1, so its actual spectral norm is2*(1/2)^T=2^(1-T).',
       'CompleteFoundationsMatrixNormModels','partialSum','actual_tail_matrix','first_tail_coordinate_dominates','source_tail_ratio','exact_spectral_tail_norm','spectral_tail_integer_power',
       hypotheses='Every natural term countT including0; the last expression uses an integer exponent to preserve negative exponents.',
       correspondence='The actual inverse minus actual matrix sum is evaluated before taking its actual spectral norm. Geometric identities and both-coordinate comparison prove the exact tail; no scalar expression is assumed to represent the matrix remainder.'),
 claim('The actual spectral remainder is at most0.01 exactly whenT>=8. At7 and8 it equals0.015625 and0.0078125; the first unit coordinate attains the norm, and range8 consists exactly of indices0 through7.',
       'CompleteFoundationsMatrixNormModels','exact_tail_threshold','tail_source_numbers_and_neumann_hypothesis','first_basis_attains_tail','eight_term_indices','partialSum',
       hypotheses='Actual matrix remainder and natural integer indexing convention.',
       correspondence='A universal integer iff proves smallest-budget necessity and sufficiency, exact rational values check the printed decimals, and the actual CLM action proves attainment by the first basis vector.')]
