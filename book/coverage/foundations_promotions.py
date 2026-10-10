"""Exact reviewed foundations additions after the eight-module checkpoint.

Only entries in COMPLETE_EXERCISES close a whole exercise. Partial examples and
teaching assertions stay individually mapped; their surrounding units remain
pending when another mathematical assertion has not yet been encoded.
"""
from foundations_review import refs

REVIEWED_NONFORMAL_MATERIAL = {}

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

COMPLETE_EXERCISES['opt-ex-descent-3'] = [
 claim('On the positive domain, the actual derivatives ofx-logx are1-1/x and1/x^2. The Newton direction solves the actual Hessian equation and is a strict descent direction except at the unique global minimizer1.',
       'CompleteFoundationsLogBacktracking','actual_derivative','derivative_identification',
       'actual_second_derivative','second_derivative_identification','positive_hessian',
       'unique_global_minimum','newton_equation','newton_direction_formula','actual_descent_direction',
       hypotheses='The source logarithmic function onx>0; strict descent requiresx≠1.',
       correspondence='The second derivative is proved for the actual first derivative using its local positive-domain identity. The real logarithm tangent inequality establishes the unique global minimum.'),
 claim('At4, the derivatives are3/4 and1/16, the Newton direction is-12 and directional derivative-9. Full and half steps give-8 and-2 and are rejected by the domain test; a quarter step gives1 and satisfies Armijo withconstant1/4.',
       'CompleteFoundationsLogBacktracking','source_four_numerics','source_larger_steps_rejected',
       'source_quarter_step_accepted','source_first_accepted_backtracking_index',
       hypotheses='Exactly the source start4, backtracking factors(1/2)^k and Armijo constant1/4.',
       correspondence='The actual derivatives drive the update, and an IsLeast statement proves the quarter step is the first accepted candidate. The acceptance predicate explicitly requires positivity before the finite decrease inequality.'),
 claim('The Armijo left side is1, its right side rounds to2.051206 within half a unit of the last printed decimal, and the accepted point is the unique global minimizer.',
       'CompleteFoundationsLogBacktracking','source_armijo_decimal','log_four_bounds',
       'source_accepted_step_is_global_optimum','unique_global_minimum',
       hypotheses='The same source candidate and exact Armijo expression; decimal tolerance is1/(2*10^6).',
       correspondence='Proven rational enclosures for actual log4 establish the decimal assertion and the exact inequality; no floating point approximation is used as evidence.')]

PARTIAL_MATERIAL.setdefault('primer-optimization.html::node-843',[]).extend([
 ('For the positive-domain functionx-logx, the actual Newton full step is2x-x^2 and squares the error1-x; from1/2, every iterate stays in(0,1], has error(1/2)^(2^n), and tends to the unique minimizer1. All four printed iterates are evaluated or enclosed to their displayed precision.',
  refs('CompleteFoundationsLogBacktracking','unique_global_minimum','full_newton_step_formula',
       'source_half_initial_iterations','source_half_iteration_in_domain','source_half_error_closed_form',
       'source_half_iteration_converges')),
 ('From3, the actual Newton full and half steps leave the positive domain; the quarter step gives3/2 and is accepted by Armijo. The actual objective and right side are within0.0005 of the displayed1.095 and1.651.',
  refs('CompleteFoundationsLogBacktracking','source_three_domain_checks',
       'source_three_quarter_accepted_and_decimals','log_three_bounds'))])

COMPLETE_EXERCISES['la-ex-spectral-1'] = [
 claim('The actual Euclidean vectors(1,1)/sqrt2 and(1,-1)/sqrt2 are orthonormal eigenvectors with eigenvalues4 and2 and span the full real plane.',
       'CompleteFoundationsSpectralModels','source_eigenvectors','source_orthonormal',
       'source_eigenbasis_spans','norm_squared_coordinates','source_all_eigenvalues',
       hypotheses='Exactly sourceA=[[3,1],[1,3]] and the specified normalized vectors in EuclideanSpace.',
       correspondence='The actual matrix linear map and Orthonormal predicate are proved, with every vector reconstructed from its two inner-product coefficients. Original squared lengths follow from the proved coordinate norm identity.'),
 claim('The source matrix equals4qPlusqPlus^T+2qMinusqMinus^T.',
       'CompleteFoundationsSpectralModels','source_spectral_matrix_decomposition',
       hypotheses='The same actual matrix and normalized eigenvectors.',
       correspondence='An actual Matrix equality verifies all four entries of the spectral outer-product decomposition; it is not a detached eigenvalue calculation.')]

COMPLETE_EXERCISES['la-ex-spectral-2'] = [
 claim('For every Euclidean vector the actual quadratic form is between2 and4 times its squared length. Lower equality holds exactly whenx1=-x2, and upper equality exactly whenx1=x2.',
       'CompleteFoundationsSpectralModels','source_all_eigenvalues','source_quadratic_expansion',
       'rayleigh_bounds_and_equality',
       hypotheses='The exact sourceA and arbitrary Euclidean vectors, including0 for the undivided form.',
       correspondence='Actual inner product with the matrix linear map and actual Euclidean norm are related by a coordinate identity. Sum/difference squares prove both sharp bounds and equality iff statements.'),
 claim('At(1,2) the actual image is(5,7), form19, squared length5 and quotient19/5=3.8, with strict bounds10<19<20 and nonzero components in both normalized eigendirections.',
       'CompleteFoundationsSpectralModels','source_rayleigh_numerics','source_both_eigencomponents_nonzero',
       hypotheses='Exactly the stated vector and source matrix.',
       correspondence='The actual linear-map image, inner-product form, norm and quotient are evaluated; both eigencomponents and both strict inequalities are proved.'),
 claim('Every nonzero multiple of(1,-1) has quotient2 and every nonzero multiple of(1,1) has quotient4.',
       'CompleteFoundationsSpectralModels','source_rayleigh_attainers',
       hypotheses='An arbitrary nonzero real multiple; nonzero is needed for a genuine Rayleigh quotient.',
       correspondence='Both actual quotient expressions are proved for every permitted multiple, so endpoint attainment is universal in the stated directions.')]

COMPLETE_EXERCISES['la-ex-spectral-3'] = [
 claim('The actual nonsymmetric matrixN=[[1,4],[0,1]] has characteristic polynomial(X-1)^2 and every nonzero eigenvector has eigenvalue1 and second coordinate0. Its image of(1,-1) is(-3,-1), with actual quadratic form-2.',
       'CompleteFoundationsSpectralModels','source_N_characteristic_polynomial',
       'source_N_eigenvector_characterization','source_N_negative_form',
       hypotheses='The exact sourceN and actual Euclidean matrix map.',
       correspondence='The actual characteristic polynomial records both repeated eigenvalues, while an eigenvector iff proves the full real eigenspace statement. The counterexample evaluates the actual quadratic form.'),
 claim('The symmetric part is[[1,2],[2,1]] with exactly eigenvalues3 and-1 along(1,1) and(1,-1). The actual skew part transposes to its negative and contributeszero to every quadratic form, so the N and symmetric-part forms coincide.',
       'CompleteFoundationsSpectralModels','source_symmetric_and_skew_parts','symmetric_part_eigenvalues',
       'general_real_skew_quadratic_zero','source_forms_equal','norm_squared_coordinates',
       hypotheses='The specified real symmetric/skew decomposition; the zero-skew theorem also covers arbitrary finite real matrices.',
       correspondence='Actual matrix identities and all-and-only eigenvalues are proved. The general transpose argument proves vanishing of real skew forms, with an explicit bridge to the Euclidean inner-product forms.'),
 claim('N is not symmetric and has no orthonormal eigenbasis; its nonzero eigenvectors cannot even be pairwise orthogonal.',
       'CompleteFoundationsSpectralModels','source_N_not_symmetric',
       'source_N_eigenvectors_never_orthogonal','source_N_has_no_orthonormal_eigenbasis',
       hypotheses='The exact sourceN over the real Euclidean plane.',
       correspondence='The missing spectral-theorem hypothesis is explicit, and failure of an actual OrthonormalBasis consisting of eigenvectors is proved rather than inferred solely from nonsymmetry.')]

COMPLETE_EXERCISES['la-ex-psd-1'] = [
 claim('The actual diagonalP=diag(2,0) has form2x1^2 and is positive semidefinite, with determinant0 and nonzero zero-form witness(0,1), so it is singular and not positive definite.',
       'CompleteFoundationsDefinitenessModels','singular_P_positive_semidefinite',
       'singular_P_actual_form','singular_P_failure_witness',
       hypotheses='The source matrix on the whole real Euclidean plane.',
       correspondence='The actual Matrix.PosSemidef object and explicit Euclidean form identity establish all-direction nonnegativity. Actual determinant and nonzero witness establish singularity and PD failure.'),
 claim('Q=[[2,3],[3,2]] has positive entries but its actual forms at(1,1) and(1,-1) are10 and-2; hence both signs occur and Q is indefinite and not PSD.',
       'CompleteFoundationsDefinitenessModels','indefinite_Q_both_signs',
       hypotheses='The exact sourceQ and the displayed real witness vectors.',
       correspondence='Both actual inner-product forms, all-entry positivity and failure of the actual Matrix.PosSemidef predicate are proved. The positive-versus-zero witness distinction follows from these two actual classified matrices.')]

COMPLETE_EXERCISES['la-ex-psd-2'] = [
 claim('The actual factorL=[[2,0],[1,1]] is lower triangular with positive diagonal and P=LL^T; the sourceP is positive definite.',
       'CompleteFoundationsDefinitenessModels','cholesky_actual_factor','cholesky_positive_definite',
       hypotheses='Exactly sourceP=[[4,2],[2,2]] and factorL.',
       correspondence='Actual matrix equality and entries establish the factor properties, and the actual Matrix.PosDef predicate is proved through strict quadratic positivity in every nonzero direction.'),
 claim('The forward equationLy=(6,4) has unique solution(3,1), the backward equationL^Tx=y has unique solution(1,1), and actualPx=(6,4).',
       'CompleteFoundationsDefinitenessModels','forward_triangular_solve_unique',
       'backward_triangular_solve_unique','cholesky_source_solution',
       hypotheses='All candidate vectors for each specified triangular equation.',
       correspondence='Both complete solution iff statements use actual matrix linear maps; they verify the two-solve method and the source direct check without assuming an inverse.'),
 claim('ActualdetL=2 anddetP=(detL)^2=4, with actuallogdetP=2(log2+log1)=log4.',
       'CompleteFoundationsDefinitenessModels','cholesky_actual_log_determinant',
       hypotheses='The same two actual matrices and ordinary real logarithm.',
       correspondence='Actual determinant evaluations and the true logarithm power identity establish every displayed determinant and logdet equality.')]

COMPLETE_EXERCISES['la-ex-psd-3'] = [
 claim('For the actualP=diag(4,1) ellipsoid, the changeu=(2x1,x2) makes its constraint the Euclidean unit ball and objective the inner product with(1/2,2), whose true norm issqrt17/2.',
       'CompleteFoundationsDefinitenessModels','ellipsoid_actual_form',
       'ellipsoid_change_of_variables','ellipsoid_coefficient_norm',
       hypotheses='The full real plane and exact source ellipsoid/objective.',
       correspondence='Actual Euclidean norm, actual matrix quadratic form and actual inner product are connected by identities, including a constraint iff.'),
 claim('The linear objective has actual maximumsqrt17/2, attained at(1/(2sqrt17),4/sqrt17); its actual quadratic form and transformed Euclidean norm areboth1.',
       'CompleteFoundationsDefinitenessModels','ellipsoid_margin_upper_bound',
       'ellipsoid_attains','ellipsoid_actual_maximum',
       hypotheses='Every real point in the source ellipsoid; maximum is over its whole image under the source linear objective.',
       correspondence='Cauchy–Schwarz derives the universal bound and an explicit feasible vector attains it. IsGreatest of the actual set image states a genuine maximum.'),
 claim('The two semi-axis lengths are1/2 and1. The actual maximizer is a positive multiple ofP^-1(1,2) and is not a multiple of(1,2).',
       'CompleteFoundationsDefinitenessModels','ellipsoid_semiaxes','ellipsoid_inverse_direction',
       hypotheses='The exact source ellipsoid and nonzero positive sqrt17.',
       correspondence='Exact all-real axis-section iff statements establish the lengths. The actual matrix inverse and actual transformed vector identify the direction, with a proved failure of Euclidean alignment.')]

REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-520'] = [
 claim('Every finite real matrix quadratic formx^TPx equals the stated double sum, and replacingP by(P+P^T)/2 preserves its value for every real vector.',
       'CompleteFoundationsQuadraticForms','real_quadratic_double_sum','real_quadratic_transpose',
       'real_quadratic_only_symmetric_part','symmetric_part_is_symmetric',
       hypotheses='Arbitrary finite index type, real matrixP and real vectorx; no symmetry is presumed for the reduction.',
       correspondence='The actual matrix-vector/dot-product expression is expanded, and its actual transpose and symmetrized matrix values agree for every vector.'),
 claim('For every symmetric two-dimensional real matrix with nonzero first pivota, the exact completed-square expression has second coefficientc-b^2/a.',
       'CompleteFoundationsQuadraticForms','plane_actual_form','plane_completed_square',
       'all_real_symmetric_plane_matrices',
       hypotheses='All symmetric2x2 real matrices; the source positive-pivot hypothesis implies the nonzero pivot required for the identity.',
       correspondence='Every symmetric source matrix is identified with the generic(a,b,c) model; the exact matrix quadratic identity, with its actual division, is proved.'),
 claim('A real symmetric2x2 matrix is positive definite exactly when its first diagonal entry and actual determinant arebothpositive.',
       'CompleteFoundationsQuadraticForms','plane_actual_determinant','plane_pd_criterion',
       'plane_pd_iff_positive_pivot_and_determinant','generic_symmetric_plane_criterion',
       hypotheses='Every real symmetric2x2 matrix, including zero/negative pivots and singular matrices.',
       correspondence='The actual Matrix.PosDef predicate is characterized inbothdirections. Necessity uses actual nonzero vectors, while sufficiency uses the completed square. Actualdet=ac-b^2 gives the printed Schur/pivot criterion.')]

REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-523'] = [
 claim('For a finite real symmetric matrix, actualPSD means a nonnegative quadratic form in every direction, and actualPD means a strictly positive form in every nonzero direction.',
       'CompleteFoundationsQuadraticForms','real_psd_definition','real_pd_definition',
       hypotheses='Arbitrary finite real symmetric matrix; all real coordinate vectors are quantified.',
       correspondence='Actual Matrix.PosSemidef and Matrix.PosDef objects are equivalent to precisely the source quadratic predicates. The strict and nonstrict distinctions remain explicit.'),
 claim('Negative semidefiniteness/definiteness is PSD/PD of-P, equivalently nonpositive/strictly negative values of the original quadratic form.',
       'CompleteFoundationsQuadraticForms','real_negative_semidefinite_definition',
       'real_negative_definite_definition',
       hypotheses='The same arbitrary finite real symmetric matrix.',
       correspondence='Negating the actual matrix negates its actual quadratic values, yielding the stated two negative classifications.'),
 claim('A real symmetric matrix that is neitherPSD nornegativePSD hasbotha positive and a negative quadratic direction, and conversely.',
       'CompleteFoundationsQuadraticForms','real_indefinite_iff_both_signs',
       hypotheses='Arbitrary finite real symmetric matrix; witnesses quantify actual real coordinate vectors.',
       correspondence='The otherwise-indefinite classification is exactly the failure of both semidefinite predicates, characterized by actual opposing-sign witnesses. Nonnegative-definite is source terminology forPSD, not an additional empirical claim.')]

PARTIAL_MATERIAL.setdefault('primer-linalg.html::node-529',[]).append(
 ('For every finite real diagonal matrix, actual positive semidefiniteness is equivalent to nonnegative diagonal entries.',
  refs('CompleteFoundationsQuadraticForms','real_diagonal_psd_iff')))

REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-562'] = [
 claim('For every finite real matrixM and square or rectangularT, the actual congruence quadratic equals the original form atTx. PSD ofM implies PSD ofT^TMT.',
       'CompleteFoundationsCongruence','congruence_quadratic_identity','congruence_psd',
       hypotheses='Arbitrary finite real matrix dimensions, sourceM PSD only for the PSD implication.',
       correspondence='The actual matrix product and matrix-vector quadratic expressions agree for every real vector; the actual Matrix.PosSemidef predicate is preserved without assumingT is square.'),
 claim('WhenM ispositive definite, T^TMT ispositive definite exactly whenT isinjective on coordinate vectors, equivalently when its columns are linearly independent.',
       'CompleteFoundationsCongruence','congruence_pd_iff_injective',
       'congruence_pd_iff_independent_columns','singular_congruence_counterexample',
       hypotheses='Arbitrary finite real dimensions and actualPD ofM; no invertibility assumption is imposed on rectangularT.',
       correspondence='A genuine iff proves the strict condition and its necessity. The exactI2/diag(1,0) example has PSD but singular and non-PD congruence.'),
 claim('For square invertibleT, congruence preserves and reflectsbothPSD andPD.',
       'CompleteFoundationsCongruence','inverse_congruence_identity',
       'invertible_congruence_psd_iff','invertible_congruence_pd_iff',
       hypotheses='Any finite real squareM/T, with actualdetT a unit, which is precisely finite matrix invertibility.',
       correspondence='Congruence by the actual inverse recoversM. Both actual matrix definiteness predicates are proved equivalent, including the reverse directions.'),
 claim('The rectangular columnT=(1,0) withM=diag(1,-1) hasPD congruence1 althoughM hasopposing-sign quadratic directions and isnotPSD.',
       'CompleteFoundationsCongruence','rectangular_congruence_counterexample',
       hypotheses='Exactly the displayed2x1T and2x2M.',
       correspondence='The exact actual rectangular matrix product equalsI1 and isPD; actual forms1/-1 and non-PSD establish that the converse can fail.'),
 claim('The complex version uses conjugate transposeT*: its actual Hermitian quadratic identity andPSD preservation hold, strict definiteness is equivalent to independent columns, and invertible congruence worksbothways forPSD/PD.',
       'CompleteFoundationsCongruence','complex_congruence_quadratic_identity','complex_congruence_psd',
       'complex_congruence_pd_iff_independent_columns','complex_inverse_congruence_identity',
       'complex_invertible_congruence_iff',
       hypotheses='Arbitrary finite complex dimensions; positive-definiteM for the strict column criterion and unitdetT for invertible square equivalences.',
       correspondence='The source complex replacement isencoded using actual conjugate transpose and actual complex Hermitian definiteness predicates; all corresponding implications and equivalences areproved.')]

PARTIAL_MATERIAL.setdefault('primer-linalg.html::node-552',[]).extend([
 ('For every finite real rectangularR, bothR^TR andRR^T areactualPSD matrices.',
  refs('CompleteFoundationsCongruence','real_gram_psd')),
 ('For every finite real rectangularR, actualPD ofR^TR is equivalent to linearly independent columns.',
  refs('CompleteFoundationsCongruence','real_gram_pd_iff_independent_columns'))])

REVIEWED_PARTIAL_MATERIAL = {
 'primer-linalg.html::node-552':dict(
  proved=[
   claim('Every finite real Gram matrixR^TR andRR^T isPSD; its actual quadratic form equals the squared Euclidean norm ofRx, andR^TR isPD exactly for independent columns.',
         'CompleteFoundationsCongruence','real_gram_psd','real_gram_pd_iff_independent_columns',
         hypotheses='Arbitrary finite real rectangularR and every compatible real vectorx.',
         correspondence='Actual Matrix PSD/PD predicates and LinearIndependent columns encode the general statements. GramRegularization.gram_actual_quadratic_norm proves the actual Euclidean norm equality.'),
   claim('For epsilon>0, epsilonI+R^TR has actual formepsilon||x||²+||Rx||², isPD and invertible, and its actualL1 image ofxi-xiStar has positive norm wheneverxi≠xiStar.',
         'CompleteFoundationsGramRegularization','regularized_gram_exact_quadratic',
         'regularized_gram_strict_quad_and_invertible','actual_regularized_l1_certificate',
         hypotheses='Arbitrary finite realR, strictly positiveepsilon, and distinct real coordinate states for theL1 conclusion.',
         correspondence='The actual matrix expression, actual Euclidean squared norms, actual IsUnit matrix and actual PiLp1 norm are linked. Injectivity of the actual matrix map proves the nonzero image certificate.'),
   claim('For everyPSDK andlambda>0, K+lambdaI isPD and invertible.',
         'CompleteFoundationsGramRegularization','positive_regularization_pd','positive_regularization_is_invertible',
         hypotheses='Arbitrary finite real squareK with its actual Matrix.PosSemidef object and positivelambda.',
         correspondence='The actual ridge matrix has an actualPD certificate and an actual IsUnit witness; the separate positive-diagonal Cholesky construction is explicitly mapped below.'),
   claim('The actual outer productaa^T isPSD and has rank1 fornonzeroa and rank0 fora0. Its quadratic form is(a^Tv)^2, its action ona has eigenvalue||a||², and it vanishes on every direction orthogonal toa.',
         'CompleteFoundationsGramRegularization','outer_psd','outer_zero','outer_actual_rank',
         'outer_actual_quadratic','outer_eigen_direction','outer_orthogonal_directions',
         hypotheses='Arbitrary finite real coordinate vectors; nonzeroa only for the rank1 assertion.',
         correspondence='Actual Matrix.rank is bounded above by1 and below by a genuine nonzero1x1 minor. Actual matrix-vector actions and actual Euclidean norm give the source eigen-directions and form.'),
   claim('Forbeta>=0, betaaa^T isPSD and adding it changes every actual quadratic value bybeta(a^Tv)^2, so the value cannot decrease.',
         'CompleteFoundationsGramRegularization','outer_psd_increase',
         hypotheses='Arbitrary finite realM/a, any nonnegativebeta and every real vectorv; no convergence-speed conclusion is inferred.',
         correspondence='The exact actual matrix increment has aPSD certificate and a quantified exact quadratic increase. The parenthetical performance distinction asserts no further mathematical guarantee.')],
  pending=[])
}
REVIEWED_PARTIAL_MATERIAL['primer-linalg.html::node-552']['proved'].append(
 claim('Every finite real positive-definite regularized kernel matrix has an exact lower triangular Cholesky factor with strictly positive diagonal; every leading principal minor is positive.',
       'CompleteModulesCholesky','actual_positive_definite_matrix_has_cholesky',
       'actual_cholesky_existence_iff_positive_definite','actual_exact_cholesky_failure_iff_not_positive_definite',
       'actual_positive_definite_leading_principal_minors_are_positive',
       hypotheses='Arbitrary finite square real positive-definite matrices; the preceding ridge theorem supplies this premise for K PSD and lambda>0.',
       correspondence='An actual Gram–Schmidt construction proves the factor, its product identity, and every positive diagonal entry. Failure means absence of an exact positive-diagonal factor, which is impossible here. This substantiates the exact-arithmetic mathematical claim; no floating-point implementation or algorithm execution trace is inferred.'))
REVIEWED_PARTIAL_MATERIAL['primer-linalg.html::node-552']['proved'][0]['lean_declarations'] += refs(
 'CompleteFoundationsGramRegularization','gram_actual_quadratic_norm')

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

COMPLETE_EXERCISES['la-ex-svd-1'] = [
 claim('The stated U, Sigma and V give an actual SVD of diag(2,-1); both orthogonality products equal the identity and the factor product equals A.',
       'CompleteFoundationsSVDModels','sourceA','signU','stretchSigma','rightV','actual_svd_product','actual_svd_orthogonal',
       hypotheses='Exactly the source real two-by-two matrix and displayed factors.',
       correspondence='Actual Matrix multiplication and transpose establish the decomposition, with strictly positive diagonal entries 2 and1 in Sigma.'),
 claim('The actual Gram matrix is diag(4,1); the nonnegative square roots of all its eigenvalues are exactly2 and1. The signed eigenvalues of A are exactly2 and-1.',
       'CompleteFoundationsSVDModels','actual_gram_matrix','diagonal_all_eigenvalues','isSingularValue','actual_singular_values','actual_signed_eigenvalues',
       hypotheses='Eigenvalues mean actual nonzero Euclidean eigenvectors; singular values mean nonnegative sigma with sigma squared an eigenvalue of the actual Gram matrix.',
       correspondence='Universal iff statements prove all-and-only eigenvalues and singular values; the positive stretches are distinguished from the actual signed invariant directions.'),
 claim('The actual spectral norm is2, actual Frobenius norm sqrt5, and actual inverse-based spectral condition number and largest-to-smallest singular-value ratio are both2.',
       'CompleteFoundationsSVDModels','actual_spectral_norm','actual_frobenius_norm','actual_inverse','actual_condition_number',
       hypotheses='The separately scoped actual L2 operator and Frobenius matrix norms; this A is invertible.',
       correspondence='A checked inverse product gives the actual inverse before its induced norm is evaluated. The norms are the standard objects, not unproved proposed scalar formulas.'),
 claim('The entire unit circle image is exactly the ellipse y1 squared over4 plus y2 squared equals1; the coordinate axes stretch by2 and1, and the second coordinate is reflected.',
       'CompleteFoundationsSVDModels','actual_coordinate_action','actual_unit_circle_image','actual_axis_stretches',
       hypotheses='All real Euclidean vectors of norm1, not a sampled circle.',
       correspondence='Actual set-image equality proves both inclusion directions and all ellipse points; actual coordinate actions and norms verify both semi-axis lengths and reflection.')]

COMPLETE_EXERCISES['la-ex-svd-2'] = [
 claim('The actual row Gram product is5; the actual pseudoinverse is column(1/5,2/5), satisfying all four Moore–Penrose identities and uniquely satisfying them. Applied to b5 it gives xStar(1,2), which solves the equation.',
       'CompleteFoundationsPseudoinverse','sourceA','sourcePlus','target','moorePenrose','actual_moore_penrose_identities','actual_moore_penrose_unique','actual_row_gram','actual_row_pseudoinverse_formula','actual_solution_from_pseudoinverse','actual_unique_minimum_norm',
       hypotheses='Exactly the real one-by-two source matrix and target5; uniqueness ranges over every candidate two-by-one matrix.',
       correspondence='Actual rectangular products and symmetry identities identify the Moore–Penrose inverse, rather than assigning the label to a computed vector without checking its definition.'),
 claim('For every nonzero finite real row a, its Moore–Penrose inverse is a transpose divided by the positive row squared length; the row Gram product is that squared length times the one-by-one identity.',
       'CompleteFoundationsPseudoinverse','rowMatrix','rowPlus','nonzero_row_squared_length_positive','actual_nonzero_row_right_inverse','actual_nonzero_row_pseudoinverse','actual_general_row_formula',
       hypotheses='An arbitrary finite real row, required to be nonzero for positive denominator and the four inverse identities.',
       correspondence='This also covers the generic formula in the hint. The actual Gram product is computed and the denominator is proved positive before showing all Moore–Penrose identities.'),
 claim('All and only source solutions are xStar+t*(-2,1); this nonzero null direction is orthogonal to xStar, both squared lengths are5, and the actual solution squared norm is5+5t squared.',
       'CompleteFoundationsPseudoinverse','actual_equation_iff','actual_null_direction','solution_coordinates','actual_all_solutions','actual_orthogonality','actual_squared_norms',
       hypotheses='All real solution vectors and all real parameters, without nonnegativity restrictions.',
       correspondence='A universal parameterization iff gives every solution and checks the nullspace action. Actual Euclidean inner product and squared norm give the precise Pythagorean calculation.'),
 claim('The vector(1,2) is the unique minimum Euclidean norm solution, although the full solution set is infinite.',
       'CompleteFoundationsPseudoinverse','actual_unique_minimum_norm','actual_parameter_injective','actual_infinitely_many_solutions',
       hypotheses='The entire actual source equation solution set.',
       correspondence='The norm comparison has equality iff x=xStar. Injectivity of the real parameterization proves actual Set.Infinite, so the infinitude assertion is also encoded.')]

COMPLETE_EXERCISES['la-ex-svd-3'] = [
 claim('The actual initial vector is unit, its matrix image is(3,1)/sqrt2, and its estimate is sqrt5, rounded2.2361; the actual Gram matrix is diag(9,1).',
       'CompleteFoundationsPowerNormalization','actual_x_zero_unit','actual_initial_action','actual_initial_estimate','actual_source_gram','actual_printed_decimal_enclosures',
       hypotheses='The exact source diag(3,1) and normalized initial vector.',
       correspondence='Actual induced matrix action and actual Euclidean norm are evaluated. The printed approximation has a rigorous half-last-place rational enclosure.'),
 claim('The actual normalized Gram power step gives(9,1)/sqrt82, which is unit; its matrix image is(27,1)/sqrt82 and actual estimate is sqrt(730/82), rounded2.9837. The estimate increases strictly but remains below the true spectral norm3.',
       'CompleteFoundationsPowerNormalization','powerStep','actual_gram_action','actual_gram_action_norm','actual_power_iterate','actual_x_one_unit','actual_next_action','actual_next_estimate','actual_improvement_below_true_norm','actual_source_spectral_norm','actual_printed_decimal_enclosures',
       hypotheses='The true normalized iteration, with its actual nonzero Gram-image norm.',
       correspondence='The normalization denominator is evaluated before the iterate is identified. Actual norms prove the claimed improvement and remaining strict gap; a rational enclosure verifies the approximation.'),
 claim('The actual spectral norm after division by the initial estimate is3/sqrt5, rounded1.3416 and strictly above1, so it fails the proposed certificate.',
       'CompleteFoundationsPowerNormalization','actual_failed_normalization','actual_printed_decimal_enclosures',
       hypotheses='Exactly the matrix and initial positive estimate.',
       correspondence='Actual matrix scaling and its true operator norm establish the violating value; no candidate scalar bound is substituted for the norm.'),
 claim('Dividing by3 gives actual norm1, and dividing by the actual Frobenius norm sqrt10 gives norm at most1. Every unit-direction estimate is a lower bound, whereas the spectral norm of every finite real matrix is bounded above by its actual Frobenius norm; any positive upper bound safely normalizes.',
       'CompleteFoundationsPowerNormalization','actual_guaranteed_normalizations','actual_source_frobenius','actual_matrix_action_squared_bound','actual_spectral_le_frobenius','actual_frobenius_length_is_norm','actual_unit_direction_estimate_is_lower_bound','actual_upper_bound_normalizes',
       hypotheses='Arbitrary finite rectangular real matrices for the general bound, every unit direction, and a positive divisor for guaranteed normalization.',
       correspondence='Finite Cauchy–Schwarz bounds the actual map on every Euclidean vector, giving the actual operator norm bound. The scoped Frobenius identity identifies the standard norm and the explicit counterexample proves a power estimate alone cannot certify normalization.')]

# These newly retained excerpts have been read individually; their classification
# is explicit instead of inherited from containment in a completed exercise.
for node in [780,798,816]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-linalg.html::node-{node}'] = (
   'The exact paragraph is only a link labelled Review: Singular values, least squares and power iteration. It directs reading and makes no mathematical assertion.')
REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-784'] = [
 claim('The sign can be placed in an orthogonal factor; singular values are nonnegative stretches, while the source negative eigenvalue reflects its direction.',
       'CompleteFoundationsSVDModels','actual_svd_orthogonal','actual_svd_product','isSingularValue','actual_singular_values','actual_signed_eigenvalues','actual_axis_stretches',
       hypotheses='The hint is interpreted in the exact exercise context diag(2,-1); the nonnegativity requirement is explicit for arbitrary matrices in isSingularValue.',
       correspondence='Actual orthogonality and factor product put the negative sign in U. The singular-value definition requires nonnegativity, and actual axis lengths prove the two source unsigned stretches.')]

COMPLETE_EXERCISES['la-ex-blocks-1'] = [
 claim('The actual three-by-three source matrix sends(1,2,3) to(4,7,12), has trace9 and determinant20, and its all-vector action has no coupling between the first two coordinates and the third.',
       'CompleteFoundationsBlockModels','blockM','actual_independent_block_action','actual_block_source_values',
       hypotheses='The exact stated matrix; the independence statement holds for every real input vector.',
       correspondence='Actual matrix-vector multiplication, actual trace and actual determinant are evaluated, including the universal coordinate action behind the no-coupling explanation.'),
 claim('The matrix is precisely a block diagonal matrix after the canonical index equivalence. The first block determinant is5 and scalar block determinant4; block determinants multiply and block traces add.',
       'CompleteFoundationsBlockModels','actual_block_representation','actual_determinant_from_blocks','generic_block_diagonal_determinant','generic_block_diagonal_trace',
       hypotheses='Exact source blocks for their values; arbitrary finite square real blocks for the two general identities.',
       correspondence='Actual equality after Fin2+Fin1 toFin3 reindexing and determinant invariance connect the source matrix to the general block determinant theorem. Trace additivity is also proved generically.')]
COMPLETE_EXERCISES['la-ex-blocks-2'] = [
 claim('For every reala and vectorz the actual Schur matrix quadratic form equals(a-4/3)x squared+3(y+2x/3) squared. It isPSD iff a>=4/3 andPD iff a>4/3.',
       'CompleteFoundationsBlockModels','schurMatrix','actual_schur_completed_square','actual_schur_symmetry','actual_schur_psd_iff','actual_schur_pd_iff',
       hypotheses='All real parameter and vector values, including the boundary.',
       correspondence='The exact completed-square identity leads to actual Matrix.PosSemidef and PosDef iff statements, with both necessity and sufficiency.'),
 claim('At a4/3 the nonzero vector(3,-2) is in the actual nullspace and determinant is0, while the matrix isPSD. For every a<4/3 the same vector has a negative form.',
       'CompleteFoundationsBlockModels','actual_schur_boundary','actual_schur_negative_direction',
       hypotheses='Exactly the boundary or strict lower parameter range.',
       correspondence='Actual matrix-vector zero, nonzero witness and zero determinant establish singularity, and the quantified strict negative value verifies failure below the boundary.')]
COMPLETE_EXERCISES['la-ex-blocks-3'] = [
 claim('The actual base inverse isdiag(1/2,1), its action onu(1,2) givesv(1/2,2), and u dotv=9/2. The actual updated matrix is[[3,2],[2,5]] and its determinant equals detV*(1+u dotv)=11.',
       'CompleteFoundationsBlockModels','actual_update_base_inverse','actual_shared_update_quantities','actual_rank_one_update_matrix','actual_update_determinant',
       hypotheses='Exactly the stipulated base matrix and real update vector.',
       correspondence='The actual nonsingular inverse is established by a product check before the shared quadratic scalar and actual rank-one updated determinant are evaluated.'),
 claim('The actual inverse candidate is V inverse minusvv transpose divided by1+u dotv, equal to1/11*[[5,-2],[-2,3]]. Both actual multiplication orders equalI, so it is the actual updated inverse.',
       'CompleteFoundationsBlockModels','inverseCandidate','actual_rank_one_inverse_formula','actual_independent_inverse_check',
       hypotheses='The source update has the checked positive denominator11/2.',
       correspondence='The displayed inverse-update expression is identified with the actual candidate matrix; independent products establish the inverse itself in both orders.'),
 claim('The actual log-determinant increase islog(11/2), rounded1.70475 within0.000005.',
       'CompleteFoundationsBlockModels','actual_log_determinant_increase','actual_log_determinant_decimal',
       hypotheses='The actual positive determinants2 and11.',
       correspondence='The exact log quotient identity is applied only to nonzero positive determinants. A finite real logarithm series bound and certified log2 enclosure prove the half-last-place decimal bound.')]
for node in [924,942,960]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-linalg.html::node-{node}'] = (
   'The exact paragraph is a reading link labelled Review: Block algebra, Schur complements and updates, with no mathematical assertion.')

COMPLETE_EXERCISES['la-ex-svd-2'][2]['lean_declarations'] += refs(
 'CompleteFoundationsUniversalMatrices','actual_equal_images_iff_null_difference')
COMPLETE_EXERCISES['la-ex-blocks-3'][0]['lean_declarations'] += refs(
 'CompleteFoundationsUniversalMatrices','actual_matrix_determinant_lemma')

COMPLETE_EXERCISES['la-ex-structured-1'] = [
 claim('The actual Q=diag(1,-1) equals its transpose, its transpose product equalsI, determinant is-1, and its action is(x1,-x2). It preserves every Euclidean norm.',
       'CompleteFoundationsStructuredModels','actual_reflection_orthogonal','actual_reflection_action','actual_reflection_preserves_every_norm',
       hypotheses='The exact real source matrix, with every real input vector.',
       correspondence='Actual orthogonality, determinant and all-vector action establish reflection across the horizontal axis, with unsigned lengths preserved.'),
 claim('The actual image of(3,4) is(3,-4) and both Euclidean lengths equal5.',
       'CompleteFoundationsStructuredModels','actual_reflection_source_values',
       hypotheses='Exactly the source vector.',
       correspondence='Actual CLM matrix image and actual Euclidean norms are checked, including equality with the original length.'),
 claim('Every finite real orthogonal matrix preserves every Euclidean norm and is invertible.',
       'CompleteFoundationsUniversalMatrices','actual_orthogonal_matrix_preserves_norm','actual_orthogonal_matrix_is_invertible',
       hypotheses='Any finite real squareQ with actualQ transpose timesQ=I.',
       correspondence='The actual squared-norm identity follows from matrix multiplication and transpose, and the actual determinant product forces invertibility.')]
COMPLETE_EXERCISES['la-ex-structured-2'] = [
 claim('The actual P=diag(1,0) is symmetric and idempotent, maps eachx to(x1,0), and has image exactly the horizontal axis. Its residual is perpendicular to the image and the Euclidean squared norm obeys Pythagoras.',
       'CompleteFoundationsStructuredModels','actual_projection_properties','actual_projection_action','actual_projection_image','actual_projection_residual',
       hypotheses='The actual source matrix and every real Euclidean vector.',
       correspondence='Actual transpose and product identities, image set equality, inner product and squared norms establish the orthogonal projection property, rather than using the label alone.'),
 claim('The source projection is the unique closest horizontal-axis point to everyx. For(3,4), the projected point is(3,0), residual(0,4), lengths3 and4, and full length5.',
       'CompleteFoundationsStructuredModels','actual_projection_is_unique_closest','actual_projection_source_values',
       hypotheses='Every real horizontal-axis comparison point for nearest-point uniqueness; the exact source vector for numerical values.',
       correspondence='Actual Euclidean distance comparison and equality iff provide nearest-point uniqueness. Actual norm calculations verify the source right triangle.'),
 claim('P transpose timesP equalsP, which is notI; determinant0 makesP singular, while its actual operator norm is1. It removes the vertical coordinate rather than preserving every length; every orthogonal matrix preserves all lengths and is invertible.',
       'CompleteFoundationsStructuredModels','actual_projection_properties','actual_projection_action','actual_projection_source_values',
       hypotheses='The actual source matrix, with the standard induced Euclidean operator norm.',
       correspondence='The false orthogonality identity, zero determinant, actual norm1 and all-vector coordinate action prove the distinction. Generic orthogonal norm preservation and invertibility are explicitly linked below.')]
COMPLETE_EXERCISES['la-ex-structured-2'][2]['lean_declarations'] += refs(
 'CompleteFoundationsUniversalMatrices','actual_orthogonal_matrix_preserves_norm','actual_orthogonal_matrix_is_invertible')
COMPLETE_EXERCISES['la-ex-structured-3'] = [
 claim('For the exact quarter-turn skew matrix, actual(I+A) inverse ishalf*[[1,1],[-1,1]], the actual Cayley matrix is[[0,1],[-1,0]], its transpose product isI and determinant1. Its action(x1,x2) maps to(x2,-x1).',
       'CompleteFoundationsStructuredModels','quarterSkew','cayley','actual_quarter_inverse','actual_quarter_cayley','actual_clockwise_quarter_action',
       hypotheses='Exactly the source two-by-two real skew matrix.',
       correspondence='A checked product gives the actual inverse before the Cayley product is evaluated. Actual orthogonality, determinant and coordinate action establish the clockwise quarter-turn.'),
 claim('For every finite real skew-symmetricA, I+A is invertible, the actual Cayley transform is orthogonal, and Qv=-v forcesv=0.',
       'CompleteFoundationsStructuredModels','actual_skew_one_add_is_invertible','actual_cayley_is_orthogonal','actual_cayley_no_negative_one_eigenvector',
       hypotheses='Arbitrary finite real square matrices with actual transposeA=-A; every real vectorv.',
       correspondence='The quadratic skew term is0, making the actual(I+A) map injective and hence invertible. The actual inverse-based transform is orthogonal, and the exactw=(I+A) inversev equation forcesw andv to0.'),
 claim('Negative identity is orthogonal but cannot be the Cayley transform of a finite skew-symmetric matrix in a nonzero dimension.',
       'CompleteFoundationsStructuredModels','actual_negative_identity_is_orthogonal','actual_negative_identity_is_excluded',
       hypotheses='Nonempty finite coordinate type for the excluded negative-identity statement; orthogonality holds even in zero dimension.',
       correspondence='An actual nonzero single-coordinate vector of negative identity would contradict the no-negative-one-eigenvector theorem, showing precisely the parameterization restriction.')]
for node in [1035,1053,1071]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-linalg.html::node-{node}'] = (
   'The exact paragraph is a reading link labelled Review: Orthogonal maps, projections and Cayley transforms; it adds no mathematical assertion.')

for node in [876,878]:
 REVIEWED_PARTIAL_MATERIAL[f'primer-linalg.html::node-{node}'] = dict(
  proved=[
   claim('The actual rectangular determinant identity det(I+AB)=det(I+BA) holds for all finite real dimensions.',
         'CompleteFoundationsUniversalMatrices','actual_sylvester_determinant_identity',
         hypotheses='Arbitrary compatible finite rectangular real matrices.',
         correspondence='The actual matrices and their actual determinants have the universal equality; neither product is assumed square in the same dimension.'),
   claim('For any invertible realV, the actual rank-one determinant isdet(V+uv transpose)=detV*(1+v transposeV inverseu).',
         'CompleteFoundationsUniversalMatrices','actual_matrix_determinant_lemma',
         hypotheses='Arbitrary finite real squareV with unit determinant and arbitrary update vectors.',
         correspondence='The finite rectangular determinant lemma is specialized to actual one-column/one-row products and the actual one-by-one determinant. The outer-product and dot-product formulas are proved equal.')],
  pending=['The compatible rectangular productsAB andBA share all nonzero eigenvalues, with the exact eigenvalue multiplicity interpretation still requiring a full correspondence.'])

REVIEWED_PARTIAL_MATERIAL['primer-linalg.html::node-755'] = dict(
 proved=[
  claim('Every unit-direction estimate is a lower bound on the actual Euclidean operator norm; the actual Frobenius norm is a guaranteed upper bound and division by any positive upper bound safely normalizes.',
        'CompleteFoundationsPowerNormalization','actual_unit_direction_estimate_is_lower_bound','actual_spectral_le_frobenius','actual_frobenius_length_is_norm','actual_upper_bound_normalizes',
        hypotheses='Every finite rectangular real matrix and every real Euclidean unit vector; a positive divisor is required for normalization.',
        correspondence='Actual map bounds and actual induced norm establish the direction of each inequality. The standard Frobenius norm is explicitly identified.'),
  claim('A power estimate can fail to certify norm at most1 after normalization.',
        'CompleteFoundationsPowerNormalization','actual_failed_normalization',
        hypotheses='The actual diag(3,1) model and its initial unit vector.',
        correspondence='The actual scaled matrix has norm3/sqrt5>1, supplying a genuine counterexample to the unconditional estimate certificate.'),
  claim('A nonzero initial projection onto the dominant subspace is necessary for the repeated-top convergence assertion: diag(3,3,1) from the third unit vector remains there with estimate1 at every time despite top norm3.',
        'CompleteFoundationsPowerDegeneracy','actual_repeated_top_directions','actual_repeated_spectral_norm','actual_initial_dominant_projection_zero','actual_all_iterates_and_estimates','actual_estimates_do_not_reach_top',
        hypotheses='The explicit finite real counterexample, with the actual normalized Gram iteration and a unit start.',
        correspondence='Two independent top stretch directions and exact norm3 witness repetition. The start is orthogonal to both, every true iterate and estimate is evaluated, and actual filter convergence to3 is disproved. This justifies the corrected hypothesis; it does not prove the corrected positive convergence theorem.')],
 pending=[
  'General normalized Gram power convergence and its angle-rate bound under a simple largest singular value and nonzero dominant projection, with exact hypotheses and all-time dynamics.',
  'General convergence to the dominant right-singular subspace, including repeated largest positive singular values, under the corrected nonzero initial dominant projection; the actual estimate limit also requires proof.',
  'The exact breakdown iffAx=0, all-after-first range and nullspace-orthogonal invariants, exclusion of later breakdown, and the probabilistic random-start qualifier.',
  'Every displayed walkthrough iterate/estimate2.236,2.765,2.824,2.8282 and actual limit2sqrt2 for the walkthrough matrix from(1,0).',
  'The generic spectral bound sqrt(L1 operator norm timesL-infinity operator norm) and the actual walkthrough sqrt12 and rounded3.46.'])

# Actual Hilbert-space/RKHS models reviewed after checkpoint8 was frozen.
COMPLETE_EXERCISES['la-ex-functions-1'] = [
 claim('In the actual real L2([0,1]) space, constant1 and identityx are square-integrable and represented by genuine Lp classes; their inner product is1/2 and squared norms1 and1/3, with norms1 and1/sqrt3.',
       'CompleteFoundationsL2Models','constant_mem_l2','linear_mem_l2','actual_classes_have_source_representatives','actual_l2_inner_is_interval_integral','actual_source_inner_products','actual_source_squared_norms','actual_source_norms',
       hypotheses='Lebesgue measure restricted to the exact closed unit interval; actual equivalence classes modulo almost-everywhere equality.',
       correspondence='The actual L2 inner product is proved equal to the source interval integral using the source representatives almost everywhere; the Hilbert norms follow from its actual inner product.'),
 claim('For every realc, the actual L2 inner product of1 withx-c equals1/2-c and vanishes iff c=1/2. The actual residual is perpendicular with squared norm1/12, and the actual Hilbert norms obey the displayed Pythagorean identity.',
       'CompleteFoundationsL2Models','actual_projection_characterization','actual_residual_orthogonality_and_norm',
       hypotheses='The actual classes and every real scalarc.',
       correspondence='Actual Hilbert subtraction, scalar multiplication and inner products encode the projection; the existing raw interval integrals explicitly verify every printed integral.')]
COMPLETE_EXERCISES['la-ex-functions-1'][1]['lean_declarations'] += refs(
 'CompleteFoundationsFunctionExamples','projection_integrals','projection_norms','constant_projection_characterization')

COMPLETE_EXERCISES['la-ex-functions-2'] = [
 claim('The actual Euclidean feature vectors(1,x) have inner product1+xy. At samples0,1 their actual Gram matrix is[[1,1],[1,2]]. Every weighted feature sum is(alpha1+alpha2,alpha2), whose actual squared norm equals both the displayed sum of squares andalpha transposeKalpha.',
       'CompleteFoundationsAffineRKHS','actual_feature_inner','actual_sample_gram','actual_feature_sum','actual_gram_sum_of_squares',
       hypotheses='All real inputs and real coefficient pairs; actual Euclidean inner product and norm.',
       correspondence='The matrix is the actual Matrix.gram of the actual feature family. The feature vector, its actual norm and the actual matrix quadratic are identified, rather than relying only on scalar arithmetic.'),
 claim('The actual sample Gram matrix is PSD and PD, has determinant1, and the actual two sample features are linearly independent.',
       'CompleteFoundationsAffineRKHS','actual_sample_gram_positive',
       hypotheses='The exact sample inputs0 and1.',
       correspondence='Actual Matrix.PosSemidef, PosDef and LinearIndependent objects establish all source strictness and independence conclusions. The actual Gram quadratic is the sum of squares for every coefficient pair.')]

COMPLETE_EXERCISES['la-ex-functions-3'] = [
 claim('A genuine RKHS over all real inputs has kernel1+xy, actual evaluationw1+w2x, actual kernel sections(1,x), and the reproducing identity. Its unique interpolant satisfyingf(0)=1 andf(1)=3 is coefficient vector(1,2), givingf(x)=1+2x and actual squared RKHS norm5.',
       'CompleteFoundationsAffineRKHS','affineRKHS','actual_rkhs_evaluation','actual_rkhs_kernel','actual_kernel_section','actual_reproducing_identity','actual_interpolation_unique','actual_fitted_function','actual_fitted_rkhs_squared_norm',
       hypotheses='The exact scalar kernel over the whole real domain; the RKHS is the actual complete Euclidean coefficient space with an injective pointwise-continuous evaluation map.',
       correspondence='An actual RKHS class instance identifies the kernel and Hilbert norm. The interpolation iff proves uniqueness among every member of this RKHS, rather than merely among unexplained affine functions.'),
 claim('The actual Gram inverse is[[2,-1],[-1,1]], its product with(1,3) is(-1,2), andy transposeK inversey equals5. The fitted RKHS vector is the actual kernel-section combination-k(0,.)+2k(1,.), so the matrix and feature calculations give the same squared Hilbert norm.',
       'CompleteFoundationsAffineRKHS','actual_sample_gram','actual_fitted_kernel_representer','actual_fitted_representer','actual_fitted_rkhs_squared_norm',
       hypotheses='The exact sample vector and actual Gram matrix.',
       correspondence='The representer identity holds in the actual Hilbert space and uses actual RKHS.kerFun sections; the actual matrix inverse and all displayed products are linked explicitly below.'),
 claim('Actual reproducing Cauchy-Schwarz gives|f(x)|≤||f||sqrt(1+x²). The finite-norm fitted function and kernel diagonal are unbounded on the whole real line; on[-1,1] the fitted function has the valid uniform boundsqrt10.',
       'CompleteFoundationsAffineRKHS','actual_reproducing_cauchy_schwarz','actual_feature_norm','actual_domain_conclusions','actual_fitted_rkhs_squared_norm',
       hypotheses='Every real input for the pointwise bound; the exact closed interval only for the uniform bound.',
       correspondence='The bound comes from the actual reproducing inner product. Explicit all-real nonexistence of finite bounds proves the domain caveat, including the independently unbounded diagonal.')]
COMPLETE_EXERCISES['la-ex-functions-3'][1]['lean_declarations'] += refs(
 'CompleteFoundationsFunctionExamples','affine_gram_inverse','affine_interpolation_norm','affine_representer')

for node in [1153,1172,1190]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-linalg.html::node-{node}'] = (
   'This exact paragraph is only the labelled Review link to the function-space section; it adds no mathematical assertion.')
REVIEWED_NONFORMAL_MATERIAL['primer-linalg.html::node-1148'] = (
 'The paragraph gives practice-order and review-link advice only; it asserts no mathematical theorem or model property.')

for node in [1152,1157,1161]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = [COMPLETE_EXERCISES['la-ex-functions-1'][0]]
for node in [1164,1166]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = [COMPLETE_EXERCISES['la-ex-functions-1'][1]]
for node in [1171,1176,1180,1182]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = [COMPLETE_EXERCISES['la-ex-functions-2'][0]]
REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-1184'] = [COMPLETE_EXERCISES['la-ex-functions-2'][1],
 claim('Every Gram matrix of real Hilbert feature vectors is PSD, and its quadratic form is the actual squared norm of their weighted sum.',
       'CompleteFoundationsFeatures','feature_gram_psd','feature_norm_quadratic','feature_null_quadratic_iff',
       hypotheses='Any finite real Hilbert feature family.',
       correspondence='The general feature-inner-product explanation is supported by actual Gram positivity and the actual Hilbert weighted-sum norm, beyond the two-sample numeric model.')]
for node in [1189,1194,1198]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = [COMPLETE_EXERCISES['la-ex-functions-3'][0]]
for node in [1200,1202]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = [COMPLETE_EXERCISES['la-ex-functions-3'][1]]
REVIEWED_COMPLETE_MATERIAL['primer-linalg.html::node-1204'] = [COMPLETE_EXERCISES['la-ex-functions-3'][2]]

for node in [599,601]:
 REVIEWED_PARTIAL_MATERIAL[f'primer-linalg.html::node-{node}'] = dict(
  proved=[
   claim('Every finite real PD matrix has a unique lower-triangular factor with positive diagonal andP=LL transpose.',
         'CompleteFoundationsCholeskyRecursion','actual_cholesky_factor_exists_uniquely','actual_positive_triangular_factor_unique',
         hypotheses='Arbitrary finite real squareP that is genuinely Matrix.PosDef.',
         correspondence='Actual generic existence is reused from ModulesCholesky, and strong induction over each finite column proves uniqueness of the actual matrix factor.'),
   claim('The actual Cholesky diagonal equals the positive square root ofPjj minus the sum of prior squared entries, and each lower off-diagonal entry is(Pij minus the prior product sum)/Ljj. For a symmetricP, existence of exactly this positive-pivot recursion is equivalent to actualPD.',
         'CompleteFoundationsCholeskyRecursion','priorProduct','pivotArgument','positiveRecursion','actual_diagonal_recursion','actual_off_diagonal_recursion','actual_factor_gives_positive_recursion','actual_positive_recursion_gives_factor','actual_positive_recursion_iff_positive_definite',
         hypotheses='Any finite real symmetricP; a candidate lower factor obeys the actual source recurrence, with strict positive pivots and positive square-root choices.',
         correspondence='The prior sums run over exactlyk<j. Both directions prove equivalence between the actual source recursion and the genuine positive-diagonal triangular factor, including strict positivity of every source square-root argument.')],
  pending=['The computational operation-count model and leading approximate costn³/3 for the stated Cholesky recursion. A mathematical factor-existence or scalar polynomial identity alone is not a complexity proof.'])

COMPLETE_EXERCISES['primer-optimization.html::exercise-33'] = [
 claim('For the actual Euclidean quadratic1/2(x1²+10x2²), the genuine Frechet gradient isdiag(1,10)x and its actual derivative is that Hessian. Actual gradient updates equal the source coordinate recurrences, with the exact source factors at steps0.1,0.21 and2/11; Hessian operator norm10, inverse norm1, and condition number10 are identified.',
       'CompleteFoundationsConditionedQuadratic','objective','actual_frechet_derivative','actual_gradient','gradient_identification','actual_hessian_derivative','actual_hessian_coordinates','actual_gradient_step','actual_source_trajectory','actual_source_step_factors','actual_source_condition_number','actual_source_curvature_bounds',
       hypotheses='The exact real Euclidean source model; general parameter theorems retain their explicit positivity or nonzero conditions.',
       correspondence='The source algorithm acts on the actual gradient, and the actual functional iterates are identified with the prior coordinate trajectory. Both matrix and analytic curvature/condition statements are encoded.'),
 claim('From(10,1), step0.1 has objective50*(.81)^k after the first step and first meets1e-6 exactly atk85; step2/11 has objective55*(81/121)^k and first meets it exactly atk45. The exact logarithmic threshold equivalences hold, with genuine rounding enclosures84.1 and44.4. Step0.21 multiplies the second-coordinate magnitude by1.1 each time and that magnitude diverges.',
       'CompleteFoundationsConditionedQuadratic','actual_source_objective','actual_source_iteration_budgets','source_logarithmic_thresholds','actual_slow_log_threshold_decimal','actual_balanced_log_threshold_decimal','actual_unstable_ten_percent','actual_source_trajectory',
       hypotheses='Every natural iteration index, withk≥1 explicitly required for the first objective/log formula; exact start and source steps.',
       correspondence='Universal integer iff gives the genuine minimal budgets including index-zero handling. Logarithm series with rigorous remainders certify the printed approximations, and the exact actual-coordinate recurrence supports the10% statement and divergence.'),
 claim('For any finite real symmetric quadratic Hessian with actual positive minimum eigenvalueμ and maximumL, eta2/(L+μ) uniquely minimizes the actual gradient update operator norm to(L-μ)/(L+μ); this yields factors9/11 and optimal step2/11 in the source model. The genuine Newton linear equation has unique correction-x for every nonzero diagonal curvature, giving source gradient(10,10), correction(-10,-1), and a zero point after one full step independently of the condition ratio.',
       'CompleteFoundationsConditionedQuadratic','generic_best_constant_step','generic_interval_factor_bound','generic_actual_diagonal_update_norm','generic_quadratic_optimal_step','actual_symmetric_quadratic_optimal_step','actual_diagonal_update_norm','actual_newton_correction','actual_newton_step_solves','actual_source_newton_data',
       hypotheses='The actual symmetric matrix eigenvalues lie in[μ,L] and attain both positive endpoints; the Newton conclusion requires both diagonal curvatures nonzero, as true for the stated strictly convex source.',
       correspondence='Genuine unitary spectral diagonalization bridges the generic symmetric matrix update to its actual diagonal operator norm; optimality is an iff for every real candidate step. Actual gradient/Hessian objects and the actual matrix solve establish the full Newton statement.')]
COMPLETE_EXERCISES['primer-optimization.html::exercise-33'][1]['lean_declarations'] += refs(
 'CompleteFoundationsAlgorithms','slow_coordinate_objective','balanced_step_objective','diagonal_iteration','unstable_diagonal_coordinate')
for node in [1697,1701]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['primer-optimization.html::exercise-33']

# Every clause of these theorem bodies is now supported, including an actual
# arithmetic-expression/loop cost model rather than a standalone cubic number.
for node in [599,601]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-linalg.html::node-{node}'] = (
  REVIEWED_PARTIAL_MATERIAL[f'primer-linalg.html::node-{node}']['proved'] + [
   claim('In the exact-arithmetic source recurrence, each lower entry at columnj evaluatesj multiply/subtract pairs followed by one square root or division, for2j+1 arithmetic operations. Evaluating each lower entry once has totalC satisfying6C=n(n+1)(2n+1), andC/n³ tends to1/3.',
         'CompleteFoundationsCholeskyCost','Expression','evaluate','arithmeticCost','subtractProducts','sourceCell','actual_accumulator_evaluation','actual_accumulator_operation_count','actual_cell_evaluation','actual_positive_recursion_cell_is_factor_entry','actual_cell_operation_count','sourceProgramCost','actual_row_operation_count','actual_program_cost_as_squares','actual_program_cost_polynomial','actual_cost_independent_of_entries','actual_cubic_leading_term',
         hypotheses='Dense exact arithmetic with matrix-entry reads uncounted and each multiplication, subtraction, division and square root assigned unit cost. Every row evaluates exactlycolumns0 throughits row index; positive-recursion assumptions are required for those expression values to equal the actual Cholesky factor entries.',
         correspondence='The arithmetic-expression evaluator is proved equal to the source diagonal/off-diagonal recurrence and to actual factor entries. Its syntactic operation count is summed over the actual lower-triangular row/column indexing. The exact polynomial and actual asymptotic limit substantiate the printed approximate cost; no wall-clock or floating-point stability assertion is inferred.')])

# Genuine differential objects and Taylor remainders added after snapshot9.
COMPLETE_EXERCISES['opt-ex-derivatives-1'] = [
 claim('For the actual Euclidean polynomial x1²+x1*x2+2*x2², the genuine gradient is (2*x1+x2,x1+4*x2), and its actual Frechet derivative is the symmetric Hessian [[2,1],[1,4]].',
       'CompleteFoundationsCalculusModels','sourceQuadratic','actual_quadratic_gradient','actual_quadratic_gradient_coordinates','actual_quadratic_hessian','actual_quadratic_hessian_symmetric',
       hypotheses='Every vector in the real two-dimensional Euclidean space.',
       correspondence='Actual HasGradientAt and HasFDerivAt objects encode the source partials and mixed second partials, with an actual transpose equality rather than a numeric Hessian label.'),
 claim('At (1,-1), the actual gradient is (1,-3) and the actual differential in direction (0,1) is -3. Every vertical displacement t has exact change -3*t+2*t², so the residual after the linear term is genuinely O(t²) near zero.',
       'CompleteFoundationsCalculusModels','actual_directional_derivative','actual_vertical_displacement','actual_vertical_bigO',
       hypotheses='The exact source base point and direction; every real displacement for the exact identity, and the neighbourhood filter at zero for the asymptotic statement.',
       correspondence='The directional derivative is actual fderiv applied to the source direction. A genuine IsBigO statement substantiates the local-slope interpretation and its quadratic remainder.')]
COMPLETE_EXERCISES['opt-ex-derivatives-2'] = [
 claim('For the actual margin 1-x1²-x2² and curve (t,t²), substitution gives 1-t²-t⁴ and a genuine scalar derivative -2*t-4*t³.',
       'CompleteFoundationsCalculusModels','margin','curve','actual_substituted_curve','actual_substitution_derivative',
       hypotheses='Every real curve parameter.',
       correspondence='The actual function composition is identified before its actual HasDerivAt theorem is proved; the source computation is not merely a polynomial expression with no analytic derivative.'),
 claim('The genuine margin gradient is (-2*x1,-2*x2) and the actual curve velocity is (1,2*t). Their actual inner product is the same derivative by the genuine chain rule. At t=1 the actual value is -1 and derivative -6, so the safety test h≥0 fails and the immediate change is negative.',
       'CompleteFoundationsCalculusModels','actual_margin_gradient','actual_curve_velocity','actual_chain_rule_derivative','actual_curve_source_values',
       hypotheses='Every real parameter for the chain rule; exactly t=1 for the source safety/sign conclusion.',
       correspondence='Actual HasGradientAt, vector-valued HasDerivAt and their composition give the source dot-product rule. The actual value and derivative are strictly negative; no all-time safety inference is made from this local statement.')]
COMPLETE_EXERCISES['opt-ex-derivatives-3'] = [
 claim('The actual Euclidean objective exp(x)+y² has genuine gradient (exp(x),2*y) and Hessian diag(exp(x),2). At the origin its value is1, gradient(1,0), Hessian diag(1,2), and its actual second-order Taylor expression is 1+x+x²/2+y².',
       'CompleteFoundationsTaylorModels','objective','actual_gradient','actual_hessian','actual_origin_data','actual_taylor_model','actual_remainder_identity',
       hypotheses='Every real Euclidean input; the origin is the expansion point.',
       correspondence='The model equals the actual value plus the actual gradient inner product plus half the actual Hessian quadratic. The y² contribution is exact, leaving only the actual scalar exponential remainder.'),
 claim('For positive x, the actual exponential Taylor remainder equals exp(c)*x³/6 for some c between0 andx, and lies between0 andexp(x)*x³/6. The actual third derivative is exp(t), bounded by exp(0.1) on [0,0.1].',
       'CompleteFoundationsTaylorModels','actual_iterated_exponential_derivative','actual_scalar_taylor_polynomial','actual_positive_scalar_lagrange_remainder','actual_positive_remainder_bound','actual_third_derivative_and_interval_bound','actual_source_remainder',
       hypotheses='Strictly positive scalar x for the Lagrange theorem; the exact closed interval [0,1/10] for the source derivative bound.',
       correspondence='A genuine Taylor/Lagrange theorem yields an actual intermediate-point witness. Actual function subtraction and the interval derivative bound prove both the sign and the printed source error bound.'),
 claim('At (0.1,0.2), the actual model is1.145, actual objective rounds to1.145170918, error to0.000170918 and bound to0.000184195. Omitting the Hessian factor1/2 adds x²/2+y², gives the actual erroneous source-point value1.19, and exceeds the true value.',
       'CompleteFoundationsTaylorModels','actual_source_model_value','actual_exp_tenth_decimal','actual_source_decimal_values','omittedHalfModel','actual_omitted_half_error','actual_source_omitted_half_value',
       hypotheses='The exact source rational input; every quoted decimal has a strict error enclosure of half a unit in its ninth decimal place.',
       correspondence='Actual exp series bounds rigorously certify the printed approximations, while exact polynomial identities prove the effect of dropping the factor and a strict actual-value comparison.')]
COMPLETE_EXERCISES['opt-ex-matrix-calculus-1'] = [
 claim('For actual A=diag(1,2), b=(1,1) and objective ||Ax-b||², the scalar expansion is (x1-1)²+(2*x2-1)². The genuine gradient equals both (2*(x1-1),4*(2*x2-1)) and2*A transpose*(Ax-b). At zero the actual residual is(-1,-1) and actual gradient(-2,-4).',
       'CompleteFoundationsCalculusModels','leastA','leastB','leastObjective','actual_least_square_expansion','actual_least_square_gradient','actual_least_square_residual_gradient','actual_least_square_source_values',
       hypotheses='Every real two-dimensional Euclidean input, with the exact source matrix and right side.',
       correspondence='The true norm-squared objective, actual gradient and coordinate expansion agree, preserving the transpose orientation and the second-coordinate chain-rule factor.'),
 claim('The actual gradient derivative is the positive-definite Hessian2*A transpose*A=diag(2,8). The source matrix is genuinely invertible; every actual objective is nonnegative and is zero iff x=(1,1/2), which solves Ax=b and is the unique global minimizer.',
       'CompleteFoundationsCalculusModels','actual_least_square_hessian','actual_least_square_matrix_invertible','actual_least_square_unique_minimum','actual_least_square_source_values',
       hypotheses='Every real input for global optimality and uniqueness.',
       correspondence='Genuine HasFDerivAt, Matrix.PosDef and IsUnit objects support the Hessian and inverse claims. Actual norm nonnegativity and an all-input equality iff establish a global unique optimum.')]

for node in [267,272,276,278]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-derivatives-1'][0]]
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-280'] = [COMPLETE_EXERCISES['opt-ex-derivatives-1'][1]]
for node in [285,294]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-derivatives-2'][0]]
for node in [290,296,298]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-derivatives-2'][1]]
for node in [303,308,312]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-derivatives-3'][0]]
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-316'] = [COMPLETE_EXERCISES['opt-ex-derivatives-3'][1]]
for node in [314,318]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-derivatives-3'][2]]
for node in [392,397,401,405]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-matrix-calculus-1'][0]]
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-403'] = [COMPLETE_EXERCISES['opt-ex-matrix-calculus-1'][1]]
for node in [268,286,304,393]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-optimization.html::node-{node}'] = (
  'The exact paragraph is a labelled Review link to its prerequisite section; it adds no mathematical assertion.')
for node in [263,388]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-optimization.html::node-{node}'] = (
  'The exact paragraph gives practice-order and review-link advice only; it asserts no mathematical theorem.')
for node, exercise in [(267,'opt-ex-derivatives-1'),(272,'opt-ex-derivatives-1'),
                       (285,'opt-ex-derivatives-2'),(290,'opt-ex-derivatives-2'),
                       (303,'opt-ex-derivatives-3'),(392,'opt-ex-matrix-calculus-1')]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES[exercise]

COMPLETE_EXERCISES['opt-ex-matrix-calculus-2'] = [
 claim('For every finite invertible real square X and every real direction E, the actual determinant path has derivative det(X)*tr(X inverse*E), its actual log determinant has derivative tr(X inverse*E), and the actual matrix inverse has Frechet differential dY ↦ -X inverse*dY*X inverse.',
       'CompleteFoundationsMatrixSensitivity','actual_generic_identity_determinant_direction','actual_generic_determinant_direction','actual_generic_log_determinant_direction','actual_generic_inverse_differential','actual_generic_inverse_direction',
       hypotheses='Arbitrary finite real square matrices with IsUnit X; the source positive-definite X satisfies this invertibility requirement.',
       correspondence='The actual determinant polynomial derivative at identity equals trace; actual determinant multiplicativity transports it to X. True HasDerivAt and HasFDerivAt objects encode the source directional and inverse differentials.'),
 claim('For source X=diag(2,3) and E=[[1,1],[1,0]], the actual inverse isdiag(1/2,1/3), actual X inverse*E=[[1/2,1/2],[1/3,0]] has trace1/2, actual path is[[2+t,t],[t,3]] with determinant6+3*t-t², and the actual logarithm derivative at zero is1/2.',
       'CompleteFoundationsMatrixSensitivity','sourceX','sourceE','sourcePath','actual_source_path','actual_source_determinant','actual_source_inverse','actual_source_invertible','actual_source_log_trace','actual_source_log_derivative','actual_source_log_expansion_derivative',
       hypotheses='The exact source matrices and every real path parameter for the algebraic equalities; derivative at zero.',
       correspondence='Actual matrix inverse, product, trace and determinant all agree with the genuine path derivative and its scalar determinant expansion.'),
 claim('The actual source path is positive definite for every |t|<1/2, so it is genuinely PD with positive determinant on a neighbourhood of zero. Its actual inverse derivative is -[[1/4,1/6],[1/6,0]], with actual off-diagonal derivative -1/6.',
       'CompleteFoundationsMatrixSensitivity','actual_source_positive_definite','actual_source_positive_neighbourhood','actual_source_inverse_formula','actual_source_inverse_derivative','actual_source_inverse_is_not_entrywise_reciprocal',
       hypotheses='The exact open interval(-1/2,1/2) for the actual PD certificate; actual inverse differentiation at zero.',
       correspondence='Genuine Matrix.PosDef and an eventual-neighbourhood statement substantiate the logarithm domain. The generic order-preserving matrix differential specializes to the exact matrix, and a true entry derivative confirms that matrix inversion is not entrywise reciprocation.')]
COMPLETE_EXERCISES['opt-ex-matrix-calculus-3'] = [
 claim('For genuine differentiable operator families A(theta), states x(theta) and right sides b(theta) satisfying Ax=b near the differentiation point, actual differentiation gives A prime*x+A*x prime=b prime and the actual sensitivity is the linear solve A*x prime=b prime-A prime*x. An invertible operator gives the unique solution by its inverse equivalence.',
       'CompleteFoundationsSolutionSensitivity','actual_differentiated_linear_system','actual_sensitivity_is_linear_solve','actual_invertible_sensitivity_solution',
       hypotheses='Any real normed spaces, actual continuous linear operators and actual HasDerivAt hypotheses, with equation equality on a neighbourhood; a ContinuousLinearEquiv is required for the explicit unique inverse solution.',
       correspondence='The genuine operator-application chain rule differentiates the original equation directly. The result holds in arbitrary normed spaces, supporting the source extension to larger systems without assuming an unexplained derivative of an inverse.'),
 claim('For actual A(theta)=diag(1+theta,2), b=(2,4) and theta>-1, every solution is exactly (2/(1+theta),2). Its genuine derivative is(-2/(1+theta)²,0). Differentiating the actual equation itself forces x(0)=(2,2), x prime(0)=(-2,0), and A*x prime=-A prime*x=(-2,0).',
       'CompleteFoundationsSolutionSensitivity','sourceMatrix','sourceOperator','matrixDerivative','operatorDerivative','rightSide','explicitSolution','actual_operator_coordinates','actual_matrix_derivative','actual_source_solution_iff','actual_explicit_solution_derivative','actual_equation_forces_source_sensitivity','actual_source_zero_data',
       hypotheses='The exact source family and every real parameter theta>-1; the equation-forces-derivative theorem retains an actual HasDerivAt hypothesis for any candidate solution family.',
       correspondence='Actual continuous linear operators, an all-input solution iff, genuine derivative objects and the generic differentiated-equation theorem establish both independent methods and their agreement.'),
 claim('The actual first-order predictor is x(0)+theta*x prime(0)=(2-2*theta,2). Its exact vector error is(2*theta²/(1+theta),0), with genuine Euclidean norm2*theta²/(1+theta) and a genuine O(theta²) estimate near zero. At theta0.01, predictor(1.98,2), exact state(200/101,2), Euclidean error1/5050, and the printed decimals1.980198020 and0.000198020 are rigorously rounded.',
       'CompleteFoundationsSolutionSensitivity','firstOrderPrediction','actual_prediction_is_tangent','actual_exact_prediction_difference','actual_horizontal_norm','actual_prediction_error','actual_prediction_error_bigO','actual_source_prediction_values',
       hypotheses='Theta>-1 for the exact positive error norm; the neighbourhood filter at zero for IsBigO; exact rational theta1/100 for the source numerical values.',
       correspondence='The predictor is explicitly the actual tangent model, not merely a named polynomial. Actual vector subtraction, actual Euclidean norm and an actual asymptotic bound verify the error; strict half-unit ninth-decimal enclosures support both approximations.')]

for node in [410,415]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-matrix-calculus-2']
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-419'] = [COMPLETE_EXERCISES['opt-ex-matrix-calculus-2'][1]]
for node in [421,423]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-matrix-calculus-2']
for node in [428,433]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-matrix-calculus-3']
for node in [437,439]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-matrix-calculus-3'][1]]
for node in [441,443]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = [COMPLETE_EXERCISES['opt-ex-matrix-calculus-3'][0],COMPLETE_EXERCISES['opt-ex-matrix-calculus-3'][2]]
for node in [411,429]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-optimization.html::node-{node}'] = (
  'The exact paragraph is only a labelled Review link to the matrix-derivative prerequisite section; it adds no mathematical assertion.')
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-357'] = [
 claim('At every invertible finite real square X, the genuine inverse Frechet differential acts on every perturbation E as -X inverse*E*X inverse, preserving the actual multiplication order.',
       'CompleteFoundationsMatrixSensitivity','actual_generic_inverse_differential','actual_generic_inverse_direction',
       hypotheses='Arbitrary finite real square matrix and every real perturbation; IsUnit X is necessary for the differential.',
       correspondence='The derivative is the actual continuous linear map for genuine matrix inversion. Its application has exactly the source left/right factors, not coordinatewise reciprocals.')]

PARTIAL_EXERCISES['primer-optimization.html::exercise-30'] = [
 claim('For every finite rectangular real W and real beta, the genuine Frobenius-norm objective beta/4*||WW transpose-I||F² has actual Hilbert gradient beta*(WW transpose-I)*W.',
       'CompleteFoundationsParsevalModels','Space','toMatrix','fromMatrix','errorMatrix','objective','actual_frobenius_squared','actual_error_entries','actual_objective_expansion','actual_error_is_symmetric','actual_entry_differential','actual_symmetric_trace_identity','actual_inner_coordinates','actual_parseval_gradient','actual_gradient_matrix',
       hypotheses='Arbitrary finite row and column types and arbitrary real beta; the actual matrix entries are a complete finite-dimensional Euclidean Hilbert space.',
       correspondence='The actual Frobenius norm and actual matrix Gram error are retained. Genuine entry differentials and an all-matrix symmetric finite-sum identity produce HasGradientAt and the exact actual matrix-gradient formula. The literal matrix-trace proof route is separately covered by the source-specific ParsevalTrace declarations below.'),
 claim('For actual W=[[1,1],[0,1]] and beta1, WW transpose-I=[[1,1],[1,0]], objective3/4 and actual gradient[[1,2],[1,1]]. The genuine gradient step0.1 is[[.9,.8],[-.1,.9]]; its actual cost10287/40000=.257175 strictly decreases and rounds to.257.',
       'CompleteFoundationsParsevalModels','sourceW','sourcePoint','sourceStep','actual_source_data','actual_source_gradient_step','actual_source_step_decreases',
       hypotheses='The exact source matrix and actual step size1/10.',
       correspondence='The matrix is the actual image of a genuine Hilbert gradient, and the update subtracts that gradient. Exact actual Frobenius cost and a rigorous nearest-thousandth enclosure support the printed approximation; no scalar surrogate replaces the source objective.')]


# The generic trace bridge closes every displayed source proof-route clause,
# rather than upgrading the earlier correct gradient merely by theorem count.
COMPLETE_EXERCISES['primer-optimization.html::exercise-30'] = PARTIAL_EXERCISES.pop('primer-optimization.html::exercise-30') + [
 claim('For every matrix direction H, the genuine Gram-error derivative is H W transpose+W H transpose. The genuine Frobenius squared-norm derivative is 2 tr(E dE); symmetry and actual trace cyclicity give tr(E H W transpose)=tr(E W H transpose)=tr(W transpose E H), and dR=beta tr(W transpose E H)=inner(beta E W,H). Actual finite differences converge to this value in every direction.',
       'CompleteFoundationsParsevalTrace','actual_trace_pair_coordinates','actual_trace_pair_is_hilbert_inner','actual_symmetric_source_trace_equalities','actual_symmetric_trace_pair_is_inner','actual_parseval_differential_is_source_inner','actual_error_along_matrix_direction','actual_error_matrix_directional_differential','actual_parseval_directional_trace_derivative','actual_squared_frobenius_directional_trace_derivative','actual_parseval_finite_differences_converge','actual_source_gram_matrix',
       hypotheses='Arbitrary finite real rectangular W and perturbation H, arbitrary real beta, genuine complete Euclidean space of matrix entries and the actual Frobenius norm. The Gram error is symmetric by its actual definition.',
       correspondence='The full Gram-error matrix is differentiated in its actual Hilbert representation, not just an assumed coordinate differential. Actual Matrix.trace identities retain each displayed product factor. HasDerivAt and genuine punctured-neighborhood Tendsto establish the source finite-difference agreement in the derivative sense. The exact source Gram [[2,1],[1,1]] is also explicitly computed; all printed step costs and rounding are covered by the retained actual model.')]
for node in [1667]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['primer-optimization.html::exercise-30']
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-1671'] = [COMPLETE_EXERCISES['primer-optimization.html::exercise-30'][0],COMPLETE_EXERCISES['primer-optimization.html::exercise-30'][2]]
REVIEWED_COMPLETE_MATERIAL['primer-optimization.html::node-1672'] = [COMPLETE_EXERCISES['primer-optimization.html::exercise-30'][1],COMPLETE_EXERCISES['primer-optimization.html::exercise-30'][2]]

# Source-specific actual objective derivatives/KKT conditions and all-domain
# optima close these complete questions and every worked-solution clause.
COMPLETE_EXERCISES['opt-ex-constraints-1'] = [
 claim('For the actual scalar Lagrangian (x-3)^2+lambda*(x-bound), the true derivative is2(x-3)+lambda. All four actual KKT conditions hold at(bound1,x1,lambda4) and(bound4,x3,lambda0), and at the latter point complementary slackness forces lambda0.',
       'CompleteFoundationsConstrainedModels','scalarLagrangian','scalarKKT','actual_scalar_lagrangian_derivative','actual_scalar_kkt_certificates',
       hypotheses='The exact source real scalar objective and one affine upper-bound inequality; KKT includes actual deriv, feasibility, nonnegative multiplier and complementary product.',
       correspondence='Stationarity is the genuine derivative of the actual Lagrangian. The full four-condition conjunction is explicitly proved, and the looser-bound multiplier has an exact iff characterization.'),
 claim('The unconstrained unique minimizer is3 and forbidden by bound1; the objective strictly decreases up to3. On x<=1 its unique global minimum is4 at1; with bound4 the unconstrained point3 is strictly feasible. The objective is ConvexOn and the bound function is affine with a convex feasible set.',
       'CompleteFoundationsConstrainedModels','actual_scalar_global_optima','actual_scalar_objective_decreases_until_three','actual_scalar_objective_is_convex','actual_scalar_constraint_is_affine','actual_scalar_feasible_set_is_convex',
       hypotheses='Arbitrary real feasible points for each source bound, not only the displayed candidate.',
       correspondence='Actual all-point inequalities and iff equality cases prove both optima; genuine StrictAntiOn/ConvexOn and an exact affine-combination identity cover the displayed proof route. The observation about a present inactive constraint is supported by the complete looser-bound calculation.')]
COMPLETE_EXERCISES['opt-ex-constraints-2'] = [
 claim('The actual Euclidean half squared-distance objective is weightedDistance(1,1,2,2), with genuine gradient x-(2,2), true Hessian identity, StrictConvexOn, and unique unconstrained zero at(2,2). Its actual feasible set x0+x1<=1,x0>=0 is convex and excludes that point.',
       'CompleteFoundationsConstrainedModels','weightedDistance','actual_weighted_distance_gradient','actual_weighted_distance_hessian','actual_weighted_distance_strict_convex','actual_weighted_distance_unconstrained_minimum','halfspaceFeasible','actual_halfspace_norm_objective','actual_halfspace_hessian_is_identity','actual_halfspace_feasible_set_is_convex','actual_halfspace_source_kkt',
       hypotheses='The actual complete Euclidean two-coordinate space, with unit positive weights and target(2,2).',
       correspondence='The norm is genuine Euclidean norm, not a product-space maximum norm. The gradient and Hessian differentiate the actual objective; global strict convexity and all-coordinate feasible convexity are proved.'),
 claim('Actual affine constraints g1=x0+x1-1 and g2=-x0 have their true normals. Actual Lagrangian stationarity with lambda2=0 plus g1=0 is equivalent to lambda1=3/2,x=(1/2,1/2); all KKT signs/products/gradient cancellation and strict inactivity of g2 hold.',
       'CompleteFoundationsConstrainedModels','affineConstraint','actual_affine_constraint_gradient','halfspaceLagrangian','actual_halfspace_lagrangian_gradient','actual_halfspace_stationarity_iff','actual_halfspace_active_constraint_solves_candidate','actual_halfspace_source_kkt',
       hypotheses='The exact two source constraints, their sign convention and nonnegative multipliers.',
       correspondence='The actual HasGradientAt Lagrangian gives the displayed vector stationarity; an iff derives the active-set candidate rather than assuming it. Every source feasibility/complementarity/sign check is retained.'),
 claim('Every actual feasible point has cost>=9/4, with equality exactly at(1/2,1/2); hence the KKT candidate is the unique global minimum and also the closest point on the active line.',
       'CompleteFoundationsConstrainedModels','actual_halfspace_global_unique_optimum','actual_halfspace_source_kkt',
       hypotheses='Every point satisfying both inequalities; points on the source active line are included in this comparison and the minimizer lies on that line.',
       correspondence='The full source norm objective and all-domain iff optimality establish uniqueness independently of an unchecked active-set guess. Teaching advice to check guesses is reflected in the explicit complete KKT certificate.')]
COMPLETE_EXERCISES['opt-ex-programs-1'] = [
 claim('The actual two-dimensional QP has Q=diag(2,4),c=(-2,4) and objective1/2 inner(x,Qx)+inner(c,x); adding the omitted constant3 gives exactly(x0-1)^2+2(x1+1)^2 and the expanded source polynomial.',
       'CompleteFoundationsConstrainedModels','sourceQ','sourceC','qpObjective','actual_source_qp_expansion',
       hypotheses='The genuine Euclidean matrix operator and inner product on the actual two-coordinate space.',
       correspondence='The true matrix action and Hilbert inner product retain the convention factor1/2; equality holds for every point, rather than only at the optimizer.'),
 claim('The actual row-matrix constraints A=[[1,1],[-1,0]],b=(2,0) are equivalent to x0+x1<=2 and x0>=0. Q is actual Matrix.PosDef and the squared-distance objective is genuinely strictly convex.',
       'CompleteFoundationsConstrainedModels','sourceA','sourceB','qpFeasible','actual_source_qp_constraints','actual_source_q_is_positive_definite','actual_weighted_distance_strict_convex',
       hypotheses='The source positive weights2,4 and every real two-coordinate point.',
       correspondence='The exact matrix-vector inequalities are proved equivalent to both original scalar constraints. PosDef is the actual all-vector matrix predicate, and StrictConvexOn is proved for arbitrary positive weights.'),
 claim('For every point the original cost is>=0, with equality iff x=(1,-1); the QP without its constant is>=-3 with the identical equality case. The actual optimizer is feasible, so both constrained and unconstrained minimizers are the same unique point.',
       'CompleteFoundationsConstrainedModels','actual_source_qp_unique_global_optimum','actual_source_qp_expansion',
       hypotheses='All real points, hence all points in the actual source feasible set.',
       correspondence='Both actual objective values and all-point iff equality conditions are retained. Constant omission changes exactly the optimal value and preserves the optimizer, as the source says.')]
for node in [1204,1209,1213,1215,1217]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-constraints-1']
for node in [1222,1227,1231,1233,1235,1237]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-constraints-2']
for node in [1318,1323,1327,1329,1331]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-programs-1']
for node in [1205,1223,1319]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-optimization.html::node-{node}'] = 'This exact unit is only a labelled Review link to the prerequisite section; it adds no mathematical conclusion.'

# Actual source norm/gradient/KKT models, whole-domain minima and genuine
# boundary/infeasibility witnesses close these three previously partial rows.
COMPLETE_EXERCISES['opt-ex-programs-3'] = [
 claim('The actual objective is half the squared Euclidean norm, with true gradient u and StrictConvexOn. The actual full feasible set is the safety half-space intersected with both actuator intervals, and is Convex. Without the box, the unique all-feasible half-space projection is(4/5,8/5), which violates the second actuator bound.',
       'CompleteFoundationsBoxedQP','objective','feasible','constraint','actual_norm_objective','actual_objective_gradient','actual_objective_strictly_convex','actual_constraints_iff','actual_boxed_feasible_set_convex','actual_halfspace_only_zero_projection','actual_zero_projection_violates_box',
       hypotheses='The genuine two-coordinate Euclidean space, zero reference, source safety RHS4 and box radius3/2. Every actual feasible input is quantified.',
       correspondence='Actual Euclidean norm and actual derivative are retained. An all-point objective bound with equality iff identifies the true half-space projection; exact safety equality and failed box inequality show why that candidate is not a permitted output.'),
 claim('The actual full-box candidate(1,3/2) has cost13/8=1.625. Multipliers1 for4-u0-2u1 and1/2 foru1-3/2, with the other three bounds at multiplier0, satisfy every primal/dual/complementarity condition and the genuine Lagrangian gradient equation. All other box bounds are strictly inactive. Every feasible input has cost>=13/8, with equality iff this candidate.',
       'CompleteFoundationsBoxedQP','lagrangian','zeroMultipliers','actual_lagrangian_gradient','actual_zero_source_kkt','actual_zero_boxed_unique_global_optimum',
       hypotheses='The complete five-inequality source QP with its displayed sign convention, including every lower and upper actuator bound.',
       correspondence='Stationarity differentiates the actual objective-plus-five-constraint Lagrangian. The entire KKT conjunction and all-point unique global comparison establish the answer independently of an unchecked active-set guess.'),
 claim('The actuator box limits u0+2u1 to at most9/2<5, so the actual feasible set at RHS5 is empty. A nonnegative slack can make u0=u1=0 feasible for the softened RHS5 inequality while violating the original safety requirement.',
       'CompleteFoundationsBoxedQP','actual_box_maximum_and_infeasibility','relaxedFeasible','actual_slack_restores_solvability_without_original_guarantee',
       hypotheses='Both true actuator bounds remain imposed; the relaxed witness changes only the safety inequality by adding nonnegative slack.',
       correspondence='Actual set equality with the empty set proves infeasibility, not just failure of one candidate. The softened-feasible/original-infeasible witness proves that adding slack changes the requirement and does not recover its original guarantee.')]
COMPLETE_EXERCISES['primer-optimization.html::exercise-34'] = [
 claim('For the actual reference(2,1) and RHS21/5, the unique half-space-only projection is(51/25,27/25), with exact cost1/250. Its coordinate clipping is(3/2,27/25), yielding safety value183/50=3.66<4.2, so sequential half-space projection and box clipping fail the intersection.',
       'CompleteFoundationsBoxedQP','actual_norm_objective','actual_halfspace_only_reference_projection','clip','actual_reference_projection_and_clipping',
       hypotheses='The genuine source Euclidean tracking objective, exact half-space RHS4.2 and actuator radius1.5.',
       correspondence='The half-space projection is proved by an all-point unique global comparison. The actual coordinate max/min clip is evaluated exactly, with original reference normal product4 and projection increment(1/25)*(1,2) retained.'),
 claim('The full-box point(3/2,27/20) has objective149/800=.18625. Actual five-constraint KKT holds with safety multiplier7/40=.175 and first-upper-bound multiplier27/40=.675, others0; objective gradient(-1/2,7/20) cancels the actual normals. The feasible set is convex and objective StrictConvexOn. Every feasible point has objective>=149/800 with equality iff this point.',
       'CompleteFoundationsBoxedQP','actual_objective_gradient','actual_objective_strictly_convex','actual_boxed_feasible_set_convex','actual_lagrangian_gradient','referenceMultipliers','actual_reference_source_kkt','actual_reference_boxed_unique_global_optimum',
       hypotheses='Every input satisfying all five actual source inequalities; all inactive box bounds and multiplier signs are included.',
       correspondence='The true Euclidean objective and actual Lagrangian derivatives match the displayed source stationarity. A quantified all-feasible unique minimum proves global optimality and exact cost, retaining the full model rather than numeric checks alone.'),
 claim('A genuine finite box grid with spacing1/20 has the actual optimal grid point at indices(60,57)=(3/2,27/20); its objective is no larger than any other feasible grid point. RHS5 is genuinely infeasible on the box, while an actual slack-feasible zero command need not satisfy the original safety inequality.',
       'CompleteFoundationsBoxedQP','gridPoint','actual_grid_search_agrees','actual_box_maximum_and_infeasibility','actual_slack_restores_solvability_without_original_guarantee',
       hypotheses='The source does not specify a grid spacing; the explicit 61-by61 grid includes the exact source optimizer. Infeasibility quantifies the full continuous actuator box.',
       correspondence='The grid agreement is an actual all-grid comparison with candidate attainment, not an empirical claim from an unrecorded simulation. Continuous infeasibility and a softened counterexample establish the exact bounded-input/slack conclusions.')]
COMPLETE_EXERCISES['opt-ex-constraints-3'] = [
 claim('The actual positive-part quadratic penalty has the two displayed branches. On the lower branch the objective strictly decreases toward1 with value1. The actual upper-branch derivative is8x-10 and actual second derivative8>0; its stationary candidate5/4 has penalized cost3/4, smaller than1, and violation1/4.',
       'CompleteFoundationsPenaltyModels','objective','constraint','quadraticPenalty','candidate','actual_objective_derivative','actual_constraint_derivative','actual_penalty_branch_formulas','actual_right_polynomial_derivative','actual_penalty_derivative_below_one','actual_penalty_derivative_above_one','actual_right_polynomial_curvature','actual_objective_decreases_to_branch_endpoint','actual_practice_penalty_derivative_and_curvature','actual_penalty_second_derivative_above_one','actual_candidate_true_stationarity','actual_practice_penalty_values_and_infeasibility',
       hypotheses='Practice coefficient3 corresponds to generic penalty weight rho6. Branch polynomial derivative formulas hold universally; genuine full-penalty derivatives and second derivative on the upper open branch require x>1, including the stationary source candidate.',
       correspondence='Derivatives are true HasDerivAt objects. The source Hessian refers to the branch polynomial, with actual full-objective second derivative also established throughout its open branch. Exact objective and penalty terms support the displayed .75²+3(.25)² value.'),
 claim('For every finite nonnegative rho, the actual penalty uniquely globally minimizes at(4+rho)/(2+rho), with strictly positive violation2/(2+rho). In particular the source rho6 optimizer5/4 uniquely minimizes the entire piecewise objective and violates the original bound.',
       'CompleteFoundationsPenaltyModels','actual_penalty_candidate_violation','actual_right_branch_completed_square','actual_penalty_generic_unique_global_optimum',
       hypotheses='Arbitrary finite nonnegative real weight rho and every real input x; no branch is omitted from the global comparison.',
       correspondence='The exact completed square on the upper branch and strict lower-branch separation prove full all-point lower bound/equality iff. This substantiates the claimed trade of feasibility for lower penalized objective, not only local stationarity.'),
 claim('The actual epsilon-KKT definition includes original feasibility, nonnegative multiplier, genuine objective/constraint gradient norm residual and complementary residual. Atx9/10,lambda11/5, g=-1/10<0, stationarity norm0 and complementary residual11/50=.22. It holds iff epsilon>=11/50, and exact KKT fails despite zero stationarity.',
       'CompleteFoundationsPenaltyModels','epsilonKKT','actual_gradients_and_stationarity_residual','actual_practice_approximate_kkt_numbers','actual_practice_minimal_epsilon','actual_practice_not_exact_kkt_despite_zero_stationarity',
       hypotheses='The exact real scalar objective and one affine constraint, with the page norm/complementarity definition retained.',
       correspondence='The residual is the actual gradient norm, identified with the real absolute value using genuine derivative-to-gradient conversion. The whole definition has an exact iff threshold, preserving feasibility and multiplier signs. Positive inactive-constraint multiplier explicitly violates complementarity.')]
for node in [1354,1359,1363,1365,1367,1369]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-programs-3']
for node in [1705,1710,1711,1712]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['primer-optimization.html::exercise-34']
for node in [1242,1247,1251,1254,1256,1258]:
 REVIEWED_COMPLETE_MATERIAL[f'primer-optimization.html::node-{node}'] = COMPLETE_EXERCISES['opt-ex-constraints-3']
for node in [1243,1355]:
 REVIEWED_NONFORMAL_MATERIAL[f'primer-optimization.html::node-{node}'] = 'This exact paragraph is only a labelled Review link to the prerequisite topic; it adds no mathematical assertion.'

# One broad lesson paragraph is split into exact proved model conclusions and
# its still-unproved generic/rate/algorithm clauses. It is not a full-unit closure.
REVIEWED_PARTIAL_MATERIAL['primer-optimization.html::node-1107'] = {
 'proved': [
  claim('For every finite nonnegative weight rho, the actual quadratic-penalty running example uniquely globally minimizes at(4+rho)/(2+rho), with strictly positive original-constraint violation2/(2+rho).',
        'CompleteFoundationsPenaltyModels','quadraticPenalty','candidate','actual_penalty_candidate_violation','actual_penalty_generic_unique_global_optimum',
        hypotheses='The exact running objective(x-2)^2 and constraintx<=1 on the whole real line, with finite realrho>=0.',
        correspondence='The actual positive-part penalty and all-real-point equality iff establish the genuine global optimizer. Positive violation proves infeasibility for every finite weight, rather than only for several printed numbers.'),
  claim('The actual scalar L1 positive-part penalty has unique global minimizer1 exactly whenrho>=2. For0<=rho<2 its unique minimizer is2-rho/2 with costrho-rho^2/4. At weight>=2 the actual penalty has unequal left/right derivatives and is genuinely nondifferentiable at1.',
        'CompleteFoundationsExactPenaltyModels','exactPenalty','actual_exact_penalty_branches','actual_exact_penalty_upper_weight_global_unique','actual_exact_penalty_below_weight_global_unique','actual_exactness_threshold','actual_exact_penalty_one_sided_derivatives','actual_exact_penalty_is_nondifferentiable_at_threshold',
        hypotheses='The exact running real objective and affine upper-bound constraint, with nonnegative real weight for the iff threshold.',
        correspondence='Both real branches are compared globally with iff equality cases. True one-sided derivatives and uniqueness of derivatives on the two half-lines prove the actual kink, not merely a plotted corner.'),
  claim('For the source linear slack model, every relaxed-feasible cost is bounded below by the actual exact penalty. For0<=p<2 an actual global optimum isx=2-p/2,s=1-p/2; forp>=2 the actual global optimum isx1,s0. In particularp1 gives the actual globally optimal relaxed-feasible pointx1.5,s.5, which violates the originalx<=1 constraint.',
        'CompleteFoundationsExactPenaltyModels','slackObjective','slackFeasible','actual_slack_objective_dominates_exact_penalty','actual_slack_lower_price_optimum','actual_slack_upper_price_optimum','actual_source_slack_violation',
        hypotheses='The whole real scalar decision/slack space, slack>=0 andx<=1+slack; nonnegative linear slack price.',
        correspondence='The true two-variable objective is compared against every relaxed-feasible pair. Actual optimized violation shows why relaxed feasibility cannot establish the original constraint; no unique slack claim is inferred at zero price.'),
  claim('For every given point in any domain and finite family of real inequalities, nonnegative slacksmax(g_i(x),0) make every softened inequalityg_i(x)<=s_i feasible.',
        'CompleteFoundationsExactPenaltyModels','actual_finite_softening_feasible',
        hypotheses='A given underlying decision point exists; the finite inequality family under consideration is softened. Other hard constraints and nonempty hard domains are not supplied by slack.',
        correspondence='The actual coordinate slack construction is proved for arbitrary types and finite families. It substantiates solvability of fully softened finite constraints on a nonempty decision domain, without asserting solvability of an independently infeasible hard part.'),
  claim('The actual constrained nonconvex objective-x^4 onx^2<=1 has global minima exactly at+-1 with value-1; both satisfy actual derivative-based KKT with multiplier2. Its actual L1 penalty-x^4+rho*max(x^2-1,0) is unbounded below for every finite realrho.',
        'CompleteFoundationsExactPenaltyModels','nonconvexObjective','nonconvexConstraint','nonconvexPenalty','actual_nonconvex_constrained_global_minima','actual_nonconvex_lagrangian_derivative','actual_nonconvex_source_kkt','actual_nonconvex_penalty_unbounded_below',
        hypotheses='The actual nonconvex polynomial objective and scalar inequality; every realpenalty weight and every proposed finite lower bound are quantified.',
        correspondence='A full constrained all-point lower bound/equality iff identifies both genuine optima. True Lagrangian derivatives verify their KKT multipliers. A sqrt-based actual point violates every proposed penalized lower bound, establishing genuine unboundedness rather than one finite failure.')],
 'pending': [
  'Supply exact source quadratic-penalty valuesx=1.5,1.1,1.01 atrho2,18,198 and both actual open-branch second derivatives2 and2+rho in explicitly source-bound wrappers.',
  'Supply the source large-rho step-size scaling1/rho, conditioning interpretation and amplification of approximate-objective errors with precise norms, hypotheses and genuine algorithm/error conclusions.',
  'Supply the generic finite-constraint convex exact-penalty theorem forrho>||lambda-star||infinity from actual attained optimal multiplier and strong-duality definitions, preserving feasibility/nonempty/boundedness requirements.',
  'Supply the actual rho2 augmented-Lagrangian minimization/update model, the three printed iterate pairs, genuine all-time convergence to(1,2), and the exact positive-part proportional violation correction.',
  'Classify the MPC recursive-feasibility claim under exact hard-domain/nonempty and softened-constraint assumptions; a finite given-point slack construction alone does not prove arbitrary hard-constrained MPC recursion.',
  'The instruction to keep safety constraints hard and reserve slack for performance is modeling advice supported by the actual relaxed-original counterexample; any further mathematical safety/recursive-feasibility guarantee requires its own precise model proof.']}

# These two future modules have actual standalone EXIT0 and a separate
# independent component review. Keep the complete paragraph partial.
_augmented_review = 'book/coverage/checks/foundations-augmented-generic-penalty-source-review-v1.json'
REVIEWED_PARTIAL_MATERIAL['primer-optimization.html::node-1107']['proved'] += [
 claim('The actual quadratic-penalty candidates are exactly1.5,1.1,1.01 at rho2,18,198. Its actual second derivatives on the open branchesx<1 andx>1 are respectively2 and2+rho.',
       'CompleteFoundationsAugmentedModels','actual_quad_source_candidates','actual_quadratic_penalty_both_open_branch_curvatures',
       hypotheses='The actual running positive-part penalty and its two open branches; no second derivative at the branch boundary is inferred.',
       correspondence='True derivatives of the actual derivative function give both source curvatures. Exact rational source values are tied to the genuine global candidate. Independently reviewed in '+_augmented_review+'.'),
 claim('For arbitrary finite real inequality constraints on a nonempty feasible domain, an actual attained nonnegative optimal multiplier with a bounded-below Lagrangian and strong duality makes the positive-part sum penalty exact whenever rho exceeds the multiplier infinity norm. Its actual infimum equals the primal infimum; its true argmin set is exactly the original constrained argmin set, and every infeasible point has penalty strictly above the common optimal value.',
       'CompleteFoundationsGenericPenalty','feasible','lagrangian','primalValues','primalValue','dualValue','admissibleMultiplier','dualValues','dualSupremum','attainedOptimalMultiplier','exactPenalty','actual_weak_duality','actual_dual_supremum_weak_bound','actual_strong_duality_and_attainment','actual_sup_norm_weight_bounds_every_multiplier','actual_penalty_lagrangian_gap','actual_infeasible_penalty_strictly_dominates_lagrangian','actual_exact_penalty_optimal_value_and_feasibility','actual_exact_penalty_infimum_and_argmin',
       hypotheses='Finite inequality family; genuine nonempty feasible set; the actual admissible multiplier attains the true dual supremum; true primal infimum equals that supremum; rho>the actual finite-Pi infinity norm. These are the explicit strong-duality/attainment premises, not assumed penalty optimality.',
       correspondence='Actual primal/Lagrangian infima and dual supremum supply the source mathematical objects. Strict positive penalty-Lagrangian gaps force feasibility at the optimal value and yield exact argmin-set equality. Convexity is not needed once the source duality/attainment hypotheses hold. Independently reviewed in '+_augmented_review+'.'),
 claim('The actual rho2 augmented Lagrangian has the source positive-part objective, global unique minimizer(6-lambda)/4 for every nonnegative multiplier, actual zero derivative at that point, and true projected update max(lambda+2*(x-1),0)=(lambda+2)/2 there.',
       'CompleteFoundationsAugmentedModels','augmentedObjective','augmentedCandidate','multiplierUpdate','actual_augmented_branches','actual_augmented_upper_completed_square','actual_augmented_global_unique','actual_augmented_candidate_and_update','actual_augmented_candidate_true_stationarity',
       hypotheses='Exactly the running objective(x-2)^2, constraintx-1, fixed penaltyrho2 and arbitrary nonnegative multiplier.',
       correspondence='Both real branches of the actual augmented objective are compared globally; the minimizer and its genuine derivative are derived. The update is the actual positive part of multiplier plus proportional violation. Independently reviewed in '+_augmented_review+'.'),
 claim('Starting at multiplier0, every actual primal iterate globally minimizes its augmented objective and the multiplier obeys the actual projected recurrence. The exact pairs(1.5,1),(1.25,1.5),(1.125,1.75) belong to the all-time sequence, which genuinely tends to(1,2) with the fixed finite penaltyrho2.',
       'CompleteFoundationsAugmentedModels','actualMultiplier','actualPrimalStep','actual_multiplier_range','actual_primal_step_formula','actual_running_iteration','actual_source_three_pairs','actual_running_primal_and_multiplier_limits','actual_source_paired_iteration_limit',
       hypotheses='The true primal-minimization/projected-update sequence for the source rho2 model, initialized with lambda0=0.',
       correspondence='The all-time closed formula and its actual recurrence identify the optimization algorithm; filter Tendsto proves paired convergence. Finite-penalty sufficiency is established for this running model, without asserting arbitrary augmented-Lagrangian convergence. Independently reviewed in '+_augmented_review+'.')]
REVIEWED_PARTIAL_MATERIAL['primer-optimization.html::node-1107']['pending'] = [
 'Supply the source large-rho step-size scaling1/rho, conditioning interpretation and amplification of approximate-objective errors with precise norms, hypotheses and genuine algorithm/error conclusions.',
 'Classify the MPC recursive-feasibility claim under exact hard-domain/nonempty and softened-constraint assumptions; a finite given-point slack construction alone does not prove arbitrary hard-constrained MPC recursion.',
 'The instruction to keep safety constraints hard and reserve slack for performance is modeling advice supported by the actual relaxed-original counterexample; any further mathematical safety/recursive-feasibility guarantee requires its own precise model proof.']

# Finite exact semantic review of isolated headings and prerequisite links.
# No surrounding definition/application/theorem is closed by these leaf labels.
import json as _review_json
import hashlib as _review_hashlib
from pathlib import Path as _ReviewPath
_labels_path = _ReviewPath('book/coverage/checks/foundations-material-label-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_labels_path.read_bytes()).hexdigest() == '6283841c6e20ac690b92b71334253944ba883ad03db0e4ead96ca861cc8f46cd'
_label_review = _review_json.loads(_labels_path.read_text())
_live_label_units = {u['key']: u for u in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['material_source_units']}
for _label_unit in _label_review['material_units']:
 _live_label = _live_label_units[_label_unit['source_unit_key']]
 assert _label_unit['material_status'] == 'not_a_formal_claim'
 assert _live_label['text_sha256'] == _label_unit['unit_text_sha256']
 assert _live_label['source_sha256'] == _label_unit['source_sha256']
 REVIEWED_NONFORMAL_MATERIAL[_label_unit['source_unit_key']] = _label_unit['per_unit_reason'] + ' Exact semantic record: ' + str(_labels_path) + '.'


# Working checkpoint14: exact independent whole-source review of original0.7c.
# This finite source-bound loader preserves per-clause and per-unit scopes.
_regret_path = _ReviewPath('book/coverage/checks/foundations-regret-0-7c-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_regret_path.read_bytes()).hexdigest() == '506dc8db9908f327c5851fa481970c88a3224e345f92b76239c274bd1fa64825'
_regret_review = _review_json.loads(_regret_path.read_text())
assert _regret_review['status'] == 'independent_whole_source_review_passed' and not _regret_review['missing_clauses']
_live_regret_ex = next(e for e in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['exercises'] if e['key'] == _regret_review['exercise_key'])
assert _live_regret_ex['text_sha256'] == _regret_review['exercise_text_sha256']
for _regret_file,_regret_hash in _regret_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_regret_file).read_bytes()).hexdigest() == _regret_hash
for _regret_evidence in _regret_review['actual_standalone_evidence']:
 assert _regret_evidence['exit_code'] == 0 and _regret_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_regret_evidence['compiler_manifest']).read_bytes()).hexdigest() == _regret_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_regret_evidence['log']).read_bytes()).hexdigest() == _regret_evidence['log_sha256']
COMPLETE_EXERCISES['mb-ex-asymptotics-3'] = [dict(
 statement_in_prose=c['source_clause'],lean_declarations=c['lean_declarations'],
 hypotheses=c['hypotheses'],correspondence=c['reason']+' Exact independent whole review: '+str(_regret_path)+'.')
 for c in _regret_review['components'] if c['status']=='approved']
for _regret_unit in _regret_review['material_units']:
 _regret_live = _live_label_units[_regret_unit['source_unit_key']]
 assert _regret_live['text_sha256']==_regret_unit['unit_text_sha256'] and _regret_live['source_sha256']==_regret_unit['source_sha256']
 assert not _regret_unit['missing_clauses']
 if _regret_unit['material_status']=='proved':
  REVIEWED_COMPLETE_MATERIAL[_regret_unit['source_unit_key']] = [dict(
   statement_in_prose=_regret_unit['source_text'],lean_declarations=_regret_unit['lean_declarations'],
   hypotheses='The exact cumulative-regret source inequality for natural budgets at least2; nonnegative sparse trial counterexample; natural logarithms and the source finite budget where stated.',
   correspondence=_regret_unit['per_unit_reason']+' Exact independent whole review: '+str(_regret_path)+'.')]
 else:
  assert _regret_unit['material_status']=='not_formalizable'
  REVIEWED_NONFORMAL_MATERIAL[_regret_unit['source_unit_key']] = _regret_unit['per_unit_reason']+' Exact independent whole review: '+str(_regret_path)+'.'

# Working14: actual finite backup table and continuous nested interval game.
_backup_path = _ReviewPath('book/coverage/checks/foundations-backup-games-b8b-b8c-source-review-v1.json')
assert _review_hashlib.sha256(_backup_path.read_bytes()).hexdigest() == 'e3f5fb440c8b2a137eb9223a5e561a41958f0a17dc03c773052ada62d302204f'
_backup_review = _review_json.loads(_backup_path.read_text())
assert _backup_review['status']=='independent_whole_source_reviews_passed' and not _backup_review['missing_clauses']
for _backup_file,_backup_hash in _backup_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_backup_file).read_bytes()).hexdigest()==_backup_hash
for _backup_evidence in _backup_review['actual_standalone_evidence']:
 assert _backup_evidence['exit_code']==0 and _backup_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_backup_evidence['compiler_manifest']).read_bytes()).hexdigest()==_backup_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_backup_evidence['log']).read_bytes()).hexdigest()==_backup_evidence['log_sha256']
_live_backup_exercises = {e['key']:e for e in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['exercises']}
for _backup_exercise in _backup_review['exercises']:
 assert _backup_exercise['review_status']=='approved_complete_source' and not _backup_exercise['missing_clauses']
 assert _live_backup_exercises[_backup_exercise['exercise_key']]['text_sha256']==_backup_exercise['exercise_text_sha256']
 COMPLETE_EXERCISES[_backup_exercise['exercise_key'].split('#')[1]] = [dict(
  statement_in_prose=c['source_clause'],lean_declarations=c['lean_declarations'],hypotheses=c['hypotheses'],
  correspondence=c['reason']+' Exact independent whole review: '+str(_backup_path)+'.')
  for c in _backup_exercise['reviewed_clauses'] if c['status']=='approved']
for _backup_unit in _backup_review['material_units']:
 _backup_live = _live_label_units[_backup_unit['source_unit_key']]
 assert _backup_live['text_sha256']==_backup_unit['unit_text_sha256'] and _backup_live['source_sha256']==_backup_unit['source_sha256']
 assert not _backup_unit['missing_clauses']
 if _backup_unit['material_status']=='proved':
  REVIEWED_COMPLETE_MATERIAL[_backup_unit['source_unit_key']] = [dict(
   statement_in_prose=_backup_unit['source_text'],lean_declarations=_backup_unit['lean_declarations'],
   hypotheses='The exact source three-controller/two-constraint real margin table; or the actual real interval game X=[0,2],Y=[-3,0],L=(x-1)^2-(y+2)^2, according to this exact unit.',
   correspondence=_backup_unit['per_unit_reason']+' Exact independent whole review: '+str(_backup_path)+'.')]
 else:
  assert _backup_unit['material_status']=='not_formalizable'
  REVIEWED_NONFORMAL_MATERIAL[_backup_unit['source_unit_key']] = _backup_unit['per_unit_reason']+' Exact independent whole review: '+str(_backup_path)+'.'

# Working14: independently reviewed genuine finite induction, triangular exchange and random horizon.
_discount_path = _ReviewPath('book/coverage/checks/foundations-discount-horizons-0-3-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_discount_path.read_bytes()).hexdigest() == 'baf989daec673fac49cbc4bc4fe2cf28ab640a1d4777604e257e251420e9d08c'
_discount_review = _review_json.loads(_discount_path.read_text())
assert _discount_review['status']=='independent_whole_source_review_passed' and all(not e['missing_clauses'] for e in _discount_review['exercises'])
for _discount_file,_discount_hash in _discount_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_discount_file).read_bytes()).hexdigest()==_discount_hash
for _discount_evidence in _discount_review['actual_standalone_evidence']:
 assert _discount_evidence['exit_code']==0 and _discount_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_discount_evidence['compiler_manifest']).read_bytes()).hexdigest()==_discount_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_discount_evidence['log']).read_bytes()).hexdigest()==_discount_evidence['log_sha256']
_live_discount_exercises = {e['key']:e for e in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['exercises']}
for _discount_exercise in _discount_review['exercises']:
 assert _discount_exercise['review_status']=='approved_complete_source' and not _discount_exercise['missing_clauses']
 assert _live_discount_exercises[_discount_exercise['exercise_key']]['text_sha256']==_discount_exercise['exercise_text_sha256']
 COMPLETE_EXERCISES[_discount_exercise['exercise_key']] = [dict(
  statement_in_prose=c['source_clause'],lean_declarations=c['lean_declarations'],hypotheses=c['hypotheses'],
  correspondence=c['reason']+' Exact independent whole review: '+str(_discount_path)+'.')
  for c in _discount_exercise['reviewed_clauses'] if c['status']=='approved']
for _discount_unit in _discount_review['material_units']:
 _discount_live = _live_label_units[_discount_unit['source_unit_key']]
 assert _discount_live['text_sha256']==_discount_unit['unit_text_sha256'] and _discount_live['source_sha256']==_discount_unit['source_sha256']
 assert not _discount_unit['missing_clauses']
 if _discount_unit['material_status']=='proved':
  REVIEWED_COMPLETE_MATERIAL[_discount_unit['source_unit_key']] = [dict(
   statement_in_prose=_discount_live['source_text'],lean_declarations=_discount_unit['lean_declarations'],
   hypotheses='Actual realq!=1 for finite geometric induction, 0<=q<1 for genuine infinite nonnegative sums and the actual horizon law; exact sourceq=.9 for the numeric values.',
   correspondence=_discount_unit['per_unit_reason']+' Exact independent whole review: '+str(_discount_path)+'.')]
 else:
  assert _discount_unit['material_status']=='not_formalizable'
  REVIEWED_NONFORMAL_MATERIAL[_discount_unit['source_unit_key']] = _discount_unit['per_unit_reason']+' Exact independent whole review: '+str(_discount_path)+'.'

# Working14: exact whole geometric-series lesson and its two overlapping units.
_lesson_series_path = _ReviewPath('book/coverage/checks/foundations-lesson-geometric-material-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_lesson_series_path.read_bytes()).hexdigest() == '2341319fd9025606651a453111d585f937c36f718d709929db85d014cbd45ab1'
_lesson_series_review = _review_json.loads(_lesson_series_path.read_text())
assert _lesson_series_review['status']=='independent_source_correspondence_review_passed' and not _lesson_series_review['missing_clauses']
for _lesson_series_file,_lesson_series_hash in _lesson_series_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_lesson_series_file).read_bytes()).hexdigest()==_lesson_series_hash
for _lesson_series_evidence in _lesson_series_review['actual_standalone_evidence']:
 assert _lesson_series_evidence['exit_code']==0 and _lesson_series_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_lesson_series_evidence['compiler_manifest']).read_bytes()).hexdigest()==_lesson_series_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_lesson_series_evidence['log']).read_bytes()).hexdigest()==_lesson_series_evidence['log_sha256']
_lesson_series_clauses={c['id']:c for c in _lesson_series_review['reviewed_clauses']}
for _lesson_series_unit in _lesson_series_review['material_units']:
 _lesson_series_live=_live_label_units[_lesson_series_unit['source_unit_key']]
 assert _lesson_series_live['text_sha256']==_lesson_series_unit['unit_text_sha256']
 assert _lesson_series_live['source_sha256']==_lesson_series_review['source_sha256'][_lesson_series_live['source']]
 assert not _lesson_series_unit['missing_clauses']
 if _lesson_series_unit['review_status']=='approved_complete_source':
  REVIEWED_COMPLETE_MATERIAL[_lesson_series_unit['source_unit_key']]=[dict(
   statement_in_prose=_lesson_series_clauses[cid]['source_clause'],
   lean_declarations=_lesson_series_clauses[cid]['lean_declarations'],
   hypotheses='The actual real geometric ratio q!=1 for the finite quotient; |q|<1 for the signed infinite series and tails; arbitrary rewards with |r_t|<=Rmax and 0<=q<1 for the discount inequalities. Effective horizon means actual geometric mass, with exact q=.99 in the example.',
   correspondence=_lesson_series_clauses[cid]['per_clause_reason']+' Exact independent whole review: '+str(_lesson_series_path)+'.')
   for cid in _lesson_series_unit['clause_ids']]
 else:
  assert _lesson_series_unit['review_status']=='approved_specific_nonformalizable_label'
  REVIEWED_NONFORMAL_MATERIAL[_lesson_series_unit['source_unit_key']]=_lesson_series_unit['reason']+' Exact independent whole review: '+str(_lesson_series_path)+'.'

# Working14: independently reviewed actual finite reachability closure and genuine threshold jump.
_reachability_path = _ReviewPath('book/coverage/checks/foundations-reachability-0-2-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_reachability_path.read_bytes()).hexdigest() == '00160405420ebcd3f4c89f0b26d69c4dc628d77f18e81732e1b220be8d2fdad1'
_reachability_review = _review_json.loads(_reachability_path.read_text())
assert _reachability_review['status']=='independent_whole_source_review_passed' and all(not e['missing_clauses'] for e in _reachability_review['exercises'])
for _reachability_file,_reachability_hash in _reachability_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_reachability_file).read_bytes()).hexdigest()==_reachability_hash
for _reachability_evidence in _reachability_review['actual_standalone_evidence']:
 assert _reachability_evidence['exit_code']==0 and _reachability_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_reachability_evidence['compiler_manifest']).read_bytes()).hexdigest()==_reachability_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_reachability_evidence['log']).read_bytes()).hexdigest()==_reachability_evidence['log_sha256']
_live_reachability_exercises = {e['key']:e for e in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['exercises']}
for _reachability_exercise in _reachability_review['exercises']:
 assert _reachability_exercise['review_status']=='approved_complete_source' and not _reachability_exercise['missing_clauses']
 assert _live_reachability_exercises[_reachability_exercise['exercise_key']]['text_sha256']==_reachability_exercise['exercise_text_sha256']
 COMPLETE_EXERCISES[_reachability_exercise['exercise_key']] = [dict(
  statement_in_prose=c['source_clause'],lean_declarations=c['lean_declarations'],hypotheses=c['hypotheses'],
  correspondence=c['reason']+' Exact independent whole review: '+str(_reachability_path)+'.')
  for c in _reachability_exercise['reviewed_clauses'] if c['status']=='approved']
for _reachability_unit in _reachability_review['material_units']:
 _reachability_live = _live_label_units[_reachability_unit['source_unit_key']]
 assert _reachability_live['text_sha256']==_reachability_unit['unit_text_sha256'] and _reachability_live['source_sha256']==_reachability_unit['source_sha256']
 assert not _reachability_unit['missing_clauses']
 if _reachability_unit['material_status']=='proved':
  REVIEWED_COMPLETE_MATERIAL[_reachability_unit['source_unit_key']] = [dict(
   statement_in_prose=_reachability_live['source_text'],lean_declarations=_reachability_unit['lean_declarations'],
   hypotheses='Actual source Fin9 fitness vector, absolute coordinate distance, initial singleton0, epsilon=.5 or0 for the computed closures; arbitrary finite domains for the strict-increase cardinality theorem, and .4<epsilon<=.5 for the genuine gateway jump.',
   correspondence=_reachability_unit['per_unit_reason']+' Exact independent whole review: '+str(_reachability_path)+'.')]
 else:
  assert _reachability_unit['material_status']=='not_formalizable'
  REVIEWED_NONFORMAL_MATERIAL[_reachability_unit['source_unit_key']] = _reachability_unit['per_unit_reason']+' Exact independent whole review: '+str(_reachability_path)+'.'


# Working14: exact independent full review of original0.5, including every sublevel case.
_minima_path = _ReviewPath('book/coverage/checks/foundations-minima-0-5-source-review-v1-correction23-rebase.json')
assert _review_hashlib.sha256(_minima_path.read_bytes()).hexdigest() == '76d80fd9306c830218f6efa7d06fde619f2b9a9b360fcfdc62233da8921a1b2d'
_minima_review = _review_json.loads(_minima_path.read_text())
assert _minima_review['status']=='approved_complete_source' and not _minima_review['missing_clauses']
_live_minima_ex = next(e for e in _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())['exercises'] if e['key']==_minima_review['exercise_key'])
assert _live_minima_ex['text_sha256']==_minima_review['exercise_text_sha256']
for _minima_file,_minima_hash in _minima_review['proof_source_sha256'].items():
 assert _review_hashlib.sha256(_ReviewPath(_minima_file).read_bytes()).hexdigest()==_minima_hash
for _minima_evidence in _minima_review['actual_standalone_evidence']:
 assert _minima_evidence['exit_code']==0 and _minima_evidence['unchanged']
 assert _review_hashlib.sha256(_ReviewPath(_minima_evidence['compiler_manifest']).read_bytes()).hexdigest()==_minima_evidence['compiler_manifest_sha256']
 assert _review_hashlib.sha256(_ReviewPath(_minima_evidence['log']).read_bytes()).hexdigest()==_minima_evidence['log_sha256']
COMPLETE_EXERCISES[_minima_review['exercise_key']] = [dict(
 statement_in_prose=c['source_clause'],lean_declarations=c['lean_declarations'],hypotheses=c['hypotheses'],
 correspondence=c['per_clause_reason']+' Exact independent whole review: '+str(_minima_path)+'.')
 for c in _minima_review['reviewed_clauses'] if c['status']=='approved_precise_component' and not c['missing_clauses']]
for _minima_unit in _minima_review['material_units']:
 _minima_live = _live_label_units[_minima_unit['source_unit_key']]
 assert _minima_live['text_sha256']==_minima_unit['unit_text_sha256'] and _minima_live['source_sha256']==_minima_unit['source_sha256']
 assert _minima_unit['review_status']=='approved_complete_source' and _minima_unit['material_status']=='proved' and not _minima_unit['missing_clauses']
 REVIEWED_COMPLETE_MATERIAL[_minima_unit['source_unit_key']] = [dict(
  statement_in_prose=_minima_live['source_text'],lean_declarations=_minima_unit['lean_declarations'],
  hypotheses='The five exact original0.5 real models and domains: exp(-x) on nonnegative reals; x²-x on[0,1]; Euclidean norm² on the closed halfspace sum>=1; sum u1+u2 on real²; and x²/(1+x²) sublevels for every real threshold.',
  correspondence=_minima_unit['per_unit_reason']+' Exact independent whole review: '+str(_minima_path)+'.')]

# Working15: load only independently approved whole literal exercises/units.
# Each caller pins its actual review bytes; historical reviews and execution
# records stay untouched. Unapproved or incomplete records cannot enter here.
def _load_independent_full_foundation_review(path, expected_sha256):
 review_path = _ReviewPath(path)
 assert _review_hashlib.sha256(review_path.read_bytes()).hexdigest()==expected_sha256
 review = _review_json.loads(review_path.read_text())
 assert not review['missing_clauses']
 for source, fingerprint in review['source_sha256'].items():
  assert _review_hashlib.sha256(_ReviewPath(source).read_bytes()).hexdigest()==fingerprint
 for source, fingerprint in review['proof_source_sha256'].items():
  assert _review_hashlib.sha256(_ReviewPath(source).read_bytes()).hexdigest()==fingerprint
 for source, fingerprint in review.get('definition_dependency_source_sha256', {}).items():
  assert _review_hashlib.sha256(_ReviewPath(source).read_bytes()).hexdigest()==fingerprint
 for evidence in review['actual_standalone_evidence']:
  assert _review_hashlib.sha256(_ReviewPath(evidence['compiler_manifest']).read_bytes()).hexdigest()==evidence['compiler_manifest_sha256']
  raw = evidence.get('raw_execution_record', evidence)
  assert raw['exit_code']==0
  assert raw['source_sha256_before']==raw['source_sha256_after']
  assert _review_hashlib.sha256(_ReviewPath(raw['source']).read_bytes()).hexdigest()==raw['source_sha256_after']
  assert _review_hashlib.sha256(_ReviewPath(raw['log']).read_bytes()).hexdigest()==raw['log_sha256']
 inventory = _review_json.loads(_ReviewPath('book/coverage/inventory.json').read_text())
 live_exercises = {entry['key']:entry for entry in inventory['exercises']}
 live_units = {entry['key']:entry for entry in inventory['material_source_units']}
 exercise_reviews = review.get('exercises', [review] if 'exercise_key' in review else [])
 for exercise in exercise_reviews:
  key = exercise['exercise_key']
  assert live_exercises[key]['text_sha256']==exercise['exercise_text_sha256']
  assert not exercise.get('missing_clauses', [])
  clauses = exercise['reviewed_clauses']
  assert clauses and all(clause['status'] in ['approved','approved_precise_component'] and not clause['missing_clauses'] for clause in clauses)
  COMPLETE_EXERCISES[key] = [dict(
   statement_in_prose=clause['source_clause'], lean_declarations=clause['lean_declarations'],
   hypotheses=clause['hypotheses'],
   correspondence=clause.get('per_clause_reason',clause.get('reason',''))+' Exact independent whole review: '+path+'.') for clause in clauses]
 for unit in review['material_units']:
  key = unit['source_unit_key']
  assert live_units[key]['text_sha256']==unit['unit_text_sha256']
  assert live_units[key]['source_sha256']==unit['source_sha256']
  assert not unit['missing_clauses']
  if unit['material_status']=='proved':
   assert unit['review_status']=='approved_complete_source' and unit['lean_declarations']
   related_clauses = [clause for exercise in exercise_reviews for clause in exercise['reviewed_clauses']
     if set(clause['lean_declarations']) & set(unit['lean_declarations'])]
   hypotheses = unit.get('hypotheses', sorted({h for clause in related_clauses for h in clause['hypotheses']}))
   assert hypotheses
   REVIEWED_COMPLETE_MATERIAL[key] = [dict(
    statement_in_prose=live_units[key]['source_text'], lean_declarations=unit['lean_declarations'],
    hypotheses=hypotheses,
    correspondence=unit['per_unit_reason']+' Exact independent whole review: '+path+'.')]
  else:
   assert unit['material_status'] in ['not_a_formal_claim','not_formalizable']
   assert unit['review_status'] in ['approved_complete_source','approved_pedagogical_classification']
   assert not unit['lean_declarations']
   REVIEWED_NONFORMAL_MATERIAL[key] = unit['per_unit_reason']+' Exact independent whole review: '+path+'.'

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-convex-sets-b4a-source-review-v1.json',
 '56d28ae2b44a0936d542986d6bd645fc0e5e5670d41be4d33468d71b46c8b96a')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-rates-costs-0-6-source-review-v1.json',
 '88898c755cd5fe11a6f7b545619efee2b2d8d02b68cd9b9375648fc1b6df1ecc')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-parameterized-convex-b4b-source-review-v1.json',
 '1fc3cdb7ea74d8f2e4cda30f2137aad5622033d89f918e5c194698c8295bde44')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-extended-conjugate-b4c-source-review-v1.json',
 '0f9b8a50c732df3ba82584fdb51a484d9a1156ea89d71151426fd741b2534cef')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-two-conjugates-b4-source-review-v1.json',
 '350a42b04940a5d7c1211d4691e4a7e73b8e5746f968aa33472268445dc51083')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-norms-a1-source-review-v1.json',
 '2803a9c4abc66f751f30e8b189bb4a5419e1572bb2b5b580ac48f94769a909fd')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-polygon-lp-b7b-source-review-v1.json',
 'c305d150f3a5bf78325442f604ebbd8fc5d38fc6627392d7d049a0c39d355872')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-norm-material-source-review-v1.json',
 '578dd1f5b7f897481aed42c8cbad356e58a2ba2dfc80d1375f770da3652f0b0f')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-cholesky-family-a3-source-review-v1.json',
 'badcd849618949b1ba352f6f3e92f3a1026e72eb238a0c3a876800d221bc81db')

_load_independent_full_foundation_review(
 'book/coverage/checks/foundations-generalized-eigen-a7-source-review-v1.json',
 '72e91451206ca0a30aa71677960ebd5de713ef68497401be39cd08457f90fec0')
