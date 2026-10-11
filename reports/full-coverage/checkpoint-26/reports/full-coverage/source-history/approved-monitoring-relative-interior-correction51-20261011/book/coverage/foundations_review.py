"""Reviewed correspondences for the foundations ledger.

Pending source clauses retain their exact text and a mathematical gap category.
The category is a review aid, never a proof promotion. Only the explicit table
below can close a teaching source unit.
"""
import re

PREFIX='SafeLearning.'
def refs(group,*names):
    return [PREFIX+group+'.'+name for name in names]

EXTRA={
 'mb-ex-f1':refs('CompleteFoundationsTeaching','finite_square_classification','finiteSquare','squareDomain','squareCodomain'),
 'mb-ex-f8':refs('CompleteFoundationsTeaching','stabilized_reachFive'),
 'mb-ex-f9':refs('CompleteFoundationsTeaching','half_open_not_closed','half_open_counterexample_limit'),
 'mb-ex-p7':refs('CompleteFoundationsTeaching','contraction_unique_general'),
 'mb-ex-sequences-1':refs('CompleteFoundationsTeaching','sequence_initial_values'),
 'mb-ex-sequences-2':refs('CompleteFoundationsSeries','discounted_return_bound','discounted_tail_bound','constant_discounted_tail','half_discount_minimal_budget','half_discount_numbers'),
 'mb-ex-sequences-3':refs('CompleteFoundationsTeaching','all_time_excursion_card','finite_excursion_last_index'),
 'la-ex-norms-1':refs('CompleteFoundationsGeometry','cauchy_schwarz_general'),
 'la-ex-matrix-norms-2':refs('CompleteFoundationsGeometry','operator_product_bound'),
 'la-ex-matrix-norms-3':refs('CompleteFoundationsGeometry','neumann_series_general'),
 'la-ex-spectral-1':refs('CompleteFoundationsGeometry','symmetric_orthonormal_eigenbasis','symmetric_spectral_decomposition'),
 'la-ex-psd-1':refs('CompleteFoundationsGeometry','symmetric_psd_eigenvalues','symmetric_pd_eigenvalues'),
 'la-ex-functions-1':refs('CompleteFoundationsFunctionExamples','projection_integrals','constant_projection_characterization','projection_norms'),
 'la-ex-functions-2':refs('CompleteFoundationsFunctionExamples','affine_feature_kernel','affine_gram_quadratic','affine_gram_pd'),
 'la-ex-functions-3':refs('CompleteFoundationsFunctionExamples','affine_interpolation_unique','affine_gram_inverse','affine_interpolation_norm','affine_representer','affine_reproducing_bound','affine_not_uniformly_bounded','affine_compact_uniform_bound'),
 'opt-ex-derivatives-1':refs('CompleteFoundationsOptimization','quadratic_frechet_derivative','quadratic_hessian_partials','derivative_numerical_values','quadratic_vertical_remainder'),
 'opt-ex-matrix-calculus-1':refs('CompleteFoundationsOptimization','least_squares_frechet_derivative'),
 'opt-ex-convexity-2':refs('CompleteFoundationsOptimization','parameter_quadratic_convex_iff','parameter_strict_curvature_iff'),
 'opt-ex-convexity-3':refs('CompleteFoundationsOptimization','restricted_square_conjugate_supremum'),
 'opt-ex-constraints-1':refs('CompleteFoundationsOptimization','constrained_scalar_unique','scalar_kkt_certificates'),
 'opt-ex-constraints-2':refs('CompleteFoundationsOptimization','halfspace_unique_optimum','halfspace_kkt_certificate'),
 'opt-ex-constraints-3':refs('CompleteFoundationsOptimization','penalty_unique_optimum','approximate_kkt_minimal_tolerance'),
 'opt-ex-programs-1':refs('CompleteFoundationsOptimization','qp_unique_optimum'),
 'opt-ex-minmax-2':refs('CompleteFoundationsOptimization','finite_controller_margins'),
}

# Fully reviewed source units with exact local proof correspondence. A prose
# instruction surrounding the stated mathematics is not promoted to a theorem.
FULL={
 'primer-basics.html::node-79':refs('CompleteFoundationsTeaching','arithmetic_refresh'),
 'primer-basics.html::node-81':refs('CompleteFoundationsTeaching','arithmetic_refresh','reciprocal_decreases'),
 'primer-basics.html::node-85':refs('CompleteFoundationsTeaching','elementary_equations'),
 'primer-basics.html::node-87':refs('CompleteFoundationsTeaching','arithmetic_refresh','elementary_equations'),
 'primer-basics.html::node-98':refs('CompleteFoundationsTeaching','disc_and_box'),
 'primer-basics.html::node-122':refs('CompleteFoundationsTeaching','logical_connectives'),
 'primer-basics.html::node-143':refs('CompleteFoundationsTeaching','no_largest_real')+refs('PrimersFoundations','shared_input_implies_feedback'),
 'primer-basics.html::node-155':refs('CompleteFoundationsTeaching','viability_complement'),
 'primer-basics.html::node-390':refs('CompleteFoundationsTeaching','contraction_unique_general','banach_first_error_bound')+refs('PrimersFoundations','banach_unique_exists','banach_apriori_bound'),
 'primer-basics.html::node-636':refs('CompleteFoundationsFinite','finite_orbit_collision','orbit_reduce_at_collision','finite_orbit_early_occurrence','finite_state_check_all_time'),
 'primer-basics.html::node-639':refs('CompleteFoundationsFinite','finite_orbit_collision','orbit_reduce_at_collision','finite_orbit_early_occurrence'),
 'primer-basics.html::node-1479':refs('CompleteFoundationsBook','chamber_worked_commands'),
 'primer-basics.html::node-1484':refs('CompleteFoundationsBook','chamber_no_fixed_command'),
 'primer-linalg.html::node-133':refs('CompleteFoundationsGeometry','cauchy_schwarz_general','cauchy_schwarz_equality_including_zero'),
 'primer-linalg.html::node-138':refs('CompleteFoundationsGeometry','linear_ball_upper_bound','linear_ball_attainment'),
 'primer-linalg.html::node-143':refs('CompleteFoundationsGeometry','am_gm_sqrt','reciprocal_am_gm','scalar_young_absolute'),
 'primer-linalg.html::node-318':refs('CompleteFoundationsGeometry','operator_product_bound','frobenius_submultiplicativity','lipschitz_composition_general')+refs('CompleteFoundationsTeaching','norm_power_bound'),
 'primer-linalg.html::node-324':refs('CompleteFoundationsGeometry','neumann_series_general'),
 'primer-linalg.html::node-410':refs('CompleteFoundationsGeometry','symmetric_orthonormal_eigenbasis','symmetric_spectral_decomposition'),
 'primer-linalg.html::node-1280':refs('CompleteFoundationsBook','nearparallel_error_example'),
 'primer-optimization.html::node-82':refs('CompleteFoundationsOptimization','constrained_scalar_unique'),
}
# node-82 describes the DIFFERENT running example centred at 2, so the centred-at-3
# exercise theorem must never close it. Remove it until an exact wrapper exists.
FULL.pop('primer-optimization.html::node-82')
FULL.pop('primer-linalg.html::node-318')

ATOMS={
 'primer-basics.html::node-100':[
  ('Indexed De Morgan laws hold for arbitrary indexed families of sets.',refs('CompleteFoundationsTeaching','indexed_deMorgan'))],
 'primer-basics.html::node-335':[
  ('Preimages preserve intersection, union and complement; images preserve union and satisfy the intersection inclusion, which can be strict for squaring at -1 and 1.',refs('PrimersFoundations','preimage_intersection','preimage_union','preimage_complement','image_union_preserved')+refs('CompleteFoundationsTeaching','image_intersection_subset','image_intersection_counterexample'))],
 'primer-basics.html::node-347':[
  ('The affine function 2x+1 is a bijection on the reals.',refs('CompleteFoundationsTeaching','affine_bijection'))],
 'primer-basics.html::node-379':[
  ('A contracting self-map of a nonempty complete metric space has a unique fixed point, all iterates converge, and both quoted geometric error bounds hold.',refs('PrimersFoundations','banach_unique_exists','banach_iterates_converge','banach_apriori_bound')+refs('CompleteFoundationsTeaching','banach_first_error_bound'))],
 'primer-basics.html::node-632':[
  ('A norm bounded by every positive real is zero.',refs('CompleteFoundationsTeaching','norm_arbitrarily_small'))],
 'primer-basics.html::node-831':[
  ('Limits preserve the stated sum/product/quotient operations with nonzero denominator limit, and composition by a function continuous at the limit.',refs('CompleteFoundationsTeaching','limit_arithmetic','continuous_limits'))],
 'primer-basics.html::node-835':[
  ('Bounded monotone real sequences tend to their supremum, and bounded antitone sequences tend to their infimum.',refs('CompleteFoundationsTeaching','monotone_bounded_convergence','antitone_bounded_convergence'))],
 'primer-basics.html::node-850':[
  ('The geometric series converges for 0<=gamma<1; bounded real rewards give an absolutely convergent discounted return and the quoted absolute return/tail bounds.',refs('CompleteFoundationsSeries','geometric_hasSum','discounted_return_bound','discounted_tail_bound'))],
 'primer-basics.html::node-863':[
  ('In a complete normed unital ring with norm one identity, norm(A)<1 implies invertibility of 1-A, the convergent Neumann expansion and the inverse-norm bound.',refs('CompleteFoundationsGeometry','neumann_series_general'))],
 'primer-basics.html::node-902':[
  ('For every real x, 1+x<=exp(x); for positive x, log(x)<=x-1.',refs('CompleteFoundationsTeaching','exponential_tangent','logarithm_tangent'))],
 'primer-basics.html::node-1145':[
  ('A continuous real function on a nonempty compact set attains its minimum and maximum.',refs('PrimersFoundations','weierstrass_minimum')+refs('CompleteFoundationsTeaching','weierstrass_maximum'))],
 'primer-basics.html::node-1150':[
  ('A continuous strictly positive function on a compact set has a uniform strictly positive lower bound.',refs('CompleteFoundationsTeaching','compact_positive_margin'))],
 'primer-basics.html::node-1167':[
  ('A continuous function on a compact uniform-space domain is uniformly continuous there.',refs('CompleteFoundationsTeaching','heine_cantor'))],
 'primer-basics.html::node-1169':[
  ('An L-Lipschitz function with margin m on a tau-net has margin at least m-L*tau everywhere on the covered set.',refs('CompleteFoundationsTeaching','lipschitz_net_margin'))],
 'primer-basics.html::node-1472':[
  ('The explicit feedback -0.18*x belongs to the actuator interval and preserves the chamber interval against every disturbance in [0,0.4].',refs('CompleteFoundationsBook','chamber_nominal_feedback'))],
 'primer-basics.html::node-1483':[
  ('For every state and every permitted disturbance the feedback -0.18*x has admissible command and safe successor.',refs('CompleteFoundationsBook','chamber_nominal_feedback'))],
 'primer-basics.html::node-1498':[
  ('The explicit bound 0.05+0.75*0.6^n meets 0.06 exactly for n>=9.',refs('CompleteFoundationsBook','worked_error_budget'))],
 'primer-linalg.html::node-147':[
  ('Norm zero detection, real homogeneity and triangle inequality hold in every normed real vector space.',refs('CompleteFoundationsGeometry','norm_vanishes_iff','norm_scale','norm_triangle'))],
 'primer-linalg.html::node-164':[
  ('The reverse triangle inequality holds for every norm.',refs('CompleteFoundationsGeometry','reverse_triangle_general'))],
 'primer-linalg.html::node-202':[
  ('For a positive Lipschitz constant, a point with positive value c certifies its entire closed metric ball of radius c/L.',refs('CompleteFoundationsGeometry','positive_lipschitz_certified_ball')),
  ('With zero Lipschitz constant the function is constant on the entire domain.',refs('CompleteBookProjects','zero_lipschitz_constant'))],
 'primer-linalg.html::node-302':[
  ('The operator norm bounds every input and is the least nonnegative bound satisfying that inequality.',refs('CompleteFoundationsGeometry','operator_norm_bound','operator_norm_is_least'))],
 'primer-linalg.html::node-315':[
  ('The Frobenius norm is the square root of the sum of squared real matrix entries.',refs('CompleteFoundationsGeometry','frobenius_norm_formula'))],
 'primer-linalg.html::node-318':[
  ('Induced operator norms and the Frobenius norm are submultiplicative; matrix powers obey the corresponding power-norm bound.',refs('CompleteFoundationsGeometry','operator_product_bound','frobenius_submultiplicativity')+refs('CompleteFoundationsTeaching','norm_power_bound'))],
 'primer-linalg.html::node-532':[
  ('A symmetric real matrix is PSD iff its eigenvalues are nonnegative, and PD iff its eigenvalues are positive.',refs('CompleteFoundationsGeometry','symmetric_psd_eigenvalues','symmetric_pd_eigenvalues'))],
 'primer-linalg.html::node-870':[
  ('For a real symmetric matrix the determinant is the eigenvalue product; a PD matrix has positive determinant.',refs('CompleteFoundationsGeometry','determinant_eigenvalue_product','positive_definite_determinant'))],
 'primer-linalg.html::node-884':[
  ('For a real symmetric matrix the trace is the sum of eigenvalues.',refs('CompleteFoundationsGeometry','trace_eigenvalue_sum'))],
 'primer-linalg.html::node-1097':[
  ('The actual squared L2 integral of x^n on [0,1] is 1/(2n+1).',refs('CompleteFoundationsFunctionExamples','polynomial_l2_norm'))],
 'primer-linalg.html::node-1102':[
  ('Every bounded real linear functional on a complete real inner-product space is inner product with a unique vector.',refs('CompleteFoundationsFunctionExamples','riesz_representation'))],
 'primer-linalg.html::node-1107':[
  ('Every finite feature Gram matrix is PSD, with coefficient quadratic form equal to the squared norm of the weighted feature sum.',refs('CompleteFoundationsFeatures','feature_gram_psd','feature_norm_quadratic'))],
 'primer-linalg.html::node-1113':[
  ('The explicit polynomial features (1,sqrt(2)*x,x^2) have kernel (1+x*y)^2.',refs('CompleteFoundationsFunctionExamples','polynomial_feature_kernel'))],
 'primer-linalg.html::node-1118':[
  ('Evaluation of an inner-product feature function is bounded by its coefficient norm times sqrt(kernel diagonal).',refs('CompleteFoundationsFeatures','reproducing_evaluation_bound','feature_norm_quadratic'))],
 'primer-linalg.html::node-1123':[
  ('An invertible finite Gram matrix gives an interpolating feature sum, and the interpolant is uniquely minimum in norm with an exact Pythagorean norm decomposition.',refs('CompleteFoundationsFeatures','invertible_gram_interpolant','minimum_norm_interpolant','interpolant_norm_data_identity'))],
 'primer-optimization.html::node-457':[
  ('The positive-constant metric ball certificate and zero-constant whole-domain certificate are valid under the corrected hypotheses.',refs('CompleteFoundationsGeometry','positive_lipschitz_certified_ball')+refs('CompleteBookProjects','zero_lipschitz_lower_certificate'))],
 'primer-optimization.html::node-468':[
  ('Composing Lipschitz maps multiplies their valid Lipschitz constants.',refs('CompleteFoundationsGeometry','lipschitz_composition_general'))],
 'primer-optimization.html::node-484':[
  ('The tau-net margin loss is at most L*tau.',refs('CompleteFoundationsTeaching','lipschitz_net_margin'))],
 'primer-optimization.html::node-679':[
  ('The displayed parameter quadratic is convex on the real plane iff |a|<=2, and has positive uniform lower Hessian curvature iff |a|<2.',refs('CompleteFoundationsOptimization','parameter_quadratic_convex_iff','parameter_strict_curvature_iff'))],
 'primer-optimization.html::node-703':[
  ('The restricted translated scalar quadratic has the quoted piecewise conjugate as the actual least upper bound.',refs('CompleteFoundationsOptimization','translated_square_conjugate_supremum'))],
 'primer-optimization.html::node-1382':[
  ('Continuous real functions attain both extrema on a nonempty compact set.',refs('PrimersFoundations','weierstrass_minimum')+refs('CompleteFoundationsTeaching','weierstrass_maximum'))],
}

NONFORMAL={
 'primer-basics.html':{22,53,148,618,621,1266,1408,1471,1473,1487,1489,1493,1504},
 'primer-linalg.html':{64,92,301,447,604,614,1207,1255,1256},
 'primer-optimization.html':{41,242,250,255,510,519,525,717,729,745,967,1161,1168,1287,1372,1411,1422,1431,1495,1536,1550,1587},
}
# Some numerical-method prose also contains genuine mathematical assertions, so
# it must remain pending rather than disappear under the empirical label.
for page,nodes in [('primer-linalg.html',{447,604,614,1207}),('primer-optimization.html',{1287,1495,1536})]:
    NONFORMAL[page]-=nodes
NONFORMAL['primer-basics.html']-={148,621}
NONFORMAL['primer-optimization.html']-={967,1587}

TOPICS={
 'primer-basics.html':[(173,'logic, finite arithmetic and quantifiers','exact finite examples, every quantified necessity/converse, and the stated probability illustration'),(450,'functions, contractions and monotone set iteration','declared domains/codomains, exact images, counterexamples, finite-set stabilization and least/greatest fixed-point claims'),(651,'proof patterns and invariant trajectories','the exact modeled certificate, all-time induction and each specific counterexample'),(922,'limits, series and convergence rates','the exact limits, actual sums/integrals/expectations, interchange hypotheses, nonattainment and certified numerical enclosures'),(1036,'suprema, extended values and measure-zero assertions','actual least-upper/greatest-lower bounds, all extended-value edge cases, limsup/liminf and measure-theoretic conclusions'),(1206,'topology, compactness and Lyapunov convergence','all topology equivalences and geometric examples, coercive attainment, the complete compactness/Lyapunov convergence argument, connectedness and lower-semicontinuity assertions'),(1325,'asymptotic rates and computational complexity','actual asymptotic objects, exact iteration/sample thresholds, operation counts under specified computational models and formal complexity definitions'),(1453,'interactive numerical illustrations','rigorous numerical enclosures and the claimed qualitative dynamics for the exact displayed maps, rather than observed finite simulation'),(10000,'chamber and numerical-error models','the exact worked command/interval calculations, all-time witness feedback, geometric error envelope, logarithmic threshold equivalence and finite/error-floor claims')],
 'primer-linalg.html':[(123,'elementary matrices and coordinates','all displayed matrix products, exact rank/nullspace/range classifications, invertibility and normalized eigenvector calculations'),(209,'inner products, norms, metrics and duality','all p-norm/dual-norm comparisons and attainments, distance/covering geometry, kernel invariance and numerical enclosures'),(332,'induced matrix norms and Neumann series','actual operator extrema and exact row/column/mixed norm formulas, Frobenius/spectral rank inequalities, stochastic resolvent identities and zonotope geometry'),(447,'spectral theory and eigenvalue algorithms','Rayleigh extrema, spectral-radius claims, complex variants, exact numerical eigenbases and Jacobi convergence under the pivot rule'),(622,'PSD order, ellipsoids and factorization','all definiteness equivalences, Cholesky existence/uniqueness and recursion, order inversion, weighted supports, ellipsoid geometry/volume and exact GP solve identities'),(758,'SVD, pseudoinverses and conditioning','the full decomposition, singular-value extrema, least-squares/range optimality, approximation/condition bounds, power convergence and polar-factor optimization'),(897,'blocks, Schur complements, determinants and trace','general block identities and all singular range conditions, Woodbury/Fredholm identities, trace/probability interpretations and geometric volume claims'),(1012,'structured matrices and transforms','general orthogonal/skew/Cayley conclusions including missing eigenvalues, Toeplitz/Fourier limits, Kronecker/vec identities and exact numerical examples'),(1133,'Hilbert spaces, kernels and RKHSs','L2 quotient/norm bridges and integral examples, infinite-dimensional completeness/basis claims, Moore-Aronszajn converse, RKHS completion, singular interpolation, Mercer/Fourier/MMD theorems with their hypotheses'),(1236,'matrix explorer illustrations','the exact norm/eigenvalue/iteration computations and geometric classifications behind the numerical captions'),(10000,'measurement reconstruction and least squares','the exact matrix reconstructions, spectral/condition-number sensitivity claims, residual geometry and original-model uniqueness including all displayed approximations')],
 'primer-optimization.html':[(166,'calculus and optimization recap','the actual derivatives/integrals, finite probability/KL statements, domain conditions and exact constrained minima'),(255,'derivatives, chain rules and Taylor bounds','actual Frechet/curve derivatives, differentiability counterexamples, Hessian conditions, general remainder estimates and certified numerical values'),(373,'matrix differentials and sensitivity','general actual matrix derivatives, implicit solution derivatives, residual/Hessian calculations and log-determinant expansions with admissible domains'),(525,'Lipschitz calculus and finite-grid certificates','sharp constants and counterexamples, the full derivative-to-Lipschitz equivalence, arithmetic/reciprocal rules, model-error recurrences, covering geometry, smoothness and Rademacher assertions'),(745,'convexity, duality and conjugates','all convex-set/function equivalences and closure rules, strong-convexity objects and bounds, subgradient/Jensen equality conditions, matrix-convexity, Fenchel-Moreau and Bregman identities'),(852,'descent, SGD, Newton and search algorithms','algorithm recurrences with actual convergence/divergence, complete rate proofs, conditional stochastic assumptions, Newton/backtracking guarantees and certified finite examples'),(1168,'constraints, KKT, projections and penalties','complete constraint qualifications/necessity, cone and projection characterizations, exact active-set/global examples, sensitivity, penalty/barrier rates and central-path conclusions'),(1289,'mathematical programming and computational claims','formal feasible/objective translations, global LP/QP/SOCP conclusions, recession/vertex edge cases, exact filter geometry and complexity/relaxation assertions'),(1431,'optimal values, suprema and minimax','actual optimizer sets and nonattainment, full minmax/saddle extrema, general minimax hypotheses and duality/strategy claims'),(1537,'optimization explorer illustrations','rigorous displayed trajectories/reference solutions, conditioning and penalty/barrier numerical conclusions'),(10000,'flow-allocation and nonlinear-clearance models','actual strict-convexity/compact-feasibility claims, unique global objectives and sensitivity, all active-set cases, tangent/remainder and original nonlinear optimality certificates')],
}

def topic(page,node):
    return next((name,gap) for end,name,gap in TOPICS[page] if node<=end)

def clauses(text):
    pieces=[];start=0;math=False
    for i,c in enumerate(text):
        if c=='$' and (i==0 or text[i-1]!='\\'):math=not math
        if not math and c in '.;':
            decimal=c=='.' and i>0 and i+1<len(text) and text[i-1].isdigit() and text[i+1].isdigit()
            if not decimal and i-start>30:
                pieces.append(text[start:i+1].strip());start=i+1
    if text[start:].strip():pieces.append(text[start:].strip())
    return pieces or [text]
