"""Literal-clause routes for the seven independently reviewed qualifier families.

This is an owner mapping, not a mathematical review or compilation receipt.
Each assumption is the domain of the named actual theorem(s).  Historical peers
remain the authorities for their original decisions.
"""

PREFIX = 'SafeLearning.'
B = PREFIX + 'CompleteFoundationsRegularNewtonAndRateInterpretation31.'
R = PREFIX + 'CompleteFoundationsConvergenceRates.'
Q = PREFIX + 'CompleteFoundationsConvergenceRateExamples.'
N = PREFIX + 'CompleteFoundationsCommonMixedInducedNormFormulas32.'
Z = PREFIX + 'CompleteFoundationsBoxImageZonotope32.'
C = PREFIX + 'CompleteFoundationsCubeRadiusAndNetMargin32.'
G = PREFIX + 'CompleteFoundationsCenteredCubeNetsWhole30.'
S = PREFIX + 'CompleteFoundationsSignedDistanceHausdorff32.'
P = PREFIX + 'CompleteFoundationsPositiveSubunitPNorm32.'
L = PREFIX + 'CompleteFoundationsPlanarQuadraticLevelSets32.'


def route(clause, assumptions, *declarations):
    return {'source_clause': clause, 'hypotheses': assumptions,
            'lean_declarations': list(declarations),
            'classification': 'reviewed_mathematical_subclaim'}


BASICS_DEFINITION = [
    route('Nonnegative errors with the one-step geometric inequality have every prefix bounded by q^k e0 and converge to zero.',
          ['error:N->R; all errors nonnegative; 0<=q<1; error(n+1)<=q*error(n) for every n. The source restricts 0<q<1.'],
          R+'actual_one_step_geometric_error_bound_gives_every_natural_prefix_bound',
          R+'actual_nonnegative_geometrically_bounded_errors_converge_to_zero'),
    route('Exact positive reciprocal-power errors C/k^p converge and are slower than every positive geometric BigO rate.',
          ['C>0, p>0, 0<q<1; source indices k>=1; limits are atTop.'],
          B+'actual_positive_scaled_reciprocal_errors_converge_and_have_no_geometric_big_o_bound'),
    route('A polynomial upper bound alone does not establish the sublinear classification.',
          ['The exact counterexample is the identically zero error sequence, bounded by (n+1)^(-1) and geometric BigO.'],
          B+'actual_polynomial_upper_bound_alone_does_not_classify_an_error_as_sublinear'),
    route('The quadratic convergence convention is the positive-constant inequality; sufficiently small nonnegative errors with that recurrence converge.',
          ['C>0; errors nonnegative; error(n+1)<=C*error(n)^2 for every n; C*error(0)<1 supplies the sufficient small-initial-error domain.'],
          Q+'actual_quadratic_error_recursion_gives_the_double_exponential_prefix_bound',
          Q+'actual_quadratic_errors_converge_in_the_true_small_initial_error_domain'),
    route('Scalar Newton at a regular root of a C2 function has an invariant local domain, a positive quadratic constant and convergent actual iterates.',
          ['f:R->R is ContDiff R 2; f(root)=0; deriv f root !=0. The theorem derives radius>0 and coefficient>0 and assumes only |initial-root|<=radius for the iterates.'],
          B+'actual_C2_and_a_nonzero_root_derivative_supply_a_local_quadratic_bound',
          B+'actual_C2_regular_newton_has_an_invariant_quadratic_neighborhood_and_converges'),
]

NORM_TABLE = [
    route('The induced 1 and infinity norms are the largest absolute column and row sums.',
          ['Arbitrary finite real rectangular matrix; the simultaneous source table assumes both row and column index types nonempty (m,n>=1).'],
          N+'actual_one_induced_norm_is_the_largest_absolute_column_sum',
          N+'actual_infinity_induced_norm_is_the_largest_absolute_row_sum'),
    route('The spectral norm is the largest actual singular value and square root of the largest actual Gram eigenvalue.',
          ['Finite real matrix with nonempty input index type; the source table supplies m,n>=1. Gram eigenvalues/nonnegativity and genuine singular-value correspondence are derived.'],
          N+'actual_Euclidean_image_norm_square_is_the_Gram_quadratic_form',
          N+'actual_largest_Gram_eigenvalue_is_nonnegative',
          N+'actual_spectral_induced_norm_is_the_square_root_of_the_largest_Gram_eigenvalue',
          N+'actual_every_Gram_eigenvalue_is_the_nonnegative_square_of_a_unit_vector_image',
          N+'actual_spectral_norm_is_the_largest_square_root_of_the_actual_Gram_eigenvalues',
          N+'actual_spectral_induced_norm_is_the_first_actual_singular_value',
          N+'actual_spectral_induced_norm_is_the_greatest_actual_singular_value'),
    route('For every conjugate p,q, the p-to-infinity norm is the largest row q-norm; 1-to-p is the largest column p-norm.',
          ['p,q:R>=0 extended, p,q>=1, ENNReal.HolderConjugate p q; endpoints 1 and infinity included. Arbitrary finite matrix; row/column nonemptiness follows from the new m,n>=1 table prefix.'],
          N+'actual_matrix_action_is_the_sum_of_its_input_scaled_columns',
          N+'actual_one_to_p_column_bound_for_every_input',
          N+'actual_one_to_p_induced_norm_is_the_largest_actual_column_norm',
          N+'actual_conjugate_p_to_infinity_row_bound_for_every_input',
          N+'actual_all_conjugate_p_to_infinity_induced_norm_is_the_largest_row_q_norm'),
    route('The displayed mixed specializations are the maximum absolute entry and largest Euclidean row length.',
          ['Arbitrary finite real matrix with m,n>=1; sourcePNorm and sourceMatrixMap are the actual PiLp norms and linear map.'],
          N+'actual_one_to_infinity_induced_norm_is_the_largest_absolute_entry',
          N+'actual_two_to_infinity_induced_norm_is_the_largest_Euclidean_row_length'),
]

NORM_PROOF = [
    route('The row triangle/Holder and column decomposition bounds hold for every actual input and their bounds are attained.',
          ['m,n>=1 inherited from preceding qualified table; p,q>=1 with Holder conjugacy. The zero-row sign vector may have norm zero; the dual-ball attainer has norm<=1, and the zero operator has norm0.'],
          N+'actual_matrix_action_is_the_sum_of_its_input_scaled_columns',
          N+'actual_one_to_p_column_bound_for_every_input',
          N+'actual_one_to_p_induced_norm_is_the_largest_actual_column_norm',
          N+'actual_conjugate_p_to_infinity_row_bound_for_every_input',
          N+'actual_all_conjugate_p_to_infinity_induced_norm_is_the_largest_row_q_norm',
          N+'actual_one_induced_norm_is_the_largest_absolute_column_sum',
          N+'actual_infinity_induced_norm_is_the_largest_absolute_row_sum'),
    route('For the printed matrix [[2,2],[-1,1]], the ordinary and mixed norms are 3,4,2,sqrt8, with infinity norm attained at (1,1).',
          ['The source fixture is exactly actualRunningMatrix=[[2,2],[-1,1]], not an earlier distinct two-by-two fixture.'],
          N+'actual_running_matrix_one_and_infinity_induced_norms_and_infinity_attainer',
          N+'actual_running_matrix_mixed_one_to_infinity_and_two_to_infinity_norms'),
    route('Its spectral norm is 2 sqrt2, rigorously rounds to2.83, and is the longest semi-axis of the full unit-circle image ellipse.',
          ['Exact printed real2x2 matrix; strict rounding error<0.005; ellipse equation equivalent for every real c,s and all actual unit-circle images.'],
          N+'actual_running_matrix_spectral_norm_is_twice_sqrt_two',
          N+'actual_running_matrix_spectral_rounding_is_the_printed_two_point_eight_three',
          N+'actual_running_unit_circle_image_is_the_full_ellipse_with_the_printed_spectral_axis'),
]

ZONOTOPE = [
    route('The actual uniform infinity ball image is exactly the finite Minkowski sum of epsilon-scaled geometric column segments.',
          ['Finite input index set, arbitrary real rectangular W; epsilon>0 in the source. The image/segment identities hold for epsilon>=0 and derive both set-inclusion directions.'],
          Z+'actual_nonnegative_sup_norm_ball_is_the_uniform_input_box',
          Z+'actual_matrix_action_is_the_sum_of_its_scaled_column_vectors',
          Z+'actual_uniform_box_image_is_exactly_the_sum_of_all_column_segments',
          Z+'actual_column_segment_sum_is_the_finite_Minkowski_sum',
          Z+'actual_nonnegative_column_segment_is_epsilon_times_the_unit_segment',
          Z+'actual_column_segment_is_the_geometric_closed_segment_between_its_endpoints'),
    route('An invertible two-by-two image is a nondegenerate parallelogram.',
          ['Real2x2 W with det W !=0; epsilon>0 ensures scaled column generators remain independent.'],
          Z+'actual_invertible_two_by_two_box_image_has_two_independent_generators',
          Z+'actual_positive_radius_invertible_parallelogram_generators_remain_independent'),
    route('Both coordinate extrema are attained; the tightest enclosing axis-aligned box has half-widths epsilon times row1-norm, as retained by interval bound propagation.',
          ['Finite real W and epsilon>=0; arbitrary enclosing lower/upper endpoint vectors. Source epsilon>0 satisfies the domain; containment iff every endpoint bounds the derived extrema.'],
          Z+'actual_uniform_box_has_attained_exact_coordinate_half_widths',
          Z+'actual_uniform_box_half_width_is_epsilon_times_the_row_one_norm',
          Z+'actual_tightest_axis_aligned_enclosing_box_has_exact_printed_half_widths'),
    route('The printed W=[[1,1],[1,-1]], epsilon1 image is the full rotated square, with four stated corners and genuine Lebesgue area8 inside the area16 box.',
          ['Exact printed2x2 W and epsilon=1; all-input Euclidean squared norm identity is twice the input squared norm; volume is the actual finite-dimensional Lebesgue measure.'],
          Z+'actual_running_box_map_is_a_scaled_Euclidean_isometry',
          Z+'actual_running_full_box_image_is_the_printed_square_with_exact_areas'),
]

CUBE = [
    route('Every side-s cube about its actual center lies in the Euclidean ball of half-diagonal radius, including isometric images.',
          ['s>=0; finite coordinates; source d>=1. Coordinate deviations<=s/2; isometric image additionally has Isometry e.'],
          C+'actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball',
          C+'actual_cube_corner_attains_the_half_diagonal_radius',
          C+'actual_isometric_cube_image_has_the_same_half_diagonal_ball'),
    route('The centered ceiling grid contains exactly m^d points, covers the unit cube by radius-tau balls and gives the printed net.',
          ['d>=1 and tau>0; m=Nat.ceil(sqrt(d)/(2*tau)); actual center coordinates (k+1/2)/m; coverage and finite cardinality are derived.'],
          C+'actual_printed_ceiling_grid_cardinality_coverage_and_full_margin_compose',
          G+'actual_centered_grid_cardinality', G+'actual_centered_grid_covers',
          G+'actual_ceiling_cube_net_and_count'),
    route('The covering number is the least finite ball count even when centers are permitted anywhere in the ambient space.',
          ['Finite-dimensional Euclidean unit cube and tau>0. Actual coordinate clipping maps any ambient finite cover to an in-cube net with no larger cardinality.'],
          C+'actual_ambient_center_projection_lies_inside_the_unit_cube',
          C+'actual_center_projection_never_increases_distance_to_any_cube_point',
          C+'actual_any_ambient_finite_cover_has_an_in_cube_cover_with_no_more_centers',
          C+'actual_least_covering_number_also_minimizes_over_all_ambient_centered_balls'),
    route('At tau0.1 the construction uses64 balls in dimension2 and16^10=1099511627776, rounded about1.1e12, in dimension10.',
          ['These are construction counts and covering-number upper bounds; no claim that the counts are minimal. Exact tau=1/10.'],
          G+'actual_source_two_dimensional_ceiling', G+'actual_source_ten_dimensional_ceiling',
          G+'actual_source_centered_counts_and_rounded_trillion'),
    route('A sampled lower margin m0 transfers to every domain point as m0-L*tau.',
          ['Pseudometric domain D, finite domain-contained tau-net Z, L>=0, LipschitzOnWith L f D, and f(z)>=m0 for every net point.'],
          C+'actual_general_finite_net_transfers_every_sampled_lower_margin',
          C+'actual_printed_ceiling_grid_cardinality_coverage_and_full_margin_compose'),
]

SIGNED = [
    route('Signed distance equals distance to C outside and minus distance to the complement inside, with zero exactly at the boundary.',
          ['Metric space; C closed and nonempty with nonempty complement. Actual signedDistance=infDist(x,C)-infDist(x,C complement).'],
          S+'actual_signed_distance_has_the_printed_two_sides',
          S+'actual_signed_distance_zero_iff_boundary_for_nonempty_proper_closed_sets'),
    route('The safe-side-positive convention negates the sign; strict and nonstrict positive sign sets differ exactly on the boundary.',
          ['Same nonempty proper closed-set domain; safeSidePositiveDistance=-signedDistance; positivity inside means membership in interior C. This is a sign convention, with no trajectory safety theorem inferred.'],
          S+'actual_safe_side_positive_convention_has_the_opposite_sign',
          S+'actual_strict_and_nonstrict_sign_sets_differ_exactly_on_boundary'),
    route('For nonempty compact sets the actual Hausdorff distance is the maximum of both directed distance suprema.',
          ['A,B nonempty compact subsets of a metric space. Real finiteness and supremum boundedness are derived from compactness/nonemptiness.'],
          S+'actual_nonempty_compact_Hausdorff_distance_is_the_printed_maximum_of_two_suprema'),
    route('The exact interval Hausdorff example dH([0,1],[0,2]) equals1.',
          ['Ordinary real closed intervals; attained endpoint distance1 and the full upper bound are derived.'],
          S+'actual_interval_distance_two_to_zero_one_is_one',
          S+'actual_printed_interval_Hausdorff_distance_is_one'),
]

POSITIVE_P = [
    route('In dimensions at least2, every positive exponent below1 violates the triangle inequality.',
          ['Finite decidable nontrivial real coordinate index set; 0<p<1; powerQuasiNorm=(sum abs(x_i)^p)^(1/p).'],
          P+'actual_coordinate_unit_has_power_quasinorm_one',
          P+'actual_two_distinct_units_have_power_quasinorm_two_to_inverse_p',
          P+'actual_every_positive_subunit_exponent_fails_the_triangle_inequality'),
    route('The printed p=1/2 vectors have values4 versus1+1=2.',
          ['Exactly Fin2 real coordinates and exponent1/2.'],
          P+'actual_printed_half_exponent_values_are_four_versus_one_plus_one'),
    {'source_clause': 'Module11 norm choices and source-paper attribution, plus the instruction to check the norm of a constant.',
     'hypotheses': ['The cited peer separately verified the exact Berkenkamp1-norm and Hertneck input-infinity convention; Euclidean state norms are the current Module11 presentation convention. No full algorithm result or whole Module11 approval follows.'],
     'lean_declarations': [], 'classification': 'reviewed_factual_attribution_and_pedagogical_instruction',
     'evidence_scope': 'The independent PositiveSubunitP5 whole peer and cumulative review preserve the exact source-reference assessment; this context is not an additional Lean proposition.'},
]

PLANAR = [
    route('The positive-entry printed matrix is indefinite, while the printed singular PSD matrix has form(x1-x2)^2.',
          ['Exact real matrices [[1,2],[2,1]] and [[1,-1],[-1,1]]; explicit positive/negative witnesses, nonzero/determinant and PSD properties are derived.'],
          L+'actual_positive_entry_example_is_indefinite',
          L+'actual_singular_PSD_example_has_the_printed_form_and_two_parallel_lines'),
    route('A finite real diagonal matrix is PSD iff every diagonal entry is nonnegative.',
          ['Arbitrary finite real diagonal matrix, including empty index types.'],
          PREFIX+'CompleteFoundationsQuadraticForms.real_diagonal_psd_iff'),
    route('In the plane PD one-level sets are ellipses in actual orthogonal coordinates.',
          ['Real symmetric2x2 P with primitive positive-definite predicate. Actual eigenvector matrix is orthogonal, invertible and norm-preserving; semiaxes positivity is derived.'],
          L+'actual_spectral_coordinate_change_is_orthogonal_invertible_and_norm_preserving',
          L+'actual_every_planar_PD_one_level_is_an_ellipse_in_orthogonal_coordinates'),
    route('In the plane a nonzero singular PSD matrix has exactly two distinct parallel one-level lines.',
          ['Real symmetric2x2 P, PSD, P!=0 and det P=0. The actual two eigenvalues are one positive and one zero; no rank conclusion is assumed.'],
          L+'actual_nonzero_singular_planar_PSD_one_level_is_two_parallel_lines'),
    route('In the plane indefinite one-level sets are hyperbolas in actual orthogonal coordinates; the zero matrix one-level set is empty.',
          ['Real symmetric2x2 primitive indefinite P has witnesses of both signs. The exceptional zero matrix is treated separately; no higher-dimensional conic classification is asserted.'],
          L+'actual_every_planar_indefinite_one_level_is_a_hyperbola_in_orthogonal_coordinates',
          L+'actual_zero_PSD_matrix_has_empty_one_level'),
]

NODE922_COMPONENT = [
    route('The logarithmic geometric-envelope cutoff is exact for the envelope and sufficient for every bounded actual error; faster errors can reach tolerance earlier.',
          ['0<q<1; initial>0; epsilon>0; natural n; actual error(n)<=q^n initial. The faster-error statement is an explicit counterexample.'],
          R+'actual_positive_geometric_certificate_is_equivalent_to_the_printed_logarithmic_cutoff',
          B+'actual_geometric_tolerance_formula_is_a_sufficient_certificate_for_bounded_errors',
          B+'actual_faster_errors_do_not_need_the_geometric_envelope_first_index'),
    route('With fixed q in(0,1) and positive initial, the positive-tolerance cutoff grows asymptotically like log(1/epsilon) with constant1/log(1/q).',
          ['q and initial fixed, 0<q<1, initial>0; epsilon tends to0 from the right.'],
          B+'actual_geometric_cutoff_has_the_precise_logarithmic_growth_constant',
          B+'actual_positive_tolerance_cutoff_is_asymptotically_log_one_over_tolerance'),
    route('The exact reciprocal-square-root cutoff is1/epsilon^2, with the printed first indices20 and10^12 for the two exact envelopes.',
          ['epsilon>0 and reciprocal-square-root index>=1. Numerical specialization is epsilon=10^-6, initial1 and q=1/2.'],
          R+'actual_source_half_rate_first_tolerance_index_is_twenty',
          R+'actual_positive_square_root_error_cutoff_is_exactly_the_inverse_square',
          R+'actual_source_square_root_tolerance_requires_one_trillion_indices'),
    route('Exact positive geometric errors have an affine log plot; positive reciprocal-power curves have logarithmic derivative tending to0.',
          ['For the geometric identity q>0 and initial>0 (source q in(0,1)); reciprocal-power curve coefficient>0 and power>0, with real argument tending to positive infinity.'],
          B+'actual_exact_positive_geometric_errors_have_an_affine_logarithmic_plot',
          B+'actual_positive_reciprocal_power_logarithmic_slope_flattens',
          B+'actual_positive_scaled_power_curve_has_the_true_flattening_logarithmic_slope'),
]

ROUTES = {
    'primer-basics.html::node-916': BASICS_DEFINITION,
    'primer-basics.html::node-918': BASICS_DEFINITION,
    'primer-linalg.html::node-305': NORM_TABLE,
    'primer-linalg.html::node-307': NORM_TABLE,
    'primer-linalg.html::node-311': NORM_PROOF,
    'primer-linalg.html::node-332': ZONOTOPE,
    'primer-linalg.html::node-191': CUBE,
    'primer-linalg.html::node-205': SIGNED,
    'primer-linalg.html::node-171': POSITIVE_P,
    'primer-linalg.html::node-529': PLANAR,
}
