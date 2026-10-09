#!/usr/bin/env python3
"""Exact-source module coverage queue with individually scoped proof claims.

This does not turn a source inventory, theorem count, or an approximate numeric
check into completed formal coverage. Unreviewed requirements remain pending.
"""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
INV = json.loads((ROOT / "book/coverage/inventory.json").read_text())
PAGES = ["landscape", "toolkit-lmi", "toolkit-gp", "safe-bo", "safe-bo-theory",
         "gosafe", "viability", "lipsdp", "lipschitz-by-design", "nn-in-the-loop", "verification"]
SOURCES = {f"SafeLearning/{p}.html" for p in PAGES}


def digest(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def split_sentences(text):
    """Sentence boundaries outside TeX; decimal points are never separators."""
    text = re.sub(r"\s+", " ", text).strip()
    result, start, dollar = [], 0, False
    for i, c in enumerate(text):
        if c == "$" and (not i or text[i-1] != "\\"):
            dollar = not dollar
        if not dollar and c in ".?!" and (i+1 == len(text) or text[i+1].isspace()):
            piece = text[start:i+1].strip()
            if piece:
                result.append(piece)
            start = i+1
    tail = text[start:].strip()
    if tail:
        result.append(tail)
    return result or [text]


def claim(cid, statement, names=(), status="pending", kind="mathematical_requirement",
          hypotheses=(), correspondence="", gaps=(), units=()):
    return {"id": cid, "statement_in_prose": statement, "kind": kind,
            "lean_declarations": list(names), "status": status,
            "hypotheses": list(hypotheses), "correspondence": correspondence,
            "remaining_gaps": list(gaps) if gaps else ([] if status == "proved" else
                ["Every requested conclusion in this exact source sentence still requires a reviewed Lean correspondence."]),
            "source_unit_keys": list(units)}


BN = "SafeLearning.CompleteModulesBook."
TN = "SafeLearning.CompleteModulesTheory."
FN = "SafeLearning.CompleteModulesFinite."
ON = "SafeLearning.Modules."
AN = "SafeLearning.BookApplications."
NN = "SafeLearning.CompleteModulesNetworks."
DN = "SafeLearning.CompleteModulesDynamics."
SN = "SafeLearning.CompleteModulesScalarSDP."
CN = "SafeLearning.CompleteModulesConformal."
XN = "SafeLearning.CompleteConformal."
EN = "SafeLearning.CompleteModulesSafeExploration."
VN = "SafeLearning.CompleteModulesValues."
KN = "SafeLearning.CompleteModulesKernel."
RN = "SafeLearning.CompleteModulesRepresenter."
GN = "SafeLearning.CompleteModulesGPExamples."
MN = "SafeLearning.CompleteModulesMatrixGP."
PN = "SafeLearning.CompleteModulesPosterior."
QN = "SafeLearning.CompleteModulesKernelMetric."
JN = "SafeLearning.CompleteModulesKernelConstruction."
HN = "SafeLearning.CompleteModulesKernelCorollaries."
SSN = "SafeLearning.CompleteModulesRKHSStructure."
FFN = "SafeLearning.CompleteModulesKernelFunctional."
KBN = "SafeLearning.CompleteModulesGramBridge."
GDN = "SafeLearning.CompleteModulesGPDesign."
IPN = "SafeLearning.CompleteModulesInterpolantPower."
NGN = "SafeLearning.CompleteModulesGPNumerics."
LSN = "SafeLearning.CompleteModulesLipSDP."
LNN = "SafeLearning.CompleteModulesLipSDPNetwork."
LPN = "SafeLearning.CompleteModulesLipSDPProduct."
LWN = "SafeLearning.CompleteModulesLipSDPWalkthrough."
DQN = "SafeLearning.CompleteModulesDiagonalQC."
LCN = "SafeLearning.CompleteModulesLipSDPConvex."
IQN = "SafeLearning.CompleteModulesInvalidQC."
CSN = "SafeLearning.CompleteModulesChords."
SECN = "SafeLearning.CompleteModulesSectorExamples."
LDN = "SafeLearning.CompleteModulesLogDet."
BGN = "SafeLearning.CompleteModulesBarrierGradient."
ISN = "SafeLearning.CompleteModulesInverseSpectrum."
CHN = "SafeLearning.CompleteModulesCholesky."
SYN = "SafeLearning.CompleteModulesSylvester."
DTN = "SafeLearning.CompleteModulesDeterminantTaylor."
MEN = "SafeLearning.CompleteModulesMatrixError."
BTN = "SafeLearning.CompleteModulesBarrierTraining."
BSN = "SafeLearning.CompleteModulesBarrierSoundness."
BON = "SafeLearning.CompleteModulesBarrierObjective."
BPN = "SafeLearning.CompleteModulesBarrierPath."
BBN = "SafeLearning.CompleteModulesBarrierBoundary."
CYN = "SafeLearning.CompleteModulesCayley."
EPN = "SafeLearning.CompleteModulesEigenProduct."
CCN = "SafeLearning.CompleteModulesComplexCayleyCounterexample."
CYIN = "SafeLearning.CompleteModulesCayleyInverse."
CYPN = "SafeLearning.CompleteModulesCayleyPlane."
CYRN = "SafeLearning.CompleteModulesCayleyRange."
CLCN = "SafeLearning.CompleteModulesComplexCayley."
CLIN = "SafeLearning.CompleteModulesComplexCayleyInverse."
CLBN = "SafeLearning.CompleteModulesComplexBasics."
SGN = "SafeLearning.CompleteModulesScaledGram."
SLLN = "SafeLearning.CompleteModulesSLL."
SLCN = "SafeLearning.CompleteModulesSLLConsequences."
SLEN = "SafeLearning.CompleteModulesSLLExamples."

# These mappings are intentionally granular. A proved component is appended to
# the requirements queue; the exercise is not marked complete merely because it
# has a component theorem. Requirements not discharged below remain explicit.
COMPONENTS = {}


def component(key, statement, names, hypotheses=(), gaps=()):
    COMPONENTS.setdefault(key, []).append((statement, names, hypotheses, gaps))

component("lipsdp.html::exercise-18", "For arbitrary finite real matrices, the actual determinant Frechet derivative is trace(adjugate(N)*dN), hence the actual logdet derivative at every nonsingular matrix is trace(Ninv*dN). Applying this to the actual source block certificate gives its actual W0 Frobenius gradient -2 Lambda (Ninv)21 and the training objective gradient gradLoss+2 mu Lambda (Ninv)21.",
          [LDN+"determinantAlternating",LDN+"actual_determinant_multilinear_derivative",LDN+"actual_determinant_has_frechet_derivative",LDN+"actual_logdet_has_frechet_derivative",LDN+"actual_logdet_curve_derivative",BGN+"barrierMatrix",BGN+"barrierVariation",BGN+"actual_barrier_matrix_weight_derivative",BGN+"actual_symmetric_variation_trace_is_gradient",BGN+"actual_logdet_barrier_weight_gradient",BGN+"actual_barrier_training_weight_gradient"],
          ["The actual source finite block matrix is positive definite; the loss has its stated actual Frechet gradient at the current weight matrix."],
          ["The source's algorithm-path language needs an explicit semantic review against the actual fixed-interior limit, exact minimizing barrier path and nonglobal-local-minimum counterexamples below; no unspecified training trajectory is asserted to converge. The source's finite-difference remark is classified separately as empirical evidence, with its own seeded reproduction rather than a Lean theorem."])

component("lipsdp.html::exercise-18", "For every actual positive-definite finite real matrix, its Euclidean induced inverse norm is exactly the reciprocal of its actual smallest eigenvalue. Along every positive-definite matrix family whose actual smallest eigenvalue tends to zero, this inverse norm tends to positive infinity.",
          [ISN+"minimumEigenvalue",ISN+"actual_inverse_eigen_diagonalization",ISN+"actual_inverse_spectral_norm_is_eigen_inverse_norm",ISN+"actual_minimum_eigenvalue_is_positive",ISN+"actual_minimum_eigenvalue_is_attained",ISN+"actual_inverse_spectral_norm_is_exact_reciprocal",ISN+"actual_inverse_norm_blows_up_at_singular_boundary"],
          ["The actual matrix is positive definite and has a nonempty finite coordinate type. Boundary divergence is conditional on its actual smallest eigenvalue tending to zero, exactly as in the source's explanation of approaching singularity."],
          ["The source's training trajectory itself is not asserted to approach this boundary; roundoff acceptance remains pending."])

component("lipsdp.html::exercise-18", "Every actual finite real positive-definite matrix has a lower triangular Cholesky factor with strictly positive diagonal, constructed through its actual Gram representation and Gram-Schmidt basis. Such a factor implies positive definiteness. Thus nonexistence of such an exact factor is equivalent to failure of positive definiteness. All leading principal minors of a positive-definite matrix are positive, and the factor yields the exact reused inverse (Ginv)-transpose*Ginv.",
          [CHN+"triangularGramFactor",CHN+"actual_gram_factor_is_lower_triangular",CHN+"actual_gram_factor_product",CHN+"actual_gram_schmidt_diagonal_is_norm",CHN+"actual_gram_factor_diagonal_is_positive",CHN+"actual_positive_definite_matrix_has_cholesky",CHN+"actual_positive_triangular_factor_implies_positive_definite",CHN+"actual_cholesky_existence_iff_positive_definite",CHN+"actual_exact_cholesky_failure_iff_not_positive_definite",CHN+"actual_positive_definite_leading_principal_minors_are_positive",CHN+"actual_cholesky_factor_reuses_inverse"],
          ["Exact finite real matrix arithmetic; the theorem concerns existence of the exact source-specified positive-diagonal triangular factor, without making claims about an unspecified implementation or rounded computation."],
          ["Floating-point test behavior remains a separate pending requirement."])

component("lipsdp.html::exercise-18", "For every actual finite symmetric real matrix, all its actual leading principal minors are strictly positive iff it is positive definite. The reverse direction is proved by induction through the actual final scalar Schur complement and actual determinant factorization.",
          [SYN+"positiveLeadingPrincipalMinors",SYN+"actual_scalar_matrix_positive_definite_of_positive_determinant",SYN+"actual_last_schur_block_is_positive_definite",SYN+"actual_symmetric_matrix_with_positive_leading_minors_is_positive_definite",SYN+"actual_sylvester_criterion"],
          ["The actual matrix is symmetric; leading minors are actual determinant submatrices at every size, including the empty minor."],[])

component("lipsdp.html::exercise-18", "For every actual finite real direction matrix, det(I+epsilon E)=1+epsilon trace(E)+an explicit polynomial remainder times epsilon squared. Consequently the remainder is O(epsilon squared) as epsilon tends to zero. For every nonsingular actual matrix, det(N+epsilon E)=det(N)det(I+epsilon Ninv E), yielding its corresponding exact first-order coefficient and O(epsilon squared) remainder.",
          [DTN+"actualDeterminantRemainder",DTN+"actual_determinant_exact_second_order_expansion",DTN+"actual_determinant_second_order_remainder_is_bigO",DTN+"actual_determinant_perturbation_factorization",DTN+"actual_general_determinant_second_order_expansion"],
          ["The unperturbed actual finite real matrix is nonsingular for the factorized expansion; the unit-matrix expansion has no symmetry or eigenvalue assumptions."],[])

component("lipsdp.html::exercise-18", "Arbitrarily small absolute spectral-norm perturbations can reverse positive-definiteness in either direction: explicit actual scalar matrices are positive definite and indefinite within every positive tolerance. A genuine validated margin theorem proves that an actual symmetric matrix is positive definite whenever its spectral-norm error from a computed matrix is bounded by margin and computed-minus-margin-I is positive definite. The proof bounds actual quadratic-form error by the actual Euclidean matrix norm.",
          [MEN+"actualQuadratic",MEN+"actual_quadratic_error_is_bounded_by_spectral_norm",MEN+"actual_quadratic_shift",MEN+"actual_validated_matrix_margin_certifies_positive_definiteness",MEN+"positiveNearSingular",MEN+"indefiniteNearSingular",MEN+"actual_near_singular_matrix_is_positive",MEN+"actual_near_singular_matrix_is_not_positive",MEN+"actual_opposite_feasibility_matrices_are_arbitrarily_close",MEN+"actual_small_absolute_error_can_reverse_both_feasibility_decisions"],
          ["The actual finite matrix is symmetric. A validated spectral-norm error bound and an actual shifted computed-matrix positive-definiteness certificate provide the mathematical safety margin."],
          ["These genuine norm-error certificates and perturbation counterexamples support the source's qualitative finite-precision warning; they do not assert verified behavior of an unspecified IEEE format, Cholesky implementation, or floating-point training pipeline."])

component("lipsdp.html::exercise-18", "For the literal source block matrix with scalar weights, gain one and zero last weight, the actual certificate has quadratic form (x-lambda*w*y)^2+lambda*(2-lambda*w^2)*y^2+z^2. Parameters (w,lambda)=(1,1) and (3,1/5) are each genuinely positive definite, whereas their midpoint (2,3/5) is not. Thus the actual joint trained-weight/multiplier feasible set is not convex. A finite weight step from w=1 to w=2 at fixed multiplier one leaves the actual positive-definite certificate region.",
          [BTN+"scalarWeight",BTN+"actualTrainingMatrix",BTN+"scalarState",BTN+"actual_training_matrix_is_symmetric",BTN+"actual_training_matrix_quadratic_identity",BTN+"actual_training_matrix_is_positive_definite",BTN+"actual_joint_training_endpoints_are_feasible",BTN+"actual_joint_training_midpoint_is_infeasible",BTN+"actualJointTrainingFeasibleSet",BTN+"actual_jointly_trained_weight_and_multiplier_set_is_not_convex",BTN+"actual_finite_weight_step_can_leave_positive_definite_certificate"],
          ["The actual source neural block certificate, with one scalar input, one scalar hidden neuron, one scalar output, gain one and last weight zero. The weight and positive diagonal multiplier are jointly variable."],
          ["This proves nonconvexity and finite-step failure in the actual source model; it does not assert that any specific line-search rule or varying-mu trajectory follows the counterexample step."])

component("lipsdp.html::exercise-18", "The literal source positive-definite three-block barrier matrix, after actual sum-index reassociation and actual output Schur elimination, implies negative semidefiniteness of the precise one-hidden-layer LipSDP block certificate. Positive definiteness also forces every actual diagonal multiplier positive. Therefore every accepted iterate satisfying this actual positive-definite barrier predicate certifies the actual biased network's Euclidean Lipschitz gain at the specified nonnegative gain, for every actual [0,1]-slope-restricted activation.",
          [BSN+"leadingBarrierBlock",BSN+"outputBarrierCross",BSN+"actual_barrier_reassociates_to_output_schur_block",BSN+"actual_barrier_schur_complement_is_negative_lipsdp_certificate",BSN+"actual_positive_barrier_implies_lipsdp_feasibility",BSN+"actual_positive_barrier_has_positive_diagonal_multiplier",BSN+"actual_accepted_positive_barrier_certifies_actual_network"],
          ["The actual source barrier matrix is positive definite; the claimed gain is nonnegative; the actual activation has the source's full incremental [0,1] restriction. The conclusion bounds every pair of actual network inputs and includes both biases."],
          ["For a computed numerical acceptance test, its validated error margin must establish this actual positivity predicate. No optimization convergence or external training implementation is assumed proved."])

component("lipsdp.html::exercise-18", "For the actual scalar source certificate at fixed positive multiplier, the determinant is lambda*(2-lambda*w^2). A fully specified training loss equals a quartic/cubic polynomial plus logdet of this actual certificate. At barrier parameter one its actual barrier objective has a genuinely feasible local minimum at w=-1 which is not global, since the feasible point w=1 has strictly lower value. The example training loss itself is not convex on the certified weight set.",
          [BON+"actual_scalar_training_matrix_determinant",BON+"examplePolynomialObjective",BON+"exampleTrainingLoss",BON+"exampleBarrierObjective",BON+"actualFixedMultiplierFeasibleWeights",BON+"actual_example_barrier_objective_is_polynomial",BON+"actual_polynomial_objective_gap",BON+"actual_polynomial_negative_halfline_minimum",BON+"actual_barrier_objective_has_feasible_nonglobal_local_minimum",BON+"actual_training_loss_is_not_convex_on_certified_weights"],
          ["The actual source scalar certificate at gain one, multiplier one and zero last weight, and the explicitly supplied smooth-inside-the-certified-set loss. Both comparison weights are actually certified."],
          ["This constructive counterexample demonstrates the absence of a universal global-optimum guarantee. It does not identify or assume the behavior of any unspecified data loss, optimizer, or training trajectory."])

component("lipsdp.html::exercise-18", "At every fixed actual interior source matrix, the W0 barrier-gradient term tends to zero as mu tends to zero. For the actual scalar source certificate and the explicit loss -w, the exact barrier minimizer is w(mu)=sqrt(mu^2+2)-mu for each mu>0: an actual log-inequality proof gives a nonnegative squared objective gap over every certified weight. This minimizing path stays positive definite at every positive mu and tends to sqrt(2), where the actual certificate is singular but positive semidefinite and globally minimizes the explicit loss on the closed certificate domain.",
          [BPN+"actualBarrierPath",BPN+"actualLinearLossBarrierObjective",BPN+"actual_barrier_path_stationarity_identity",BPN+"actual_barrier_path_is_positive",BPN+"actual_barrier_path_stays_strictly_certified",BPN+"actual_barrier_path_objective_gap",BPN+"actual_barrier_path_is_global_minimum",BPN+"actual_barrier_path_tends_to_boundary",BPN+"actual_barrier_path_determinant_tends_to_zero",BPN+"actual_path_limit_is_singular_but_certified_semidefinite",BPN+"actual_path_limit_globally_minimizes_loss_on_closed_certificate",BPN+"actual_fixed_interior_weight_barrier_term_vanishes"],
          ["The fixed-interior derivative limit holds for every finite source block matrix. The minimizing-path example uses the actual one-scalar source certificate at gain/multiplier one and zero last weight, and the explicitly defined loss -w with positive mu."],
          ["These are actual conditional derivative limits and a fully derived illustrative barrier minimizer path. They establish that boundary approach can occur, not convergence of an unspecified nonconvex optimization algorithm or arbitrary parameter path."])

component("lipsdp.html::exercise-18", "Along every actual finite real matrix family converging to an actual finite singular matrix, determinant tends to zero. If every family member is positive definite and mu is a fixed positive number, its actual barrier value -mu*log(det(matrix)) tends to positive infinity. The proof uses continuity of the actual determinant, actual determinant positivity, and the real logarithm's limit from above at zero.",
          [BBN+"actual_determinant_tends_to_zero_at_finite_singular_boundary",BBN+"actual_logdet_barrier_blows_up_at_finite_singular_boundary",BBN+"actual_logdet_barrier_blows_up_at_noninvertible_finite_boundary"],
          ["The actual positive-definite finite matrices converge to a finite singular matrix; the barrier parameter is fixed and strictly positive. No false inference is made from minimum-eigenvalue convergence alone when other eigenvalues can diverge."],[])

component("lipsdp.html::exercise-18", "For every actual finite complex matrix X and scalar epsilon, det(I+epsilon X)=the product of1+epsilon omega over all actual characteristic roots, counted with algebraic multiplicity. Every root is in the actual matrix spectrum. Real matrices satisfy this identity after actual complexification, so the actual generally nonsymmetric Ninv*E is covered.",
          [EPN+"actual_complex_characteristic_roots_count",EPN+"actual_complex_determinant_is_eigenvalue_product",EPN+"actual_real_determinant_is_actual_complex_eigenvalue_product",EPN+"actual_characteristic_root_is_actual_matrix_spectral_value"],
          ["An arbitrary finite square real or complex matrix; no symmetry or diagonalizability premise."],[])

component("lipschitz-by-design.html::exercise-15", "For every actual finite real skew-symmetric matrix A, I+A and I-A are invertible. The actual rational transform Q=(I-A)(I+A)inv satisfies Q-transpose*Q=I and determinant one. Q+I is exactly twice the denominator inverse and is itself invertible, so Q has no nonzero eigenvector with eigenvalue -1.",
          [CYN+"actualCayley",CYN+"actual_skew_cayley_denominator_gram_is_positive",CYN+"actual_skew_cayley_denominator_is_invertible",CYN+"actual_skew_cayley_numerator_is_transposed_denominator",CYN+"actual_skew_cayley_numerator_is_invertible",CYN+"actual_cayley_is_orthogonal",CYN+"actual_cayley_has_determinant_one",CYN+"actual_cayley_plus_identity_is_twice_inverse",CYN+"actual_cayley_plus_identity_is_invertible",CYN+"actual_cayley_has_no_negative_one_eigenvector"],
          ["An arbitrary finite real matrix with actual transpose equal to its negative."],
          [])

component("lipschitz-by-design.html::exercise-15", "For the actual two-dimensional skew matrix [[0,a],[-a,0]], the denominator inverse is [[1,-a],[a,1]]/(1+a^2), and its actual Cayley transform is [[1-a^2,-2a],[2a,1-a^2]]/(1+a^2). This is exactly the actual rotation matrix at angle2*arctan(a), with angle strictly between -pi and pi. At a=1/2 the actual matrix is [[3/5,-4/5],[4/5,3/5]]. The exact angle in degrees differs from53.13 by at most.005, proved through actual alternating arctan sums and analytic pi bounds.",
          [CYPN+"actualPlaneSkew",CYPN+"actualPlaneRotation",CYPN+"actual_plane_matrix_is_skew",CYPN+"actual_plane_denominator_inverse",CYPN+"actual_plane_cayley_formula",CYPN+"actual_arctan_rotation_coordinates",CYPN+"actual_plane_cayley_is_rotation",CYPN+"actual_plane_cayley_angle_is_in_open_pi_interval",CYPN+"actual_half_parameter_cayley_matrix",CYPN+"actualHalfArctanTerm",CYPN+"actual_half_arctan_terms_are_antitone",CYPN+"actual_half_parameter_angle_rounds_to_53_13_degrees"],
          ["An arbitrary real scalar parameter in the actual source two-by-two skew matrix. Degrees are180/pi times the actual real angle; the printed two-decimal approximation is controlled by an analytic half-decimal-unit error bound."],[])

component("lipschitz-by-design.html::exercise-15", "The range of the actual scalar two-dimensional Cayley parameterization is exactly the two-dimensional orthogonal determinant-one matrices except -I. Every orthogonal determinant-minus-one matrix has an actual nonzero eigenvector of eigenvalue -1. Thus the omitted two-dimensional orthogonal matrices are precisely the pi rotation and every reflection.",
          [CYRN+"actual_every_plane_skew_matrix_has_scalar_form",CYRN+"actual_plane_rotation_denominator_is_invertible",CYRN+"actual_plane_cayley_range_is_exact",CYRN+"actual_every_orthogonal_reflection_has_negative_one_eigenvector",CYPN+"actual_plane_cayley_never_produces_reflection",CYPN+"actual_plane_cayley_never_produces_pi_rotation"],
          ["Actual finite real matrices. The exact range classification is two-dimensional; the reflection eigenvector conclusion holds in arbitrary finite dimension."],[])

component("lipschitz-by-design.html::exercise-16", "For every actual finite real matrix W and every strictly positive coordinate scaling q, the source diagonal Tii=sum_j |(W-transpose W)ij|qj/qi satisfies actual T-W-transpose W positive semidefinite. More generally the same construction majorizes every actual real symmetric matrix. The proof derives a genuine weighted Young inequality and bounds its actual finite quadratic form by the diagonal sum; it does not assume nonnegative eigenvalues or the desired matrix inequality.",
          [SGN+"actualMajorizerDiagonal",SGN+"actualScaledMajorizer",SGN+"actual_scaled_young_inequality",SGN+"actual_scaled_symmetric_pair_bound",SGN+"actual_symmetric_quadratic_is_bounded_by_scaled_majorizer",SGN+"actual_scaled_majorizer_difference_is_positive_semidefinite",SGN+"actual_weighted_gram_matrix_is_bounded_by_source_diagonal"],
          ["Arbitrary actual finite real weights and strictly positive real coordinate scalings; no nonzero-column assumption is needed for this semidefinite majorization alone."],
          ["The actual residual layer's energy/QC inequality and the two supplied scale examples are separate pending exercise clauses. The literal Gershgorin-disc proof in the answer is also a separate material-source correspondence."])

component("lipschitz-by-design.html::exercise-16", "For the actual arbitrary finite residual layer h(x)=x-2WTinv phi(W-transpose x+b), actual positive diagonal T, actual T-W-transpose W PSD and actual globally[0,1]-slope-restricted phi, the exact energy gap is the nonnegative activation QC term plus4DeltaPhi-transpose Tinv(T-W-transpose W)Tinv DeltaPhi. Thus the literal source energy margin is nonnegative and the actual biased layer is Euclidean nonexpansive for every input pair.",
          [SLLN+"actualSLL",SLLN+"actual_positive_diagonal_inverse",SLLN+"actual_positive_diagonal_is_invertible",SLLN+"actual_residual_step_energy_identity",SLLN+"actual_sll_energy_gap_is_qc_plus_certificate",SLLN+"actual_sll_incremental_quadratic_constraint",SLLN+"actual_sll_is_euclidean_nonexpansive",SLCN+"actualHiddenIncrement",SLCN+"actual_sll_input_output_increment",SLCN+"actual_inverse_certificate_pullback_is_source_quadratic",SLCN+"actual_sll_source_energy_margin",SLCN+"actual_majorizer_diagonal_is_nonnegative",SLCN+"actual_majorizer_diagonal_is_positive_for_nonzero_column",SLCN+"actual_positive_regularization_makes_majorizer_diagonal_positive",SLCN+"actual_source_scaled_sll_is_nonexpansive"],
          ["Arbitrary actual finite real weights, actual positive diagonal, source PSD certificate and the source's full incremental slope restriction. The source-scaled specialization requires positive q and nonzero columns so its actual inverse exists."],
          ["Whole Exercise13.2 remains partial until all source question/hint/answer clauses receive review; the literal Gershgorin-disc derivation, named tanh/sigmoid activations and epsilon-regularized certificate/corollary are not inferred from this component."])

component("lipschitz-by-design.html::exercise-16", "For the actual source W=[[1,1],[0,1]], its actual Gram is[[1,1],[1,2]]. Actual weighted diagonal construction atq=(1,1) givesdiag(2,3) and atq=(1,2) givesdiag(3,5/2). The actual differences are[[1,-1],[-1,1]] and[[2,-1],[-1,1/2]], both PSD, with exact characteristic polynomialsX(X-2) andX(X-5/2) and actual spectral values exactly0,2 or0,5/2. Neither actual majorizer dominates the other in PSD order, witnessed by actual unit vectors.",
          [SLEN+"actualSourceWeights",SLEN+"actualFirstMajorizer",SLEN+"actualSecondMajorizer",SLEN+"actual_source_gram_matrix",SLEN+"actual_first_scale_majorizer",SLEN+"actual_second_scale_majorizer",SLEN+"actual_first_certificate_matrix",SLEN+"actual_second_certificate_matrix",SLEN+"actual_both_source_certificates_are_positive_semidefinite",SLEN+"actual_first_certificate_characteristic_polynomial",SLEN+"actual_second_certificate_characteristic_polynomial",SLEN+"actual_first_certificate_eigenvalues",SLEN+"actual_second_certificate_eigenvalues",SLEN+"actual_source_majorizers_are_not_ordered"],
          ["The literal two-by-two weights and both literal positive scale vectors from Exercise13.2(c). Spectrum is the actual matrix spectrum, not an assumed eigenvalue list."],
          ["The final answer's SN spectral-norm-squared formula(3+sqrt5)/2 and its2.618 rounding are not part of this component and remain pending."])



component("landscape.html#book-m1-b1", "Without independence, twenty measurable overheating events with probability at most 1/400 each have joint success probability at least 19/20.",
          [TN+"equal_fleet_failure", BN+"fleet_budget"], ["A probability measure and twenty measurable events."])
component("landscape.html#book-m1-b2", "The third schedule has mean 60 and the global minimum of its Rockafellar–Uryasev expression is 79, attained at threshold59.",
          [BN+"peak_mean_examples", BN+"rare_spike_cvar_lower", BN+"rare_spike_cvar_attained"],
          ["Two-point loss with masses49/50 and1/50 at59 and109; CVaR confidence19/20."],
          ["Identification with an actual random-variable law, its overheating probability, and the accept/reject comparisons remain to be linked separately."])
component("toolkit-lmi.html#book-m2-b1", "Every startup satisfying coordinate magnitudes at most7/10 has energy at most49/50, hence is inside the invariant unit disk.",
          [BN+"startup_box_energy", BN+"thermal_disk_invariant", BN+"disk_coordinate_containment"],
          ["The exact two-dimensional map thermalA; coordinatewise startup bounds."],
          ["The displayed sharp spectral q, square-root radius approximation and one-step q*sqrt(.98) bound are not established by this energy argument."])
component("toolkit-lmi.html#book-m2-b2", "For q<1, qR+allowance<=R is equivalent to R>=allowance/(1-q); nonzero constant forcing gives the corresponding nonzero scalar equilibrium.",
          [BN+"invariant_radius_iff", BN+"nonzero_forced_equilibrium", AN+"tube_error_envelope"],
          ["q is the induced gain; nonnegative scalar recursion and q<1."],
          ["The exact matrix induced gain and eigenvector realization of the counterexample still need their own correspondence."])
component("toolkit-gp.html#book-m3-b1", "The repeated-observation all-ones system has coefficient2/(1+4n), posterior mean8n/(1+4n), variance4/(1+4n); for n=3 the temperature upper bound is strictly below60.",
          [BN+"repeated_gp_linear_system", BN+"repeated_gp_variance", BN+"repeated_gp_three_accept"],
          ["Fixed all-4 kernel matrix and unit regularization."],
          ["The scalar identities still need a general matrix-to-posterior correspondence, including uniqueness and sum-coordinate reduction."])
component("toolkit-gp.html#book-m3-b2", "The midpoint action56.5 fails after discrepancy allowance0.4; nominal+bound<=cap iff nominal<=cap-bound; modeled envelope plus bounded discrepancy implies the physical upper-temperature inequality.",
          [BN+"gp_midpoint_linear_solutions", BN+"gp_midpoint_unique_solution", BN+"midpoint_discrepancy_reject", BN+"residual_with_discrepancy", BN+"maximal_nominal"],
          ["Actual modeled error and discrepancy satisfy their displayed absolute bounds."],
          ["The posterior-envelope probability is explicitly assumed by the source and is not inferred here."])
component("safe-bo.html#book-m4-b1", "The conjunction of the two displayed lower-bound constraints is equivalent to gain displacement at most0.3; displacement0.4 fails the vibration inequality.",
          [BN+"two_constraints_radius", BN+"gain_proposals_fail"], ["Separate linear lower certificates for heat and vibration."])
component("safe-bo.html#book-m4-b2", "With realization error0.04 the common radius condition holds iff commanded displacement<=0.26; the0.28 proposal's worst realization has vibration lower bound-0.008.",
          [BN+"gain_realization_radius", BN+"gain_proposals_fail", AN+"lipschitz_implemented_parameter"],
          ["Actual distance obeys the metric triangle inequality and realization bound."])
component("safe-bo-theory.html#book-m5-b1", "The whole realization interval[a-.1,a+.1] is contained in[-1,1.55] exactly when a is in[-.9,1.45].",
          [BN+"losbo_command_interval", BN+"interval_realization_iff"], ["Nonnegative realization radius; non-strict safety intervals."])
component("safe-bo-theory.html#book-m5-b2", "Summing measurable finite-run failure events bounds their union without independence.",
          [TN+"finite_failure_union", TN+"simultaneous_success"], ["The stated per-query tail bound must hold for the actual adaptive experiment law."],
          ["Gaussian tail theorem, log/square-root choice of E, adaptation via conditional laws, and displayed radius approximation remain to be formally linked."])
component("gosafe.html#book-m6-b1", "The exact monitoring inequality .25+.02+.8dt<=.4 holds iff dt<=13/80.",
          [BN+"backup_monitor_period", BN+"backup_examples"], ["The given weighted distance and latency reserve."])
component("gosafe.html#book-m6-b2", "The four relevant first/second-backup distances are .50,.10,.75,.55, with metric triangle inequality for all states.",
          [BN+"backup_examples", BN+"backup_distance_triangle"], ["Weighted distance |delta d|+.5|delta v|."],
          ["Union membership/rejection and remaining-margin comparisons need final explicit specialization."])
component("viability.html#book-m7-b1", "At cap62 the predecessor sequence is Iic5 -> Iic4 -> Iic3; Iic3 is controlled invariant and contains every controlled-invariant subset of Iic5.",
          [FN+"thermal_predecessor_cap62", FN+"thermal_predecessor_cap62_second", FN+"thermal_predecessor_cap62_fixed", FN+"thermal_kernel_controlled_invariant", FN+"thermal_kernel_maximal"],
          ["Indexi encodes52+2i; run adds1, cooling subtracts2 and is allowed only for2<=i<4."],
          ["Link from controlled invariance to existence of an infinite admissible trajectory, and explicit index-to-temperature equivalence, remain to be completed."])
component("viability.html#book-m7-b2", "The displayed safe cycle value is540/61, strict rush separation has threshold5657/244, p=24 gives41/5 below540/61, and equality is a tie.",
          [BN+"safe_cycle_values", BN+"rush_strict_threshold", BN+"rush_threshold_equality", BN+"rush_eight_tenths_threshold"],
          ["The safe-cycle formula is the proposed comparison value."],
          ["Optimality over all safe and all penalized policies still requires Bellman verification and infinite discounted-return correspondence; the arithmetic alone does not prove every maximizing policy is safe."])
component("lipsdp.html#book-m12-b1", "Normalized coordinate errors<=.02 give squared Euclidean radius<=1/1250.",
          [BN+"lipsdp_box_radius"], ["The stated physical-to-normalized scaling."],
          ["The exact network global Euclidean and box Lipschitz constants, attainment, and final comparison with.06 remain to be established."])
component("lipsdp.html#book-m12-b2", "The proposed coupled multiplier's explicit ReLU increment gives quadratic value-2.",
          [BN+"coupled_multiplier_failure",IQN+"coupled_multiplier_is_positive_semidefinite",IQN+"coupled_multiplier_exact_eigenvalues",IQN+"actual_book_coupled_relu_failure",IQN+"positive_semidefiniteness_does_not_make_coupled_qc_valid"],
          ["The actual exact two ReLU input pairs and specified actual positive-semidefinite coupled matrix."])
component("lipschitz-by-design.html#book-m13-b1", "A map with exact coordinate slope.4 cannot satisfy a global normalized Lipschitz bound.3 on any two distinct points along that coordinate.",
          [BN+"normalized_target_incompatible"], ["Two distinct points on a coordinate segment within the open region."],
          ["The open-region segment-existence and affine-preprocessing correspondence, plus full gradient norm, remain to be encoded."])
component("lipschitz-by-design.html#book-m13-b2", "A product of nonnegative stage gains bounded byb is bounded byb^n; scale<=target/factor ensures scale*factor<=target; the stated six-stage reciprocal scale cancels exactly.",
          [BN+"gain_stack_bound", BN+"external_scale_certificate", BN+"six_stage_scale"],
          ["Positive implementation gain factor and nonnegative stage gains."],
          ["The actual operator-error triangle inequality and function-composition Lipschitz correspondence still need direct connection."])
component("nn-in-the-loop.html#book-m14-b1", "Actual tanh is globally1-Lipschitz; the exact closed map is.9-Lipschitz; bias and disturbance produce the.9|e|+.029 bound, with invariant-radius budget.479<=.5 and ultimate scalar radius.29.",
          [TN+"tanh_lipschitz", TN+"neural_thermal_lipschitz", TN+"neural_thermal_bias_disturbance", BN+"biased_invariant_and_ultimate"],
          ["Exact tanh/plant equations and bias/disturbance magnitudes."],
          ["The actuator bound1.5tanh(.53)<.8 and ultimate-limit theorem still require direct proof."])
component("nn-in-the-loop.html#book-m14-b2", "Independently initialized history(.5,-.5) leaves the square at next error.6 while the input magnitude.75 meets.8.",
          [BN+"delayed_square_counterexample"], ["Independent history initialization as explicitly stated in the source."],
          ["Complex characteristic roots and convergence of every augmented trajectory remain to be formalized."])
component("verification.html#book-m15-b1", "On the changed interval[-.1,.5], the network lies in[-.1,.3], and both extrema are attained; nominal59.7 therefore satisfies the non-strict60 cap.",
          [BN+"verification_changed_range", BN+"verification_extrema_attained", BN+"changed_temperature_pass"],
          ["Exact real ReLU network and changed input interval."])
component("verification.html#book-m15-b2", "A finite99%-quantile arithmetic condition is equivalent ton>=99; on the whole-trajectory residual envelope.32, every nominal59.35 plus neural bound.3 is<=59.97.",
          [BN+"trajectory_conformal_size", BN+"trajectory_residual_transfer"],
          ["Pointwise bounds for every time and common trajectory coverage event."],
          ["Exchangeable-rank/conformal coverage and ceiling/infinite-quantile correspondence are owned by the shared general conformal proof."])

# Follow-up proofs close substantive gaps listed in the initial component audit.
component("landscape.html#book-m1-b1", "Actual independence of measurable success events gives the product formula and a lower bound(.9975)^20.",
          [TN+"independent_success_product",TN+"independent_success_lower"],
          ["Independence is a property of the actual event law, not inferred from a list of marginal budgets."])
component("toolkit-lmi.html#book-m2-b1", "The exact induced Euclidean gain isq=(13+sqrt5)/20: a universal residual-square identity gives the upper bound, and its eigenvector attains it.",
          [DN+"thermal_norm_residual_square",DN+"thermal_exact_squared_norm_bound",DN+"thermal_gain_eigenvector",DN+"thermal_radius_gain"],
          ["The displayed exact thermal matrix."])
component("toolkit-lmi.html#book-m2-b2", "The actual two-dimensional disturbed map obeys the Euclidean triangle/gain bound; the unit disk remains invariant at noise radius.05; an explicit nonzero constant-forcing equilibrium disproves universal zero convergence.",
          [DN+"l2_triangle",DN+"thermal_disturbed_step",DN+"thermal_disturbed_unit_disk",DN+"thermal_constant_forcing_equilibrium",DN+"thermal_forced_trajectory_not_zero",TN+"tube_ultimate_bound"],
          ["Exact linear dynamics and Euclidean disturbance bound."],
          ["The radius-attaining forcing in the slow eigenvector direction still needs explicit normalization; the proved nonzero equilibrium already answers the requested zero-convergence question."])
component("toolkit-gp.html#book-m3-b1", "The constant-kernel regularized finite-dimensional linear system has its unique uniform solution for arbitrary sample count.",
          [BN+"constant_kernel_regularized_unique"], ["Each row of(I+4*ones)a is the same rhs."])
component("safe-bo.html#book-m4-b2", "The nominal.28 command has positive vibration lower margin while its worst allowed realization has a negative lower margin.",
          [BN+"nominal_gain_positive_but_realization_fails"], ["The source's linear vibration lower certificate."])
component("gosafe.html#book-m6-b2", "The first low-speed state passes only backup2; the high-speed state passes neither backup, by direct exact certificate comparisons.",
          [BN+"backup_library_decisions"], ["The exact displayed centers, metric, radii and reserve."])
component("viability.html#book-m7-b1", "An actual infinite admissible trajectory exists exactly from indices<=3, even after allowing cap62; every other initial state exits by two steps.",
          [FN+"thermal_infinite_trajectory_exists",FN+"thermal_infinite_trajectory_necessary",FN+"thermal_infinite_viability_iff"],
          ["The exact action interlock and temperature index encoding52+2i."])
component("lipsdp.html#book-m12-b1", "The two-neuron function is the max of four affine maps; its sharp Euclidean constant issqrt(5/4) and its sharp infinity constant is3/2. Physical scaling2 gives exact box error<=.06, attained by explicit inputs.",
          [NN+"two_neuron_max_affine",NN+"two_neuron_lipschitz_l2",NN+"exact_l2_slope_attained",NN+"exact_l2_gain_necessary",NN+"two_neuron_lipschitz_box",NN+"physical_correction_box",NN+"physical_box_bound_attained"],
          ["The exact real network and simultaneous normalized coordinate-error bounds."],
          ["The specific conservative SDP-radius value.065320 and hardware scaling-factor approximation remain to be separately enclosed."])
component("lipschitz-by-design.html#book-m13-b2", "A continuous linear operator within norm error.002 of a norm<=1 operator has norm<=1.002; actual Lipschitz stage composition multiplies gains through depth.",
          [NN+"approximate_orthogonal_operator",NN+"finite_stage_lipschitz_composition",BN+"gain_stack_bound",BN+"external_scale_certificate"],
          ["The implemented operator error is in the induced norm and each activation is1-Lipschitz."],
          ["The orthogonal-matrix-to-operator norm equivalence and the displayed decimal reciprocal scale remain to be explicitly mapped."])
component("nn-in-the-loop.html#book-m14-b1", "For the actual biased nonlinear recurrence, every sampled state remains inside|e|<=.5 and every commanded actuator stays below.8; for everyepsilon>0 errors are eventually below.29+epsilon.",
          [TN+"biased_actuator_within_limit",TN+"biased_neural_recursive_containment",TN+"biased_neural_ultimate_radius"],
          ["Initial error bound, every bias/noise bound and exact closed-loop update."])
component("nn-in-the-loop.html#book-m14-b2", "The actual augmented delayed recurrence has an exact rational positive Lyapunov storage with geometric decay; every trajectory's squared Euclidean energy tends to zero.",
          [DN+"delayed_storage_bounds",DN+"delayed_storage_exact_decrease",DN+"delayed_storage_contraction",DN+"delayed_trajectory_energy",DN+"delayed_trajectory_energy_tends_zero"],
          ["The exact independently initialized two-coordinate recurrence."],
          ["The printed complex-root values are not needed for this independent stability proof, but remain separate material claims."])
component("verification.html#book-m15-b1", "The maximum changed-domain temperature60 is attained and the changed-domain minimum is negative.",
          [BN+"changed_zero_margin_attained"], ["The specified changed input interval and exact network."])
component("verification.html#book-m15-b2", "The actual ceiling rank is finite exactly forn>=99; atn=99 it is99. General score-vector exchangeability gives whole-trajectory coverage>=.99, ties included, for the actual order statistic.",
          [CN+"ninety_nine_finite_rank_iff",CN+"rank_ninety_nine_one_percent",CN+"whole_trajectory_ninety_nine_coverage",CN+"finite_horizon_score_iff",XN+"split_conformal_coverage"],
          ["Calibration examples and test example are entire exchangeable trajectories, with the fixed score equal to the maximum absolute residual over the horizon."],
          ["A final explicit specialization from the random trajectory-score representation to the calibration radius.32 and physical thermal event remains to be linked."])

# Original exercises with substantive newly checked components.
for key, statement, names in [
    ("landscape.html#practice-1", "The scalar safe set{4-x^2>=0} is exactly[-2,2].", [FN+"landscape_safe_set"]),
    ("landscape.html#practice-9", "Negating existence of a controller safe at every time gives failure at some time for every controller.", [FN+"viability_negation"]),
    ("landscape.html#practice-11", "For x_n=n/100, safetyx_n<=1 holds exactly forn<=100.", [FN+"first_drift_violation"]),
    ("landscape.html#practice-12", "The centered interval[-r,r] is robustly invariant for x+=x/2+w, |w|<=.1, exactly whenr>=.2.", [FN+"robust_half_radius_iff", AN+"tube_sampled_invariance"]),
    ("toolkit-lmi.html#practice-1", "For all feasiblex<=1, (x-2)^2>=1 with equality iff x=1.", [FN+"kkt_scalar_minimum"]),
    ("toolkit-lmi.html#practice-3", "The quadratic form of[[t,2],[2,1]] is nonnegative for every vector iff t>=4.", [FN+"schur_scalar_psd_iff"]),
    ("toolkit-lmi.html#practice-5", "For positivep, a^2p-p<0 iff|a|<1.", [FN+"scalar_lyapunov_iff"]),
    ("toolkit-lmi.html#practice-6", "The proposed S-procedure interval polynomial is exactly-(x-1)^2/2.", [FN+"s_procedure_identity", FN+"s_procedure_interval"]),
    ("toolkit-lmi.html#practice-10", "The singular-corner quadratic form2bxy+cy^2 is PSD iff b=0 and c>=0.", [FN+"singular_psd_range_condition"]),
    ("toolkit-lmi.html::exercise-19", "Tanh is differentiable with derivative1/cosh^2 in[0,1], yielding its full global incremental sector.", [TN+"tanh_derivative", TN+"tanh_derivative_bounds", TN+"tanh_incremental_sector"]),
    ("safe-bo.html#practice-11", "If every upper endpoint is at most the recommendation lower endpoint plus epsilon, true regret is at mostepsilon.", [TN+"confidence_recommendation"]),
    ("safe-bo.html#practice-12", "A metric grid covering radiusr with all sampled lower margins>=Lr ensures global nonnegativef under actual Lipschitz regularity.", [TN+"sampling_grid_margin"]),
    ("safe-bo-theory.html#practice-10", "Each constraint can use its own witness, and all transferred lower margins still imply conjunction of safety.", [TN+"multiple_constraint_witnesses"]),
    ("nn-in-the-loop.html::exercise-16", "Tanh's global origin sector and incremental sector follow from its actual derivative and monotonicity.", [TN+"tanh_global_sector", TN+"tanh_incremental_sector"]),
    ("verification.html#practice-easy-2", "The affine neuron and ReLU are soundly enclosed in[0,8] for the specified input box.", [FN+"neuron_interval_exact"]),
    ("verification.html#practice-easy-3", "The displayed chord and lower line bound ReLU across the entire interval[-2,3].", [FN+"unstable_relu_triangle"]),
    ("verification.html#practice-medium-2", "Signed CROWN propagation gives1-4(z+1)/3<=1-2ReLU(z)<=1 on[-1,2].", [FN+"crown_negative_output"]),
    ("verification.html#practice-hard-1", "The exact affine deviations over Euclidean and infinity balls are bounded by1 and1.4, with explicit attaining perturbations.", [FN+"affine_l2_ball", FN+"affine_infinity_ball", FN+"affine_minima_attained"]),
]:
    component(key, statement, names,
              gaps=["The source exercise's additional numerical specializations, explanations and any other requested subclaims remain separately pending until reviewed."])

component("landscape.html#practice-9", "One bad controller is compatible with another controller being safe forever, so existence of a bad controller does not negate viability.",
          [FN+"some_failure_compatible_with_viability"], ["The explicit two-controller countermodel."])
component("landscape.html#practice-10", "The infinite tail of discounted deterministic violations is exactlygamma^delay/(1-gamma).",
          [TN+"delayed_deterministic_discounted_violation"], ["Absolute discount strictly below1."],
          ["Time50 numerical budget comparison and deterministic event probability1 remain to be specialized."])
component("lipsdp.html::exercise-16", "Leaky ReLU itself satisfies the full incremental sector[alpha,1] for everyalpha in[0,1].",
          [NN+"leaky_relu_incremental_sector"], ["Actual activationmax(x,alpha*x)."],
          ["Requested matrix QC expansion and any local activation examples remain separately pending."])
component("lipsdp.html::exercise-19", "The scalar LipSDP quadratic form is feasible iff rho>=rho(t); its global objective gap is a nonnegative square over the positive denominator. The optimal multiplier is in the domain and attainsbeta^2*w0^2*w1^2. Actual scalar ReLU has sharp gain|w0*w1| for every finite bias.",
          [SN+"negative_scalar_schur_iff",SN+"scalar_lipsdp_feasibility_iff",SN+"scalar_rho_gap_identity",SN+"scalar_rho_global_lower",SN+"scalar_optimal_multiplier_domain",SN+"scalar_optimal_rho_attained",SN+"scalar_relu_upper",SN+"scalar_relu_exact_gain_necessary",SN+"scalar_relu_example"],
          ["0<=alpha<beta, nonzero output weight, t>w1^2/2."],
          ["Derivative/second-derivative formulas, uniqueness, arbitrary-activation tightness and displayed eigenvalues still need explicit checks."])
component("lipsdp.html#practice-medium-1", "The scalar certificate is exactly-4(3x-y)^2 and the actual ReLU network's sharp gain is6 for every finite bias.",
          [SN+"scalar_relu_certificate",SN+"scalar_relu_upper",SN+"scalar_relu_exact_gain_necessary"],
          ["Nonzero input weight3 and output weight2."],
          ["Direct LMI-to-incremental-bound specialization remains to be written."])
component("nn-in-the-loop.html::exercise-16", "Actual tanh is concave on nonnegative inputs, yielding the sharp local origin-sector lower slope tanh(radius)/radius.",
          [TN+"tanh_concave_nonnegative",TN+"tanh_chord_lower",TN+"tanh_local_origin_sector"],
          ["Positive radius and absolute preactivation at most that radius."],
          ["The source's numeric local slope bounds and shifted-feedback correspondence remain separately pending."])
component("verification.html::exercise-15", "For arbitrary finite affine layers, center-radius IBP is sound, and input corners attain both affine endpoints; ReLU interval propagation is monotone.",
          [NN+"affine_interval_center_radius",NN+"affine_interval_upper_attained",NN+"affine_interval_lower_attained",NN+"relu_interval_sound"],
          ["A rectangular independent input box, including every coordinate endpoint."],
          ["The requested shared-input joint-looseness witness still needs explicit association."])
component("verification.html::exercise-17", "General split conformal marginal coverage follows from actual score-vector exchangeability, with ties allowed and infinity when the desired rank is unavailable.",
          [XN+"split_conformal_coverage",XN+"unavailable_calibration_rank",XN+"calibration_failure_iff"],
          ["The training/score map is fixed before calibration; score vector measurable and exchangeable."],
          ["The source's requested continuous-score upper coverage bound1-alpha+1/(n+1), and fixed-model conditioning, remain to be checked if claimed."])

component("safe-bo.html::exercise-18", "An actual Lipschitz safety cone from a point left of an unsafe separator cannot reach or cross the separator. Induction proves every accumulated SafeOpt set remains strictly on the seed's side.",
          [EN+"no_lipschitz_jump_over_unsafe",EN+"safeopt_never_crosses_unsafe"],
          ["Actual Lipschitz regularity, actual unsafe separating point, all seed points to its left, valid lower confidence bounds, and the stated cone update."],
          ["The cosine-kernel and squared-exponential RKHS examples, power-series basis identification, numeric posterior enclosure and final reported optimizer remain distinct pending source claims."])
component("safe-bo-theory.html::exercise-15", "For actual observationsf(query)+noise and a time/point-dependent upper noise envelope, the explicit union-of-cones update is safe at every round, and every query chosen in that set is safe. No lower noise envelope or GP beta is needed by the proof.",
          [EN+"asymmetric_noise_query_safety",EN+"lipschitz_query_safety"],
          ["All-round actual upper-noise bound, actual Lipschitz regularity, safe seed, actual update, and acquisition membership in the current safe set."],
          ["Source indexing uses a separate initial no-update round; this is a harmless index translation but is not a separate formal declaration."])
component("safe-bo-theory.html::exercise-17", "Actual Holder regularity and upper-noise bounds imply all-round query safety under the Holder-cone update. For nonnegative slack the radius is(s/C)^(1/alpha); atalpha=.5 it is(s/C)^2, beating the Lipschitz radius exactly whens>C. Negative slack gives no half-Holder ball, and the numerical radii are.1 and.01.",
          [EN+"holder_query_safety",EN+"holder_general_radius",EN+"holder_half_radius",EN+"holder_half_beats_lipschitz",EN+"negative_slack_has_no_modulus_ball",EN+"holder_radius_example"],
          ["Actual Holder inequality; C>0, alpha>0; nonnegative distances and nonnegative slack for the inverse formula."],
          ["Continuity and strict increase of the general modulus, and the negative-slack claim for every positive exponent, remain separately pending."])
component("safe-bo-theory.html#practice-9", "The downward cone is genuinely globallyL-Lipschitz, matches the measured value at its center with positive-extreme noise, and is unsafe at every point beyond the certified radius.",
          [EN+"downward_cone_is_lipschitz",EN+"downward_cone_matches_observation",EN+"beyond_cone_is_unsafe"],
          ["L>0 and the positive extreme noiseE is allowed whenE>=0."],
          ["The noise absolute-bound specialization|E|<=E is elementary but not separately encoded here."])
component("gosafe.html#practice-6", "Taking an infimum over a trajectory suffix cannot decrease the margin. An actual deterministic flow semigroup preserves safety on restart from every visited state.",
          [EN+"trajectory_suffix_infimum",EN+"flow_restart_trajectory_suffix"],
          ["Actual flow semigroup law, nonnegative switching time, and a bounded-below full-trajectory margin image."],
          ["The source's.2 specialization is not explicitly instantiated; omitted internal state or clock counterexamples remain explanatory claims."])
component("gosafe.html::exercise-15", "The actual suffix infimum and nonnegative suffix cost satisfy the needed monotonicity. Pointwise prefix/tail safety composes, whereas individually budget-feasible pieces can violate the total budget.",
          [EN+"trajectory_suffix_infimum",EN+"flow_restart_trajectory_suffix",EN+"nonnegative_budget_suffix",EN+"pointwise_prefix_tail_composes",EN+"budget_prefix_tail_does_not_compose"],
          ["Actual deterministic flow law; nonnegative cost represented by an ENNReal lintegral; pointwise prefix/tail conditions."],
          ["Picard-Lindelof existence/uniqueness to the flow semigroup law, and minimum attainment versus infimum, are not proved here."])
component("viability.html::exercise-16", "For every actual finite stopped reward sequence, failuretime<=horizon, discount in[0,1), nonnegative reward upper boundR and penaltyp>=0 imply the exact geometric doomed-return bound. Supremum preserves it. The explorer's two slope candidates satisfy the bound withR=0; slow fall is strictly better exactly whenc<p(1-gamma), whileR=-c gives a false bound.",
          [VN+"finite_discounted_doomed_bound",VN+"supremum_doomed_bound",VN+"two_step_slope_bound",VN+"slow_slope_strictly_better",VN+"negative_reward_slope_bound_false"],
          ["Actual rewards before and at failure obeyr<=R; rewards vanish after failure; the penalty is charged once at arrival."],
          ["Mapping every policy of the explorer's upper slope cell to exactly one of the two displayed stopped reward sequences remains to be encoded."])
component("viability.html#practice-10", "The uniform stopped-return bound evaluates exactly to-13.49. Extending a negative reward upper bound adds negative terms and reverses the needed inequality.",
          [VN+"finite_discounted_doomed_bound",VN+"supremum_doomed_bound",VN+"doomed_example",VN+"negative_reward_extension_reverses"],
          ["The exact stopped reward model in the source."])
component("viability.html#practice-4", "In the actual two-action Boolean return table, every maximizing action is safe iffpenalty>1; atpenalty=1 the unsafe action is a maximizer.",
          [VN+"every_binary_optimizer_safe_iff",VN+"equality_retains_unsafe_optimizer"],
          ["Safe actionfalse has return0, unsafe actiontrue has return1-penalty."])
component("viability.html#practice-3", "Arrival-time penalty is exactly-14.58 at time3, compared with-20 immediately; the later penalty is strictly less costly.",
          [VN+"arrival_time_example"], ["The source's one-time arrival penalty convention."])
component("viability.html#practice-11", "For an actual metric contraction with a fixed point, residual<=e implies distance to the fixed point<=e/(1-gamma). The displayed Bellman numbers give.04.",
          [VN+"contraction_residual_bound",VN+"bellman_residual_example"],
          ["Actual contraction in the chosen metric and an actual fixed point; for the source use maximum-norm distance on finite value tables."],
          ["Finite-MDP Bellman contraction and fixed-point existence from the transition/reward model, and an explicit small-residual unsafe-policy counterexample, remain pending."])

component("toolkit-gp.html::exercise-15", "For a genuine real Mathlib RKHS, the kernel-distance inequality follows from its actual reproducing evaluation. For an SE kernel every norm<=B function is B/lengthscale-Lipschitz. Equality holds for every function when the two kernel sections coincide, and otherwise exactly for scalar multiples of their difference, including the zero function.",
          [KN+"scalar_section_reproduces",KN+"scalar_kernel_is_actual_kernel",KN+"kernel_distance_is_feature_distance",KN+"actual_rkhs_kernel_bound",KN+"actual_rkhs_se_lipschitz",KN+"actual_rkhs_kernel_equality"],
          ["A complete real inner-product space with Mathlib's actual RKHS class; positive SE lengthscale; the actual kernel is SE when that specialization is requested."],
          [])
component("toolkit-gp.html::exercise-17", "The actual finite regularized Gram system has a unique solution for positive regularization, even with dependent kernel sections. Its RKHS expansion is the unique globally minimizing function for squared loss, and evaluates to the exact solved GP-mean expression.",
          [KN+"regularized_normal_system_exists_unique",KN+"ridge_objective_gap_identity",KN+"actual_rkhs_ridge_solution",KN+"actual_rkhs_ridge_minimizer_exists_unique"],
          ["A genuine real RKHS and strictly positive regularizer; finite training data."],
          ["The lambda->0 interpolant limit and lambda->infinity asymptotic remainder are separate pending requirements."])
component("toolkit-gp.html#practice-1", "The actual two-point Gram matrix has precisely characteristic roots3/2 and1/2, with the displayed nonzero eigenvectors. The kernel-section difference evaluates to1/2 and-1/2, has squared norm1, and norm1.",
          [GN+"two_gram_eigenvectors",GN+"two_gram_characteristic_roots",GN+"two_gram_half_characteristic",GN+"two_gram_half_positive",GN+"section_difference_half",KN+"scalar_section_reproduces"],
          ["The actual kernel diagonals are1 and cross-correlation1/2; instantiate the Hilbert vectors with the genuine RKHS kernel sections."],
          [])
component("toolkit-gp.html#practice-2", "The one-observation scalar solve is uniquely defined by(prior+noise)*coefficient=observation; the posterior-formula evaluations are means8/5 and4/5 and latent variances1/5 and4/5.",
          [GN+"single_observation_solve",GN+"singleMean",GN+"singleVariance",GN+"one_observation_posteriors"],
          ["The single-observation posterior formulas are used as definitions of the deterministic calculation."],
          ["The general conditional Gaussian law that justifies these deterministic formulas is a separate pending teaching claim."])
component("toolkit-gp.html#practice-3", "The actual nonnegative square root of variance.04 is.2; the multiplier3 yields the exact band[.4,1.6]. The valid-band value.4 is below.5, giving an explicit counterexample to a threshold guarantee from this band alone.",
          [GN+"variance_standard_deviation",GN+"posterior_band_and_failure"],
          ["The true value is only known to lie in the valid band; no extra lower information is available."])
component("toolkit-gp.html#practice-4", "The square-root multiplier for b=9 is3. Every nonnegative norm has squared norm<=16 exactly when its norm<=4.",
          [GN+"confidence_convention"], ["Norms are nonnegative; both band conventions refer to the same standard deviation."])
component("toolkit-gp.html#practice-5", "The actual noiseless Hilbert-feature error bound follows from the solved zero-regularization Gram system, and the numeric power functions are.8 atb and0 ata, yielding error allowance1.6 forB=2.",
          [KN+"noiseless_posterior_error",KN+"posterior_residual_norm_identity",GN+"power_function_numeric",HN+"actual_singleton_noiseless_numeric",HN+"zero_power_function_is_exact"],
          ["Norm<=2 and exact noiseless observations; kernel diagonals1 and correlation.6."],
          [])
component("toolkit-gp.html#practice-6", "For every natural sample count the actual constant-kernel finite sum system is solved by each coefficient1/(n+1), giving variance1/(n+1). At1 and3 samples the variances are1/2 and1/4.",
          [GN+"repeated_scalar_system",GN+"repeated_variance_examples",KN+"regularized_normal_system_exists_unique"],
          ["Unit constant kernel and unit regularization; independent noisy observations under the stated model."],
          ["The singular noiseless repetition model and equality of exact-data information remain to be individually encoded."])
component("toolkit-gp.html#practice-7", "The actual determinant ofI+the displayed two-point Gram matrix is15/4; an orthogonal two-point Gram has strictly larger determinant.",
          [GN+"information_gain_determinant",GN+"realized_information_not_maximum"],
          ["The deterministic information-gain formula1/2*logdet is given."],
          [])
component("toolkit-gp.html#practice-8", "The exact multiplier reduces to2+1/2*sqrt(3+2*log20), with no approximation of log used in this equality.",
          [GN+"confidence_multiplier_exact"], ["The exercise explicitly assumes the valid-bound formula and its hypotheses."],
          ["The displayed decimal multiplier and half-width enclosure are still pending."])
component("toolkit-gp.html#practice-9", "The explicit interpolant(k(a,.)-k(b,.))/(1-r) attains values1,-1. Every other feasible RKHS function has exact squared-norm gap equal to the squared distance from this interpolant. Thus the minimum is2/(1-r), is uniquely attained, and evaluates to4 and200 at the two specified correlations.",
          [GN+"conflicting_interpolant_values",GN+"conflicting_interpolant_squared_norm",GN+"conflicting_interpolation_norm_gap",GN+"conflicting_interpolant_global_minimum",GN+"conflicting_interpolant_unique",GN+"conflicting_norm_specializations",KN+"scalar_section_reproduces"],
          ["r<1 and actual RKHS sections with inner diagonals1 and cross-inner-productr. The exercise's additional0<=r hypothesis is allowed but unnecessary."])
component("toolkit-gp.html#practice-10", "Under exactly the three assumed discrepancy/model/mean inequalities, the absolute error is at mostepsilon+(beta+epsilon*sqrt(n/lambda))*sigma. The displayed parameters give29/100 exactly.",
          [GN+"misspecification_transfer",GN+"misspecification_numeric"],
          ["Exactly the exercise's three pointwise hypotheses; the parameter substitutions have positive lambda."])
component("toolkit-gp.html#practice-12", "The two displayed regularized two-coordinate systems are each equivalent to the unique asserted solution. Their query mean/variance evaluations are1/2 and13/16; the latent Gram Schur complement is2/3.",
          [GN+"two_point_regularized_solves",GN+"two_point_query_posterior"],
          ["The deterministic GP posterior is evaluated from the source's two actual solves."],
          ["A combined full matrix-formula-to-solve theorem is still pending; scalar calculations do not prove Gaussian conditioning."])
component("toolkit-gp.html::exercise-17", "For the actual finite matrix posterior, nonsingular Gram matrices give matrix inverse, posterior mean and posterior variance convergence as regularization goes to zero. For every fixed real Gram matrix, the mean tends to zero and variance to the prior diagonal as regularization goes to infinity. Its inverse has an actual O(lambda^-3) remainder after the first two terms.",
          [MN+"inverse_zero_regularization_limit",MN+"posterior_mean_zero_regularization_limit",MN+"posterior_variance_zero_regularization_limit",MN+"inverse_infinite_regularization_limit",MN+"posterior_mean_infinite_regularization_limit",MN+"posterior_variance_infinite_regularization_limit",MN+"inverse_infinite_regularization_second_order_remainder"],
          ["Finite matrix dimensions; nonzero Gram determinant for the zero-regularization limit. The infinity limits and inverse asymptotic apply to any fixed real matrix."],
          ["The scalar posterior-mean O(lambda^-2) leading-term correspondence and the function-space minimum-norm interpolant identification still need explicit combined theorems."])
component("toolkit-gp.html::exercise-19", "For actual finite Hilbert kernel features and their uniquely solved positive-regularization posterior, posterior latent variance is nondecreasing as the regularizer increases.",
          [PN+"residual_objective_at_solution",PN+"residual_objective_gap",PN+"residual_objective_global_minimum",PN+"actual_posterior_regularization_monotone"],
          ["Same actual features/query and increasing positive regularizer."],
          ["The two stated concentration constants, log decimal enclosures, regularizer convention correspondence and derivative identity remain distinct pending claims."])

component("toolkit-gp.html::exercise-17", "The actual matrix inverse GP mean is an actual RKHS section expansion and globally minimizes squared-loss ridge for every positive regularizer. Positive-definite actual data Gram matrices give its unique minimum-norm interpolant, exact squared norm y-transpose-K-inverse-y, and convergence to that interpolant in the actual Hilbert-space norm as lambda tends to zero. The scalar large-lambda mean has the requested O(lambda^-2) leading-term error and variance tends to the actual prior diagonal.",
          [KBN+"actualGram",KBN+"actualMeanFunction",KBN+"actual_gram_entry",KBN+"positive_regularization_gram_positive_definite",KBN+"positive_regularization_determinant_nonzero",KBN+"actual_mean_is_matrix_posterior",KBN+"actual_inverse_mean_globally_minimizes_ridge",KBN+"actual_inverse_interpolant_data",KBN+"actual_inverse_interpolant_minimum_norm",KBN+"actual_inverse_interpolant_unique_minimum",KBN+"actual_inverse_interpolant_squared_norm",KBN+"actual_mean_zero_regularization_limit_in_rkhs",FFN+"posterior_mean_leading_term",MN+"posterior_variance_infinite_regularization_limit"],
          ["Genuine complete real RKHS; arbitrary finite training data; positive regularizer for ridge optimality and positive-definite actual Gram matrix for interpolation/zero limit."])

# The formerly listed two-limit gaps are now discharged by the explicit matrix-to-function bridge above.
COMPONENTS["toolkit-gp.html::exercise-17"]=[(statement,names,hypotheses,()) for statement,names,hypotheses,gaps in COMPONENTS["toolkit-gp.html::exercise-17"]]

component("toolkit-gp.html#practice-7", "A single concrete positive-semidefinite kernel on the allowed three-point domain has the displayed two-query Gram matrix and realized information(1/2)log(15/4). Another permitted design under the same kernel has information(1/2)log4, which is strictly larger. Every realized design is bounded by the actual finite-domain maximum, so the displayed design is strictly below that maximum.",
          [GDN+"designFeature",GDN+"designKernel",GDN+"actual_design_kernel_positive_semidefinite",GDN+"actual_design_kernel_entries",GDN+"actual_first_design_gram",GDN+"actual_first_design_information",GDN+"actual_alternative_design_information",GDN+"same_kernel_admissible_design_has_larger_information",GDN+"maximumInformation",GDN+"realized_information_le_actual_maximum",GDN+"displayed_information_is_not_actual_maximum"],
          ["The source's deterministic log-determinant information formula; the counterexample supplies one genuine PSD kernel and one common allowed finite domain. Repeated-query designs are included in the maximum."],
          [])

component("toolkit-gp.html#practice-8", "The original assumed confidence formula is exactly2+one-half*sqrt(3+2log20); the half-width is one-fifth of this multiplier. Rational exponential-series bounds prove log20 in(2.99573227,2.99573228), the multiplier in[3.49928854,3.49928855] and the half-width in[.699857708,.699857710]. Both printed decimal approximations have error at most half their final decimal unit.",
          [GN+"confidence_multiplier_exact",NGN+"log_twenty_enclosure",NGN+"confidenceMultiplier",NGN+"confidenceHalfWidth",NGN+"confidence_multiplier_decimal_enclosure",NGN+"confidence_multiplier_printed_rounding",NGN+"confidence_half_width_decimal_enclosure",NGN+"confidence_half_width_printed_rounding"],
          ["The confidence formula and its validity are expressly given by the exercise; these exact parameter substitutions and analytic rounding bounds do not prove stochastic assumptions."])
COMPONENTS["toolkit-gp.html#practice-8"]=[(statement,names,hypotheses,()) for statement,names,hypotheses,gaps in COMPONENTS["toolkit-gp.html#practice-8"]]

# Each promotion maps an individual exact question atom, not the whole exercise
# to an undifferentiated bag of related declarations.
PROMOTED_REQUIREMENTS = {
    "lipsdp.html#book-m12-b2": {
        1: [IQN+"coupledMultiplier",IQN+"coupled_multiplier_is_positive_semidefinite",IQN+"coupled_multiplier_exact_eigenvalues"],
        2: [IQN+"coupledIncrementQC",IQN+"actual_book_coupled_relu_failure"],
        3: [IQN+"positive_semidefiniteness_does_not_make_coupled_qc_valid",DQN+"diagonal_qc_from_actual_activations"],
    },
    "lipsdp.html#practice-easy-3": {
        1: [CSN+"unit_interval_qc_is_scalar_product",IQN+"scalar_qc_practice_values"],
        2: [IQN+"scalar_practice_admissible_pairs",CSN+"scalar_qc_iff_realizable_actual_increment"],
    },
    "lipsdp.html#practice-medium-2": {
        1: [DQN+"diagonalQC",DQN+"diagonal_qc_matrix_is_stated_block"],
        2: [IQN+"diagonal_practice_sum_is_nine",DQN+"diagonal_qc_is_actual_block_quadratic",CSN+"unit_interval_qc_is_scalar_product"],
        3: [IQN+"negative_weight_invalidates_positive_scalar_qc",DQN+"diagonal_qc_from_actual_activations",CSN+"scalar_qc_iff_realizable_actual_increment"],
    },
    "lipsdp.html::exercise-15": {
        1: [LNN+"oneHiddenNetwork",LSN+"slopeRestricted"],
        2: [LPN+"actual_spectral_matrix_gain",LPN+"slope_restricted_hidden_nonexpansive",LPN+"actual_network_product_bound"],
        3: [LPN+"layer_certificate_is_product_matrix",LPN+"product_matrix_quadratic_identity",LPN+"product_bound_is_actual_lipsdp_feasible"],
        4: [LPN+"feasibleLayerRhos",LPN+"optimalLayerRho",LPN+"actual_layer_optimization_never_exceeds_product",LWN+"walkthrough_first_actual_spectral_norm_squared",LWN+"walkthrough_last_actual_spectral_norm_squared",LWN+"walkthrough_product_feasible_point",LWN+"walkthrough_product_gain_is_four"],
    },
    "toolkit-gp.html#practice-8": {
        1: [GN+"confidence_multiplier_exact",NGN+"confidenceMultiplier"],
        2: [GN+"confidence_multiplier_exact",NGN+"log_twenty_enclosure"],
        3: [GN+"confidence_multiplier_exact",NGN+"confidenceMultiplier",NGN+"confidenceHalfWidth",NGN+"confidence_multiplier_decimal_enclosure",NGN+"confidence_multiplier_printed_rounding",NGN+"confidence_half_width_decimal_enclosure",NGN+"confidence_half_width_printed_rounding"],
    },
    "toolkit-gp.html#practice-7": {
        1: [GN+"two_gram_half_characteristic",GDN+"actual_first_design_gram"],
        2: [GDN+"actual_first_design_information"],
        3: [GDN+"actual_design_kernel_positive_semidefinite",GDN+"same_kernel_admissible_design_has_larger_information",GDN+"displayed_information_is_not_actual_maximum",GDN+"realized_information_le_actual_maximum"],
    },
    "toolkit-gp.html::exercise-17": {
        1: [KBN+"actual_mean_is_matrix_posterior",KBN+"actual_inverse_mean_globally_minimizes_ridge",KN+"actual_rkhs_ridge_minimizer_exists_unique"],
        2: [KBN+"actual_mean_zero_regularization_limit_in_rkhs",KBN+"actual_inverse_interpolant_data",KBN+"actual_inverse_interpolant_minimum_norm",KBN+"actual_inverse_interpolant_unique_minimum",KBN+"actual_mean_is_matrix_posterior",FFN+"posterior_mean_leading_term",MN+"posterior_variance_infinite_regularization_limit"],
    },
    "toolkit-gp.html#practice-1": {
        1: [GN+"twoGram",KN+"scalar_kernel_is_actual_kernel"],
        2: [GN+"twoGram",GN+"two_gram_eigenvectors",GN+"two_gram_characteristic_roots",GN+"two_gram_half_characteristic"],
        3: [GN+"section_difference_half",KN+"scalar_section_reproduces"],
    },
    "toolkit-gp.html::exercise-15": {
        1: [KN+"scalar_section_reproduces",KN+"kernel_distance_is_feature_distance",KN+"actual_rkhs_kernel_bound"],
        2: [KN+"actual_rkhs_se_lipschitz"],
        3: [KN+"actual_rkhs_kernel_equality"],
    },
    "toolkit-gp.html#practice-3": {
        1: [GN+"variance_standard_deviation"],
        2: [GN+"posterior_band_and_failure"],
        3: [GN+"posterior_band_and_failure"],
    },
    "toolkit-gp.html#practice-4": {
        1: [GN+"confidence_convention"],
        2: [GN+"confidence_convention"],
        3: [GN+"confidence_convention"],
    },
    "toolkit-gp.html#practice-5": {
        1: [HN+"singleton_residual_squared_norm"],
        2: [GN+"power_function_numeric",HN+"actual_singleton_noiseless_numeric"],
        3: [GN+"power_function_numeric",HN+"zero_power_function_is_exact"],
    },
    "toolkit-gp.html#practice-9": {
        1: [GN+"conflicting_interpolant_values"],
        2: [GN+"conflicting_interpolant_values",GN+"conflicting_interpolant_squared_norm",GN+"conflicting_interpolation_norm_gap",GN+"conflicting_interpolant_global_minimum",GN+"conflicting_interpolant_unique",GN+"conflicting_norm_specializations",KN+"scalar_section_reproduces"],
    },
    "toolkit-gp.html#practice-10": {
        1: [GN+"misspecification_transfer"],
        2: [GN+"misspecification_transfer"],
        3: [GN+"misspecification_numeric"],
    },
}

COMPLETE_REQUIREMENTS = {
    "safe-bo.html#book-m4-b1", "safe-bo.html#book-m4-b2",
    "safe-bo-theory.html#book-m5-b1", "gosafe.html#book-m6-b1",
    "gosafe.html#book-m6-b2", "viability.html#book-m7-b1",
    "nn-in-the-loop.html#book-m14-b1", "verification.html#book-m15-b1",
    "landscape.html#practice-9",
}

exercises = []
for e in INV["exercises"]:
    if e["source"] not in SOURCES:
        continue
    text = e["source_text"].replace(e["label"], "", 1).strip()
    question = re.split(r"Review if needed:|Review:|Show hint|Show answer|Hint|Worked solution", text, maxsplit=1)[0].strip()
    claims = [claim(f"{e['key']}::requirement-{i+1}", t) for i, t in enumerate(split_sentences(question))]
    for i, (statement, names, hypotheses, gaps) in enumerate(COMPONENTS.get(e["key"], [])):
        claims.append(claim(f"{e['key']}::proved-component-{i+1}", statement,
                            names, "proved", hypotheses=hypotheses,
                            correspondence="The declarations establish exactly this component under the listed hypotheses. They do not discharge the entire question by association.", gaps=gaps))
    if e["key"] == "lipsdp.html::exercise-18":
        review_rel = "book/coverage/checks/modules-logdet-source-review.json"
        source_review = json.loads((ROOT/review_rel).read_text())
        assert source_review["exercise_key"] == e["key"]
        assert source_review["exercise_text_sha256"] == e["text_sha256"]
        for source, sha in source_review["source_sha256"].items():
            assert digest(source) == sha, source
        for source, sha in source_review["proof_source_sha256"].items():
            assert digest(source) == sha, source
        review_evidence = {"file":review_rel,"sha256":digest(review_rel),
            "status":source_review["status"],"reviewer":source_review["reviewer"]}
        reviewed_claims = {c["id"]:c for c in claims}
        for component_review in source_review["components"]:
            component_id = component_review["id"]
            if component_id == "actual-eigenvalue-product":
                component_id = f"{e['key']}::proved-component-12"
            c = reviewed_claims[component_id]
            assert c["statement_in_prose"] == component_review["statement"], c["id"]
            assert c["lean_declarations"] == component_review["lean_declarations"], c["id"]
            assert component_review["status"] == "approved_precise_component", c["id"]
            c["scope_limits"] = c["remaining_gaps"]
            c["remaining_gaps"] = []
            c["independent_source_review"] = review_evidence
        for c in claims:
            if c["status"] == "pending":
                c["remaining_gaps"] = source_review["remaining_gaps"]
                c["independent_source_review"] = review_evidence
                if source_review["status"] == "approved_complete_source":
                    assert len(source_review["components"]) == 12 and not source_review["remaining_gaps"]
                    c.update(status="proved",lean_declarations=sorted({
                        name for rc in source_review["components"] for name in rc["lean_declarations"]}),
                        hypotheses=["The exact source finite real matrix, source block certificate, actual differentiability/positive-definiteness premises and stated conditional boundary limits. Explicit constructed loss/path examples support possibility and absence of universal global-optimum guarantees."],
                        correspondence="The independent exact-source review discharges all mathematical clauses using its twelve individually approved components. Specific empirical, cost, numerical implementation and local-search descriptions are separately classified; no arbitrary training convergence, blockwise gradient divergence or IEEE pipeline guarantee is inferred.")
        for number, classification in enumerate(source_review["specific_nonformal_classifications"],1):
            c = claim(f"{e['key']}::specific-source-classification-{number}",
                classification["source_clause"],status="not_a_formal_claim",
                kind=classification["kind"],correspondence=classification["reason"])
            c["remaining_gaps"] = []
            c["independent_source_review"] = review_evidence
            if "evidence" in classification:
                c["independent_empirical_evidence"] = classification
            claims.append(c)
        report_rel = "book/coverage/checks/modules-logdet-finite-difference.json"
        report = json.loads((ROOT/report_rel).read_text())
        script_rel = report["script"]
        assert report["status"] == "passed" and report["script_sha256"] == digest(script_rel)
        empirical = claim(f"{e['key']}::empirical-finite-difference-review",
            "The source's sentence about random finite differences agreeing to about 1e-9 is an empirical report, not a universal mathematical guarantee. The supplied reproduction independently checks 40 seeded source-block instances and 270 scalar derivatives in float64.",
            status="not_a_formal_claim",kind="empirical_numerical_report",
            correspondence="The exact gradient is proved in Lean separately. A reproducible NumPy float64 experiment on the literal block matrix reports maximum absolute error 1.1574808125858205e-10, below 1e-9. This supplies a new reproducible fixture; it does not recover an undocumented historical random run or validate a floating-point solver.",
            units=["lipsdp.html::node-1313"])
        empirical["remaining_gaps"] = []
        empirical["empirical_evidence"] = {"script":script_rel,"script_sha256":digest(script_rel),
            "report":report_rel,"report_sha256":digest(report_rel),"observed_max_absolute_error":report["max_absolute_error"],
            "case_count":report["case_count"],"scalar_derivative_count":report["scalar_derivative_count"]}
        claims.append(empirical)
    complete = e["key"] in COMPLETE_REQUIREMENTS
    if e["key"] == "lipsdp.html::exercise-18":
        complete = source_review["status"] == "approved_complete_source" and all(
            c["status"] != "pending" and not c["remaining_gaps"] for c in claims)
    if complete:
        names = sorted({name for _statement, ds, _hypotheses, _gaps in COMPONENTS[e["key"]] for name in ds})
        for c in claims:
            c["remaining_gaps"] = []
            if c["status"] == "pending":
                c.update(status="proved",lean_declarations=names,remaining_gaps=[],
                         correspondence="The explicitly mapped component declarations jointly discharge this exact question requirement; arithmetic substitutions and certificate meanings are stated above. Physical model validity and pedagogical advice are not inferred as theorems.")
    if e["key"] in PROMOTED_REQUIREMENTS:
        for atom, names in PROMOTED_REQUIREMENTS[e["key"]].items():
            c=claims[atom-1]
            assert c['id'].endswith(f"::requirement-{atom}"), (e['key'],atom)
            c.update(status="proved",lean_declarations=names,remaining_gaps=[],
                     hypotheses=["The exact source givens and the mapped component theorem hypotheses, with genuine RKHS sections used for RKHS claims."],
                     correspondence="This exact question atom is discharged by the listed declarations. Scenario givens instantiate their parameters; proofs of function-space claims use actual RKHS reproducing sections. An unavailable certificate is refuted by the explicit admitted-band value. Printed answer approximations remain separate material claims.")
        complete=all(c['status']!='pending' and not c['remaining_gaps'] for c in claims)
    if e['source']=='SafeLearning/lipsdp.html' and e['key'] in PROMOTED_REQUIREMENTS:
        for c in claims:
            c['hypotheses']=["Arbitrary finite real layer matrices, actual elementwise activation with every chord slope in [0,1], arbitrary biases, and Euclidean induced operator norms."]
            c['correspondence']="The listed declarations establish this exact source atom using actual functions, actual quadratic forms and exact supplied matrices. Spectral norms are Euclidean induced norms. Actual globally slope-restricted linear functions realize the admissible scalar pairs; explicit actual ReLU pairs refute invalid coupled constraints. The product optimization proof bounds the infimum of actual feasible objectives. Further optimized walkthrough values remain separate material claims."
    if e["key"] == "lipschitz-by-design.html::exercise-15":
        cayley_review_rel = "book/coverage/checks/modules-cayley-source-review.json"
        cayley_review = json.loads((ROOT/cayley_review_rel).read_text())
        assert cayley_review["exercise_key"] == e["key"]
        assert cayley_review["exercise_text_sha256"] == e["text_sha256"]
        for source, sha in {**cayley_review["source_sha256"],**cayley_review["proof_source_sha256"]}.items():
            assert digest(source) == sha, source
        cayley_evidence = {"file":cayley_review_rel,"sha256":digest(cayley_review_rel),
            "reviewer":cayley_review["reviewer"],"status":cayley_review["status"]}
        approved_components = {}
        for reviewed in cayley_review["components"]:
            c = next(c for c in claims if c["id"] == reviewed["id"])
            assert c["statement_in_prose"] == reviewed["statement"]
            assert c["lean_declarations"] == reviewed["lean_declarations"]
            assert reviewed["status"] == "approved_precise_component"
            c["independent_source_review"] = cayley_evidence
            approved_components[int(c["id"].rsplit("-",1)[1])] = c
        assert set(approved_components) == {1,2,3}
        claims[0].update(status="not_a_formal_claim",kind="explicit_source_given",remaining_gaps=[],
            correspondence="The clause supplies skew symmetry as the explicit premise of the following requested theorem.",
            independent_source_review=cayley_evidence)
        for index,components in [(1,[1]),(2,[2,3])]:
            claims[index].update(status="proved",remaining_gaps=[],
                lean_declarations=sorted({name for i in components for name in approved_components[i]["lean_declarations"]}),
                hypotheses=[hyp for i in components for hyp in approved_components[i]["hypotheses"]],
                correspondence="This exact source atom is discharged by the individually approved Cayley components. The source matrix is the actual rational transform, the angle has the correct sign, the decimal has an analytic error bound, and omitted matrices are characterized exactly.",
                independent_source_review=cayley_evidence)
        complete = all(c["status"] != "pending" and not c["remaining_gaps"] for c in claims)
    exercises.append({"inventory_key": e["key"], "source": e["source"], "locator": e["locator"],
                      "label": e["label"], "source_sha256": e["source_sha256"],
                      "source_text_sha256": e["text_sha256"], "claims": claims,
                      "status": "complete_math" if complete else "partial" if COMPONENTS.get(e["key"]) else "pending"})

material = []
LOGDET_REVIEW_UNIT_COMPONENTS = {
    "lipsdp.html::node-1312": [1,5,12],
    "lipsdp.html::node-1313": [1],
    "lipsdp.html::node-1314": [1,2,7,8,9,10,11],
    "lipsdp.html::node-1315": [3,4],
    "lipsdp.html::node-1316": [6],
}
LIPSDP_UNIT_MAP = {
    267: [DQN+"scalar_qc_factorization",DQN+"scalar_qc_iff_admissible_chord"],
    271: [DQN+"scalar_qc_factorization",LSN+"scalar_slope_quadratic_constraint"],
    272: [DQN+"scalar_qc_iff_admissible_chord",LSN+"scalar_slope_quadratic_constraint"],
    273: [DQN+"scalar_qc_factorization"],
    276: [DQN+"diagonal_qc_matrix_is_stated_block",DQN+"diagonal_qc_is_actual_block_quadratic",DQN+"scalarQC"],
    277: [CSN+"unit_interval_qc_is_scalar_product",DQN+"scalar_qc_iff_admissible_chord",IQN+"positive_semidefiniteness_does_not_make_coupled_qc_valid"],
    279: [DQN+"diagonal_qc_matrix_is_stated_block",DQN+"diagonal_qc_is_actual_block_quadratic",DQN+"diagonal_qc_from_actual_activations"],
    282: [DQN+"diagonal_qc_matrix_is_stated_block",DQN+"diagonal_qc_is_actual_block_quadratic",DQN+"diagonal_qc_from_actual_activations"],
    285: [DQN+"all_diagonal_qcs_iff_coordinate_qcs",DQN+"scalar_qc_iff_admissible_chord",DQN+"all_diagonal_qcs_iff_independent_diagonal_slopes",DQN+"diagonal_qc_is_actual_block_quadratic",IQN+"positive_semidefiniteness_does_not_make_coupled_qc_valid"],
    302: [IQN+"actual_slope_restriction_implies_sector",DQN+"scalar_qc_factorization",SECN+"nonmonotoneSectorActivation",SECN+"actual_nonmonotone_sector_formula",SECN+"actual_nonmonotone_function_obeys_sector",SECN+"sector_bounded_function_need_not_be_monotone",SECN+"sector_bounded_function_need_not_be_slope_restricted"],
    327: [LNN+"blockCertificate",LNN+"canonical_certificate_is_stated_block_matrix",LNN+"actual_block_matrix_certificate_bounds_network"],
}
for u in INV["material_source_units"]:
    if u["source"] not in SOURCES:
        continue
    c=claim(u["key"]+"::claim-review", u["source_text"],
            kind="mathematical_source_unit_needs_granular_review", units=[u["key"]])
    if u["key"] in LOGDET_REVIEW_UNIT_COMPONENTS and source_review["status"] == "approved_complete_source":
        component_indices = LOGDET_REVIEW_UNIT_COMPONENTS[u["key"]]
        components = [source_review["components"][i-1] for i in component_indices]
        c.update(status="proved",kind="independently_reviewed_mathematical_clauses_with_explicit_nonformal_classification",
            lean_declarations=sorted({name for component in components for name in component["lean_declarations"]}),
            hypotheses=[hyp for component in components for hyp in component["hypotheses"]],
            correspondence="The independently reviewed components discharge the mathematical clauses of this exact answer unit. Empirical checks and unspecified implementation/runtime/local-search descriptions remain explicitly classified, without claiming a universal numerical experiment, optimizer convergence or floating-point pipeline theorem.",remaining_gaps=[],
            independent_source_review=review_evidence,
            scope_limits=source_review["limits"],
            nonformal_source_classifications=source_review["specific_nonformal_classifications"])
    if u["key"] in {"lipschitz-by-design.html::node-310","lipschitz-by-design.html::node-312"}:
        c.update(status="proved",kind="actual_cayley_bijection_theorem",remaining_gaps=[],
            lean_declarations=COMPONENTS["lipschitz-by-design.html::exercise-15"][0][1]+[
                CYIN+"actual_inverse_cayley_is_source_inverse_formula",CYIN+"actual_inverse_cayley_is_skew_symmetric",
                CYIN+"actual_inverse_cayley_recovers_orthogonal",CYIN+"actual_inverse_cayley_recovers_skew",
                CYIN+"actual_cayley_preimage_is_unique",CYIN+"actual_orthogonal_denominator_invertible_iff_no_negative_one_eigenvector",
                CYIN+"actual_orthogonal_without_negative_one_has_unique_skew_preimage"],
            hypotheses=["Arbitrary actual finite real square matrices; actual skew symmetry for the forward transform, actual orthogonality and exclusion of a nonzero -1 eigenvector for the inverse domain."],
            correspondence="The actual transform has invertible denominator, orthogonal output and determinant one. The actual rational inverse is skew symmetric, both compositions are exact, and the preimage is unique. Eigenvector exclusion is proved equivalent to denominator invertibility. The bibliographic attribution is separate from these mathematical assertions.",
            independent_source_review=cayley_evidence)
    if u["key"] == "lipschitz-by-design.html::node-1328":
        c.update(status="proved",kind="actual_two_dimensional_cayley_formula_angle_and_exact_range",remaining_gaps=[],
            lean_declarations=COMPONENTS["lipschitz-by-design.html::exercise-15"][1][1]+COMPONENTS["lipschitz-by-design.html::exercise-15"][2][1],
            hypotheses=["The actual real scalar two-dimensional skew matrix from the source. The angle is the principal real2*arctan(a); degrees are180/pi times this angle."],
            correspondence="Exact matrix inversion/multiplication, trigonometric coordinates, open angle interval, a=1/2 sample matrix, analytic53.13-degree rounding and the exact omitted orthogonal matrices are individually approved by the independent Exercise13.1 review.",
            independent_source_review=cayley_evidence)
    if u["key"] == "lipschitz-by-design.html::node-335":
        assert u["key"] in cayley_review["approved_complete_material_unit_keys"]
        c.update(status="proved",kind="corrected_complex_background_and_actual_cayley_bijection",remaining_gaps=[],
            lean_declarations=[CLBN+name for name in ["actual_imaginary_unit_squared","actual_complex_conjugate_coordinates",
                "actual_complex_modulus_squared_coordinates","actual_complex_modulus_squared_is_conjugate_product",
                "actual_matrix_adjoint_entries","actual_matrix_hermitian_definition","actual_matrix_unitarity_definition",
                "actual_complex_vector_squared_norm_is_adjoint_product","actual_imaginary_matrix_is_skew_hermitian",
                "actual_imaginary_matrix_is_unitary"]]+[
                CLCN+"actual_complex_skew_denominator_is_invertible",CLCN+"actual_complex_cayley_is_unitary",
                CLCN+"actual_complex_cayley_determinant_has_unit_norm",CLCN+"actual_complex_cayley_has_no_negative_one_eigenvector",
                CLIN+"actual_inverse_cayley_is_source_inverse_formula",CLIN+"actual_inverse_cayley_is_skew_hermitian",
                CLIN+"actual_inverse_cayley_recovers_unitary",CLIN+"actual_inverse_cayley_recovers_skew",
                CLIN+"actual_unitary_without_negative_one_has_unique_skew_preimage",
                CCN+"actual_imaginary_cayley_is_negative_imaginary",CCN+"actual_imaginary_cayley_determinant_is_not_one"],
            hypotheses=["Actual finite complex matrices and Euclidean vector norm; arbitrary real scalar coordinates. The Cayley input is actually skew-Hermitian and the inverse domain is actually unitary with no nonzero -1 eigenvector."],
            correspondence="The independent reviewer approves all corrected mathematical clauses: genuine complex conjugation, modulus and adjoint identities; actual vector norm-square product; typed Hermitian/unitary definitions; actual [i] example; generic Cayley invertibility/unitarity/exclusion/bijection and determinant norm1. The explicit [-i] determinant counterexample justifies restricting determinant+1 to the real theorem.",
            independent_source_review=cayley_evidence)
    lipnode=u['key'].removeprefix('lipsdp.html::node-')
    if lipnode.isdigit() and int(lipnode) in LIPSDP_UNIT_MAP:
        c.update(kind="actual_incremental_quadratic_constraint_and_matrix_correspondence",status="proved",
                 lean_declarations=LIPSDP_UNIT_MAP[int(lipnode)],
                 hypotheses=["Ordered real slope bounds alpha<=beta, actual finite real scalar/diagonal quadratic forms, actual slope-restricted elementwise activations and nonnegative diagonal weights where required."],
                 correspondence="The scalar factorization, zero-coordinate case and admissible-chord equivalence establish the displayed scalar formulas. The actual block matrix equals the exact weighted coordinate sum, proving the diagonal lemma and its converse with independent admissible slopes. The explicit actual ReLU counterexample establishes the danger of coupling. The displayed network LMI is encoded as the exact canonical block matrix and its negative semidefiniteness implies the actual network gain; it is not asserted feasible for arbitrary parameters.",remaining_gaps=[])
        if int(lipnode)==302:
            c['hypotheses']=["A genuine slope-restricted scalar activation with activation(0)=0 for the forward implication; the explicit real function x/(1+x²) for the converse counterexample."]
            c['correspondence']="Taking the actual increment against zero proves the static sector condition. The scalar factorization identifies the source's sector product with its 2-by-2 quadratic form. The actual function x/(1+x²) has zero origin and satisfies this sector inequality at every real input, while its values at1 and2 decrease, proving it is not monotone and not [0,1] slope-restricted."
    if u['key']=='toolkit-gp.html::node-164':
        c.update(kind="established_mathematical_theorem_and_proof",status="proved",
                 lean_declarations=[RN+"every_regularized_minimizer_has_finite_representation",RN+"actual_rkhs_representer_theorem"],
                 hypotheses=["Finite sample indices, genuine real RKHS, positive regularizer, arbitrary loss and an actual global minimizer."],
                 correspondence="The arbitrary-loss representer theorem is proved by projection onto the finite-dimensional section span, unchanged data evaluations, Pythagorean norm decomposition and strict regularization penalty. It asserts the structure of every existing minimizer; it does not assert existence for an arbitrary loss.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-162':
        c.update(kind="established_kernel_pseudometric_claim",status="proved",
                 lean_declarations=[QN+"kernel_distance_squared_identity",QN+"kernel_distance_nonnegative",QN+"kernel_distance_self",QN+"kernel_distance_symmetric",QN+"kernel_distance_triangle",QN+"kernel_distance_zero_iff",QN+"constant_kernel_does_not_separate",QN+"kernel_distance_separates_iff_injective",QN+"strictly_positive_two_point_gram_gives_injectivity"],
                 hypotheses=["Actual Hilbert kernel sections; strict-positive-definite kernels have positive definite Gram matrices on every distinct two-point set."],
                 correspondence="The kernel distance is the actual feature-space distance, proving the pseudometric axioms. The constant-feature Boolean example supplies distinct zero-distance inputs. Exact separation is equivalent to feature injectivity; actual strictly positive two-point Gram matrices force this injectivity.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-137':
        c.update(kind="finite_kernel_expansion_identity",status="proved",
                 lean_declarations=[JN+"constructed_finite_expansion_evaluates",JN+"constructed_finite_expansion_squared_norm"],
                 hypotheses=["Any scalar positive-semidefinite kernel and its actual completed RKHS; arbitrary finite section expansion."],
                 correspondence="The actual constructed RKHS section expansion evaluates as the stated kernel sum and its squared norm is the Gram quadratic form. The description as a bump is an informal name; it does not assert localization of every kernel.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-138':
        c.update(kind="actual_rkhs_definition_and_reproduction",status="proved",
                 lean_declarations=[JN+"constructedSpace",JN+"constructed_sections_reproduce",KN+"scalar_section_reproduces"],
                 hypotheses=["Scalar positive-semidefinite kernel for the construction; genuine RKHS class for the general reproducing identity."],
                 correspondence="The Hilbert space is an actual completion, equipped with the RKHS class and its inherited norm. Its genuine kernel section inner product equals evaluation.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-153':
        c.update(kind="bounded_linear_evaluation_functional",status="proved",
                 lean_declarations=[SSN+"evaluationFunctional",SSN+"evaluation_functional_evaluates",SSN+"evaluation_functional_is_linear",SSN+"evaluation_functional_is_bounded",KN+"scalar_section_reproduces",KN+"scalar_kernel_is_actual_kernel",QN+"kernelDistance",QN+"kernel_distance_squared_identity"],
                 hypotheses=["Genuine complete real scalar-valued RKHS and its actual kernel sections."],
                 correspondence="Evaluation is an actual continuous linear map, satisfies the displayed linearity and bound, and is represented by the actual reproducing section. The kernel pseudometric is the Hilbert distance between these same sections.",remaining_gaps=[])
    if u['key'] in {'toolkit-gp.html::node-127','toolkit-gp.html::node-154'}:
        c.update(kind="concrete_linear_kernel_rkhs_example",status="proved",
                 lean_declarations=[SSN+"linearRKHS",SSN+"linearFunction",SSN+"linear_function_evaluation",SSN+"linear_function_norm_and_evaluation",SSN+"linear_reproducing_property",SSN+"linear_representing_function",FFN+"actual_linear_kernel_section",FFN+"actual_linear_kernel_formula",KN+"scalar_section_reproduces",QN+"point_evaluation_bound"],
                 hypotheses=["The actual one-dimensional real coefficient RKHS with evaluation f(x)=a*x; general evaluation claims use genuine RKHS sections."],
                 correspondence="The coefficient Hilbert space has an actual injective RKHS function embedding. Its actual Mathlib kernel is x*z and its actual section coefficient is x. Coefficient norm is absolute value; evaluation at 2 and the representing function 2*x have precisely the displayed formulas. The general reproducing and Cauchy–Schwarz rules are proved for arbitrary actual RKHSs. The primer pointer is pedagogical.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-144':
        c.update(kind="moore_aronszajn_rkhs_construction_and_evaluation",status="proved",
                 lean_declarations=[JN+"scalar_kernel_operator_positive",JN+"constructedSpace",JN+"constructed_kernel_is_given",JN+"constructed_sections_reproduce",JN+"constructed_finite_expansion_evaluates",JN+"constructed_finite_expansion_squared_norm",JN+"constructed_kernel_sections_dense",SSN+"finite_expansion_cross_inner",SSN+"rkhs_with_same_kernel_unique",SSN+"evaluationFunctional",SSN+"evaluation_functional_evaluates",SSN+"evaluation_functional_is_linear",SSN+"evaluation_functional_is_bounded",HN+"equal_evaluations_equal_functions",HN+"equal_evaluations_equal_norms",QN+"norm_zero_is_zero_function",KN+"scalar_section_reproduces",KN+"scalar_kernel_is_actual_kernel",QN+"kernelDistance",QN+"kernel_distance_squared_identity",SSN+"linearRKHS",SSN+"linear_function_evaluation",SSN+"linear_function_norm_and_evaluation",FFN+"actual_linear_kernel_section",FFN+"actual_linear_kernel_formula"],
                 hypotheses=["Scalar positive-semidefinite kernel on any input type; actual completed real scalar-valued RKHS. Uniqueness concerns genuine complete RKHSs with the same kernel."],
                 correspondence="The space is Mathlib's actual uniform completion of finite kernel expansions, with a dense section span. Evaluation and mixed-inner/norm formulas use actual kernel functions. Function equality preserves norm, and norm zero is the zero function, including singular Gram representations. Every scalar PSD kernel supplies this actual completed RKHS. Uniqueness is expressed by an evaluation-preserving linear isometry between same-kernel Hilbert spaces, the precise meaning of a unique Hilbert function space. The bounded evaluator and the embedded concrete linear-kernel example are also proved.",remaining_gaps=[])
    if u['key'] in {'toolkit-gp.html::node-337','toolkit-gp.html::node-338','toolkit-gp.html::node-340','toolkit-gp.html::node-342','toolkit-gp.html::node-358'}:
        c.update(kind="actual_noise_free_minimum_norm_interpolation",status="proved",
                 lean_declarations=[KBN+"actualMeanFunction",KBN+"actual_mean_is_matrix_posterior",KBN+"actual_inverse_interpolant_data",KBN+"actual_inverse_interpolant_minimum_norm",KBN+"actual_inverse_interpolant_unique_minimum",KBN+"actual_inverse_interpolant_squared_norm",KBN+"actual_mean_zero_regularization_limit_in_rkhs",MN+"posterior_variance_zero_regularization_limit",IPN+"queryVector",IPN+"queryWeights",IPN+"powerSquared",IPN+"actual_query_weights_solve",IPN+"actual_power_is_squared_residual_norm",IPN+"actual_power_nonnegative",IPN+"inverse_interpolant_is_query_weight_prediction",IPN+"actual_noise_free_interpolation_error",IPN+"actual_noise_free_interpolation_bound_sharp",KN+"interpolant_norm_gap"],
                 hypotheses=["Genuine complete scalar real RKHS, finite noiseless data and positive-definite actual data Gram matrix. Sharpness uses a nonnegative radius and nonzero query residual; when residual is zero the bound is identically zero."],
                 correspondence="The interpolant is the actual inverse-Gram RKHS section expansion, with exact data reproduction, global minimum norm and a unique minimum. It is the Hilbert-norm limit of the actual GP means. The actual power-function squared is the matrix expression and is proved equal to the squared Hilbert residual norm. The deterministic error theorem applies to every actual RKHS function, and an actual norm-B zero-data function attains the bound for every nonzero residual. The matrix-variance limit follows by instantiating the general zero-regularization theorem with these query vectors. The Pythagorean norm gap follows from the solved Gram system and data orthogonality.",remaining_gaps=[])
    if u['key'] in {'toolkit-gp.html::node-75','toolkit-gp.html::node-77','toolkit-gp.html::node-79'}:
        names={'toolkit-gp.html::node-75':[GN+"single_observation_solve"],
               'toolkit-gp.html::node-77':[NGN+"standard_deviation_of_nine_hundredths"],
               'toolkit-gp.html::node-79':[NGN+"general_inner_product_bound"]}[u['key']]
        c.update(kind="mathematical_prerequisite_check",status="proved",lean_declarations=names,
                 hypotheses=["Exact displayed real scalar data; a real inner-product space for Cauchy–Schwarz."],
                 correspondence="The exact scalar solve, true nonnegative square root, or general absolute inner-product inequality is proved. The review link is pedagogical.",remaining_gaps=[])
    if u['key']=='toolkit-gp.html::node-1085':
        c.update(kind="realized_information_exact_value_and_rounding",status="proved",
                 lean_declarations=[GN+"information_gain_determinant",GDN+"actual_first_design_information",NGN+"log_fifteen_fourths_enclosure",NGN+"information_gain_printed_rounding"],
                 hypotheses=["The displayed unit-noise two-point Gram matrix and the given natural-log information formula."],
                 correspondence="The determinant is exactly15/4, the realized information is one-half the natural logarithm of that number, and the printed six-decimal number has error at most half its final decimal unit by analytic exponential-series enclosure.",remaining_gaps=[])
    material.append(c)

# Additional proved material claims are tied to exact current units by phrase.
material_groups = [
    ("lipsdp", "log", "The actual determinant and logdet Frechet derivatives on arbitrary finite real matrices are proved through the continuous alternating determinant, its actual row-update derivative, Cramer's identity and the actual matrix inverse. The actual source neural barrier matrix has the exact W0 Frobenius gradient -2 Lambda (Ninv)21; composing an actual differentiable training loss gives gradLoss+2 mu Lambda (Ninv)21.", [LDN+"actual_determinant_multilinear_derivative",LDN+"actual_determinant_has_frechet_derivative",LDN+"actual_logdet_has_frechet_derivative",LDN+"actual_logdet_curve_derivative",BGN+"barrierMatrix",BGN+"actual_barrier_matrix_weight_derivative",BGN+"actual_variation_trace_splits_into_weight_blocks",BGN+"actual_symmetric_variation_trace_is_gradient",BGN+"actual_logdet_barrier_weight_gradient",BGN+"actual_barrier_training_weight_gradient"]),
    ("lipsdp", "MaxMin", "Actual two-coordinate MaxMin preserves the coordinate sum and squared Euclidean norm and is Euclidean nonexpansive. Its actual input/output increments nevertheless violate the elementwise [0,1] diagonal neuron QC at the explicit pair (0,1),(0,0), so that certificate assumption cannot be transferred to this activation.", [SECN+"maxMin",SECN+"actual_maxmin_violates_elementwise_diagonal_qc",SECN+"maxmin_preserves_sum",SECN+"maxmin_preserves_squared_norm",SECN+"maxmin_is_euclidean_nonexpansive"]),
    ("lipsdp", "semidefinite program", "The actual arbitrary-dimensional one-hidden-network certificate is affine in the squared gain and diagonal multipliers. Its actual nonnegative and negative-semidefinite feasible parameter set is convex; the squared-gain objective is convex on this set and every actual local minimum on the feasible set is a global minimum.", [LCN+"actual_block_certificate_is_affine",LCN+"feasibleNeuronParameters",LCN+"actual_neuron_sdp_feasible_set_is_convex",LCN+"actual_neuron_sdp_objective_is_convex",LCN+"actual_neuron_sdp_has_no_nonglobal_local_minimum",LCN+"diagonal_multiplier_cone_is_convex"]),
    ("lipsdp", "What the QC knows", "The actual diagonal quadratic constraints hold for every nonnegative diagonal multiplier exactly when the hidden increment equals D times the preactivation increment for some independent diagonal slopes in [alpha,beta]. The proof handles zero increments explicitly and derives every coordinate condition by singleton multipliers. The block form is proved equal to the scalar-coordinate sum, and actual possibly different elementwise activations satisfy it.", [DQN+"scalar_qc_factorization",DQN+"scalar_qc_iff_admissible_chord",DQN+"diagonal_qc_from_actual_activations",DQN+"all_diagonal_qcs_iff_coordinate_qcs",DQN+"all_diagonal_qcs_iff_independent_diagonal_slopes",DQN+"diagonal_qc_matrix_is_stated_block",DQN+"diagonal_qc_is_actual_block_quadratic"]),
    ("lipsdp", "product bound", "For arbitrary finite-dimensional one-hidden-layer networks with [0,1] chord slopes, the actual Euclidean induced matrix norms give the product gain. The exact layer LMI is negative semidefinite at T=norm(W1)^2 I and rho=norm(W1)^2 norm(W0)^2, including zero weights; the infimum of feasible layer objectives therefore gives no larger gain. The walkthrough norms squared are exactly 8 and 2 and its product feasible point is (2I,16), gain4.", [LPN+"actual_network_product_bound",LPN+"product_bound_is_actual_lipsdp_feasible",LPN+"actual_layer_optimization_never_exceeds_product",LWN+"walkthrough_first_actual_spectral_norm_squared",LWN+"walkthrough_last_actual_spectral_norm_squared",LWN+"walkthrough_product_feasible_point",LWN+"walkthrough_product_gain_is_four"]),
    ("lipsdp", "slope", "Every actual slope-restricted scalar activation obeys the incremental quadratic constraint; ReLU satisfies the full [0,1] chord restriction. Summing nonnegative diagonal multipliers gives the finite lifted certificate, whose actual negative-semidefinite matrix implies the Euclidean output gain bound.", [LSN+"scalar_slope_quadratic_constraint",LSN+"relu_slope_restricted",LSN+"certificate_quadratic_identity",LSN+"finite_lifted_lipsdp_soundness"]),
    ("lipsdp", "one-hidden", "For the actual affine/elementwise/affine one-hidden-layer network, the canonical lifted certificate is exactly the stated block LMI. Its negative semidefiniteness bounds every actual output increment by sqrt(rho) times the Euclidean input increment; the proof derives the hidden relation and cancels both biases.", [LNN+"hiddenValues",LNN+"oneHiddenNetwork",LNN+"blockCertificate",LNN+"canonical_certificate_is_stated_block_matrix",LNN+"actual_network_lipsdp_soundness",LNN+"actual_block_matrix_certificate_bounds_network"]),
    ("landscape", "T_{t+1}", "The sampled thermal interval[15,60] is invariant for every admissible input/disturbance sequence.", [BN+"thermal_step",BN+"thermal_all_samples"]),
    ("toolkit-lmi", "Q=I", "The displayed two-dimensional thermal map has the stated exact quadratic decrease, strict away from zero.", [BN+"thermal_energy_identity",BN+"thermal_energy_strict"]),
    ("toolkit-lmi", "Schur", "The arbitrary-finite-dimensional positive block Schur complement equivalence holds with a positive definite invertible corner.", [TN+"positive_block_schur",TN+"positive_block_schur_lower"]),
    ("toolkit-gp", "midpoint", "The displayed midpoint solves yield exact mean6/7 and variance10/7; the original/revised nominal decisions are separated by exact square-root inequalities.", [BN+"gp_midpoint_linear_solutions",BN+"gp_midpoint_unique_solution",BN+"gp_midpoint_reject_accept"]),
    ("safe-bo-theory", "[-1,1.55]", "The two LoSBO cone intervals have the displayed exact union.", [BN+"losbo_cones",BN+"losbo_union"]),
    ("viability", "K_1", "The discrete thermal predecessor stabilizes at four states and its viable-action counts are1,1,2,1.", [FN+"thermal_predecessor_cap60",FN+"thermal_predecessor_fixed",FN+"thermal_viable_action_count"]),
    ("lipsdp", "negative semidefinite", "The complete displayed four-variable SDP quadratic form equals a sum of negative squares, hence is negative semidefinite for every vector.", [BN+"lipsdp_sum_of_squares",BN+"lipsdp_negative_semidefinite"]),
    ("lipschitz-by-design", "0.012", "The stated exact architectural gain.3 times the normalized sensor radius is strictly less than.012.", [BN+"architecture_sensor_budget"]),
    ("nn-in-the-loop", "derivative", "The actual tanh derivative proves the closed-loop map is globally.9-Lipschitz and contracts about the origin.", [TN+"tanh_derivative",TN+"neural_thermal_derivative",TN+"neural_thermal_lipschitz",TN+"neural_thermal_origin_contraction"]),
    ("verification", "exact range", "Exhaustive ReLU regions establish the original exact range[0,.3] with attained extrema and the deterministic temperature bound59.95.", [BN+"verification_left_region",BN+"verification_middle_region",BN+"verification_right_region",BN+"verification_original_range",BN+"verification_extrema_attained",BN+"deterministic_temperature_pass"]),
    ("safe-bo-theory", "heteroscedastic", "The actual all-round asymmetric-noise cone update is safe under the upper error envelope alone, independent of GP beta.", [EN+"asymmetric_noise_query_safety",EN+"lipschitz_query_safety"]),
    ("safe-bo-theory", "Hölder", "Actual Holder regularity gives all-round cone safety and the exact general inverse radius for every positive exponent and nonnegative slack.", [EN+"holder_query_safety",EN+"holder_general_radius"]),
    ("gosafe", "suffix", "A trajectory suffix has no smaller infimum margin; nonnegative suffix cost cannot exceed full cost; pointwise safety composes across a switch.", [EN+"trajectory_suffix_infimum",EN+"nonnegative_budget_suffix",EN+"pointwise_prefix_tail_composes"]),
    ("viability", "R_{X_U}", "Every stopped reward sequence with nonnegative upper bound and uniformly bounded failure time obeys the exact geometric doomed-return bound.", [VN+"finite_discounted_doomed_bound",VN+"supremum_doomed_bound"]),
    ("viability", "residual", "An actual metric contraction's residual bounds distance to its fixed point byresidual/(1-discount).", [VN+"contraction_residual_bound"]),
    ("toolkit-gp", "bounded linear", "In an actual scalar-valued RKHS, point evaluation is a bounded continuous linear functional; same-kernel RKHSs are related by an evaluation-preserving linear isometry, and mixed finite expansion inner products equal the cross-kernel double sum.", [SSN+"evaluationFunctional",SSN+"evaluation_functional_evaluates",SSN+"evaluation_functional_is_linear",SSN+"evaluation_functional_is_bounded",SSN+"rkhs_with_same_kernel_unique",SSN+"finite_expansion_cross_inner"]),
    ("toolkit-gp", "Moore", "Every scalar PSD kernel has an actual completed RKHS with precisely that kernel, actual reproducing sections, a dense section span and the stated finite expansion evaluation/squared-norm identities.", [JN+"scalar_kernel_operator_positive",JN+"constructedSpace",JN+"constructed_kernel_is_given",JN+"constructed_sections_reproduce",JN+"constructed_finite_expansion_evaluates",JN+"constructed_finite_expansion_squared_norm",JN+"constructed_kernel_sections_dense"]),
    ("toolkit-gp", "P_t(x)", "The solved noiseless Gram residual is orthogonal to every observed section. A norm-B function proportional to the residual attains the exact power-function error whenever the residual is nonzero; zero power implies exact reproduction for every function.", [HN+"noiseless_residual_orthogonal",HN+"sharp_residual_function_norm",HN+"sharp_residual_function_has_zero_data",HN+"sharp_residual_function_attains_error",HN+"zero_power_function_is_exact"]),
    ("toolkit-gp", "posterior variance", "For the actual solved finite kernel posterior, variance is the global minimum of the feature residual quadratic and is nondecreasing in regularization.", [PN+"residual_objective_at_solution",PN+"residual_objective_gap",PN+"residual_objective_global_minimum",PN+"actual_posterior_regularization_monotone"]),
    ("toolkit-gp", "lambda", "The actual fixed finite matrix posterior has zero-regularization interpolation-formula limits for nonsingular Gram matrices, infinite-regularization mean/variance limits, and an O(lambda^-3) inverse remainder.", [MN+"posterior_mean_zero_regularization_limit",MN+"posterior_variance_zero_regularization_limit",MN+"posterior_mean_infinite_regularization_limit",MN+"posterior_variance_infinite_regularization_limit",MN+"inverse_infinite_regularization_second_order_remainder",FFN+"posterior_mean_leading_term",FFN+"posterior_mean_second_order_remainder",FFN+"posterior_variance_second_order_remainder"]),
]
material_groups.append(("lipschitz-by-design", "T^{-1}", "The exact finite residual-layer energy identity and literal source QC margin imply actual Euclidean nonexpansiveness whenever the actual source diagonal is strictly positive, the actual certificate is PSD and the actual activation has incremental slopes[0,1]. The analytic source diagonal is nonnegative and strictly positive for nonzero weight columns; its source-scaled residual layer then inherits the actual bound. Named activation wrappers, literal Gershgorin similarity/discs and the full epsilon-regularized certificate remain distinct pending claims.", COMPONENTS["lipschitz-by-design.html::exercise-16"][1][1]))
material_groups.append(("lipschitz-by-design", "eigenvalues $0,2$", "The actual source two-by-two weights yield both literal scaled diagonals and actual PSD certificate differences, their exact characteristic polynomials and spectral values, and actual unit-vector witnesses that neither diagonal majorizes the other. The final printed SN spectral-norm formula and decimal remain pending.", COMPONENTS["lipschitz-by-design.html::exercise-16"][2][1]))
material_groups.append(("lipschitz-by-design", "Complex matrices", "The actual 1-by-1 complex skew-Hermitian matrix [i] has actual unitary Cayley transform [-i], with determinant -i rather than1. Thus the real determinant-one conclusion cannot be carried over verbatim to the complex theorem. This exact counterexample supports correction10; the corrected generic complex invertibility/unitarity/exclusion/bijection claims remain a separate pending source requirement.", [CCN+"actualImaginarySkew",CCN+"actualComplexCayley",CCN+"actual_imaginary_matrix_is_skew_hermitian",CCN+"actual_imaginary_cayley_denominator_inverse",CCN+"actual_imaginary_cayley_is_negative_imaginary",CCN+"actual_imaginary_cayley_is_unitary",CCN+"actual_imaginary_cayley_determinant_is_not_one",CCN+"actual_complex_skew_cayley_does_not_preserve_real_determinant_claim"]))
material_groups.append(("lipschitz-by-design", "Cayley transform of a skew-symmetric matrix", "Every actual finite real orthogonal matrix Q without a nonzero eigenvector of eigenvalue -1 has exactly one actual skew-symmetric preimage under the Cayley transform. The actual inverse is (I+Q)inv*(I-Q), equal to (I-Q)*(I+Q)inv, and both actual inverse compositions recover the original matrix. Denominator invertibility is proved equivalent to the exact eigenvector exclusion.", [CYIN+"actualInverseCayley",CYIN+"actual_inverse_cayley_right_denominator_identity",CYIN+"actual_inverse_cayley_left_denominator_identity",CYIN+"actual_inverse_cayley_is_source_inverse_formula",CYIN+"actual_inverse_cayley_is_skew_symmetric",CYIN+"actual_inverse_cayley_recovers_orthogonal",CYIN+"actual_inverse_cayley_recovers_skew",CYIN+"actual_cayley_preimage_is_unique",CYIN+"actual_orthogonal_denominator_invertible_iff_no_negative_one_eigenvector",CYIN+"actual_orthogonal_without_negative_one_has_unique_skew_preimage"]))
material_groups.append(("lipschitz-by-design", "For skew-Hermitian $A$", "For every actual finite complex skew-Hermitian matrix A, I+A and I-A are invertible, the actual Cayley matrix is unitary, its actual determinant has norm1, and it has no nonzero eigenvector of eigenvalue -1. Every actual unitary matrix with this exclusion has exactly one actual skew-Hermitian Cayley preimage. The literal inverse formula and both actual compositions are proved, without claiming complex determinant1.", [CLCN+"actualComplexCayley",CLCN+"actual_complex_skew_denominator_gram_is_positive",CLCN+"actual_complex_skew_denominator_is_invertible",CLCN+"actual_complex_skew_numerator_is_adjoint_denominator",CLCN+"actual_complex_skew_numerator_is_invertible",CLCN+"actual_complex_cayley_is_unitary",CLCN+"actual_complex_cayley_determinant_has_unit_norm",CLCN+"actual_complex_cayley_plus_identity_is_twice_inverse",CLCN+"actual_complex_cayley_plus_identity_is_invertible",CLCN+"actual_complex_cayley_has_no_negative_one_eigenvector",CLIN+"actualComplexInverseCayley",CLIN+"actual_inverse_cayley_is_source_inverse_formula",CLIN+"actual_inverse_cayley_is_skew_hermitian",CLIN+"actual_inverse_cayley_recovers_unitary",CLIN+"actual_inverse_cayley_recovers_skew",CLIN+"actual_cayley_preimage_is_unique",CLIN+"actual_unitary_denominator_invertible_iff_no_negative_one_eigenvector",CLIN+"actual_unitary_without_negative_one_has_unique_skew_preimage"]))
for i, (page, needle, statement, names) in enumerate(material_groups):
    units = [u["key"] for u in INV["material_source_units"] if
             u["source"] == f"SafeLearning/{page}.html" and needle.lower() in u["source_text"].lower()]
    assert units, (page,needle)
    material.append(claim(f"modules::proved-material-{i+1}", statement, names, "proved",
                          hypotheses=["The exact mathematical model and explicit declaration hypotheses."],
                          correspondence="Only the explicitly stated result is discharged; overlapping source units may contain other pending claims.", units=units))

proof_files = {}
declarations = []
referenced_names = {name for e in exercises for c in e["claims"] for name in c["lean_declarations"]}
referenced_names.update(name for c in material for name in c["lean_declarations"])
compiled = {}
for compile_manifest_path in sorted((ROOT/"book/coverage/checks").glob("modules*standalone.json")):
    for r in json.loads(compile_manifest_path.read_text())["files"]:
        compiled[r["file"]] = r
for p in sorted((ROOT/"verification/lean/SafeLearning").glob("CompleteModules*.lean")):
    rel = str(p.relative_to(ROOT))
    sha = digest(rel)
    record = compiled.get(rel)
    # A working source is not part of this reviewable ledger until the actual
    # standalone compiler record matches exactly and reports success.
    if not record or record['sha256'] != sha or record['exit_code'] != 0:
        continue
    text = p.read_text()
    ns = re.search(r"^namespace\s+(\S+)",text,re.M).group(1)
    # Successful but unmapped future work stays outside this ledger's audit
    # selection until an exact source component actually references it.
    if not any(name.startswith(ns+".") for name in referenced_names):
        continue
    proof_files[rel] = {"sha256":sha,
                       "standalone_compile_status":"passed" if record and record['sha256']==sha and record['exit_code']==0 else "not_yet_recorded_for_current_source",
                       "standalone_compile_evidence":record if record and record['sha256']==sha else None}
    for match in re.finditer(r"^theorem\s+(\w+)",text,re.M):
        end = text.find(":=",match.start())
        declarations.append({"name":ns+"."+match.group(1),"file":rel,
                             "line":text.count("\n",0,match.start())+1,
                             "statement":text[match.start():end].strip()})
    proof_files[rel]["declarations"] = [d["name"] for d in declarations if d["file"]==rel]

out = {"schema_version":1,"generated_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
       "scope_pages":sorted(SOURCES),"source_sha256":{p:digest(p) for p in sorted(SOURCES)},
       "chapter_fragment_sha256":{f"book/chapters/{p}.html":digest(f"book/chapters/{p}.html") for p in PAGES},
       "proof_files":proof_files,"status":"active_partial_new_formal_components_and_explicit_complete_gap_queue",
       "exercises":exercises,"material_claims":material,"declarations":declarations,
       "counts":{"exercises":len(exercises),"exercise_status":dict(collections.Counter(e['status'] for e in exercises)),
                 "exercise_claim_status":dict(collections.Counter(c['status'] for e in exercises for c in e['claims'])),
                 "material_claim_status":dict(collections.Counter(c['status'] for c in material)),
                 "new_declarations":len(declarations)},
       "remaining_research_theorem_families":[
           "Actual scalar-PSD RKHS construction/uniqueness, bounded evaluation, arbitrary-loss representer structure, ridge existence, scalar posterior asymptotic expansions, norm-convergent minimum-norm interpolation and sharp power-function errors are proved components. Remaining GP families include Gaussian conditioning/rank-one update, information gain and concentration theorems, exact source gradient formulas and spectral-norm remainder constants.",
           "SafeOpt finite-time discovery/acquisition and kernel jump examples; GoSafe ODE existence/uniqueness to flow law, returnability and discovery. Lipschitz no-crossing and abstract flow suffix are proved components.",
           "General infinite-horizon viability characterization, double-integrator continuous-time optimal braking and full penalized-policy optimality. The finite thermal graph and stopped-return upper bound are proved components.",
           "General finite lifted LipSDP soundness, actual arbitrary-dimensional one-hidden-layer block LMI, spectral product gain, its exact feasible SDP point, genuine affine-parameter SDP convexity/local-global optimality, arbitrary-size logdet and actual block-weight derivatives, exact determinant Taylor remainder, inverse spectral boundary blow-up, Cholesky/Sylvester equivalences and validated norm-error margins are proved components. Remaining families include full recursive multi-layer selectors, exact optimized walkthrough value, further network exact Lipschitz constants, varying-mu training-path assumptions, and convolution realization.",
           "Cayley general invertibility/orthogonality, SLL/AOL/Sandwich completeness, matrix convolution Gramian/weighted gain limits and REN contraction.",
           "Numeric local tanh slope enclosures, complete local-sector LFT/LMI correspondence, printed delayed-system roots and general IQC results. Actual tanh local sectors and exact delayed-loop Lyapunov decay are proved components.",
           "Full multi-layer CROWN correspondence, continuous-score conformal upper coverage and random-trajectory thermal event specialization, randomized-smoothing Neyman–Pearson theorem, Hoeffding and convex scenario probability theorem. General affine IBP and shared exchangeable-rank lower coverage are proved components."
       ],
       "limits":["All217owned exercises are inventoried. Pending requirements are intentional and must not be reported as completed.",
                 "The mathematical source-unit queue overlaps and requires semantic review; one proved statement does not cover every assertion in its source unit.",
                 "Old Modules.lean selected proofs remain valid evidence; old coarse exercise associations do not close new granular requirements.",
                 "Standalone compilation is preliminary; root must run fresh aggregate build, kernel replay and transitive-axiom audit."]}
(ROOT/"book/coverage/modules.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print(json.dumps(out["counts"],indent=2))
