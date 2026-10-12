import Mathlib
import SafeLearning.CompleteFoundationsMatrixSensitivity
import SafeLearning.CompleteFoundationsAsymptoticDefinitionsWhole30

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Asymptotics Matrix
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31

theorem actual_printed_quadratic_bounds (n : ℕ) (hn : 10 ≤ n) :
    10 * (n : ℝ) ≤ (n : ℝ)^2 ∧ 5 ≤ (n : ℝ)^2 ∧
      3 * (n : ℝ)^2 ≤ 3*(n : ℝ)^2+10*n+5 ∧
      3*(n : ℝ)^2+10*n+5 ≤ 5*(n : ℝ)^2 := by
  have h : (10 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) (sub_nonneg.mpr h)]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ)-10)]
  constructor <;> nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) (sub_nonneg.mpr h)]

theorem actual_printed_quadratic_has_source_theta_growth :
    SafeLearning.CompleteFoundationsAsymptoticDefinitionsWhole30.sourceTheta
      (fun n : ℕ => 3*(n : ℝ)^2+10*n+5) (fun n => (n : ℝ)^2) := by
  constructor
  · refine ⟨5,by norm_num,10,?_⟩
    intro n hn
    exact (actual_printed_quadratic_bounds n hn).2.2.2
  · refine ⟨3,by norm_num,10,?_⟩
    intro n hn
    exact (actual_printed_quadratic_bounds n hn).2.2.1

theorem actual_logarithm_is_little_o_of_every_positive_real_power
    (a : ℝ) (ha : 0 < a) :
    Real.log =o[atTop] (fun n : ℝ => Real.rpow n a) :=
  isLittleO_log_rpow_atTop ha

theorem actual_every_real_power_is_little_o_of_positive_exponential_growth
    (a k : ℝ) (ha : 0 < a) :
    (fun n : ℝ => Real.rpow n k) =o[atTop] (fun n => Real.exp (a*n)) :=
  isLittleO_rpow_exp_pos_mul_atTop k ha

/-- Genuine analytic Taylor control yields an order-two remainder; differentiability
alone is not used as a substitute for that stronger bound. -/
theorem actual_analytic_scalar_first_order_remainder_is_bigO_square
    (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    (fun t : ℝ => f t-f 0-deriv f 0*t) =O[𝓝 0] (fun t => t^2) := by
  obtain ⟨p,hp⟩ := hf
  have hz : p.coeff 0 = f 0 := hp.coeff_zero 1
  have hs : Fin.snoc (0 : Fin 0 → ℝ) (1 : ℝ) = (1 : Fin 1 → ℝ) := by
    ext i
    fin_cases i
    rfl
  have hd : p.coeff 1 = deriv f 0 := by
    have hh := hp.hasFDerivAt.hasDerivAt
    simp only [continuousMultilinearCurryFin1_apply,hs] at hh
    exact hh.deriv.symm
  have hb := hp.isBigO_sub_partialSum_pow 2
  have he : (fun t : ℝ => f (0+t)-p.partialSum 2 t) =
      (fun t => f t-f 0-deriv f 0*t) := by
    funext t
    simp only [zero_add,FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      pow_zero,pow_one,smul_eq_mul,one_mul,hz,hd]
    ring
  have hg : (fun t : ℝ => ‖t‖^2) = (fun t : ℝ => t^2) := by
    funext t
    simp [Real.norm_eq_abs,sq_abs]
  rw [he,hg] at hb
  exact hb

section MatrixPath
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_affine_matrix_determinant_path_is_analytic
    (N E : Matrix ι ι ℝ) :
    AnalyticAt ℝ (fun t : ℝ => (N+t • E).det) 0 := by
  let p : Polynomial ℝ := (N.map Polynomial.C+(Polynomial.X : Polynomial ℝ) • E.map Polynomial.C).det
  have he : (fun t : ℝ => p.eval t) = (fun t : ℝ => (N+t • E).det) := by
    funext t
    dsimp [p]
    rw [Polynomial.eval,← Polynomial.coe_eval₂RingHom,RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply]
    ring
  have h : AnalyticAt ℝ (fun t : ℝ => p.eval t) 0 :=
    AnalyticOnNhd.eval_polynomial p 0 (by trivial)
  simpa only [he] using h

/-- The printed logarithmic determinant expansion is derived from an actual
analytic affine determinant path and the genuine inverse-trace derivative. -/
theorem actual_generic_logdet_linear_expansion_with_bigO_square_remainder
    (N E : Matrix ι ι ℝ) (hdet : 0 < N.det) :
    (fun t : ℝ => Real.log (N+t • E).det-Real.log N.det-t*(N⁻¹*E).trace)
      =O[𝓝 0] (fun t => t^2) := by
  have ha : AnalyticAt ℝ (fun t : ℝ => Real.log (N+t • E).det) 0 :=
    (actual_affine_matrix_determinant_path_is_analytic N E).log (by simpa using hdet)
  have hu : IsUnit N := N.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet.ne')
  have hd := SafeLearning.CompleteFoundationsMatrixSensitivity.actual_generic_log_determinant_direction N E hu
  have h := actual_analytic_scalar_first_order_remainder_is_bigO_square
    (fun t : ℝ => Real.log (N+t • E).det) ha
  simpa only [hd.deriv,zero_smul,add_zero,mul_comm] using h

end MatrixPath
end SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31


namespace SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31

/-- The actual Module12 positive-definite domain supplies the determinant condition
of the derived Taylor expansion; no remainder bound is assumed. -/
theorem actual_logdet_expansion_on_the_printed_positive_definite_domain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N E : Matrix ι ι ℝ) (hN : N.PosDef) :
    (fun t : ℝ => Real.log (N+t • E).det-Real.log N.det-t*(N⁻¹*E).trace)
      =O[𝓝 0] (fun t => t^2) :=
  actual_generic_logdet_linear_expansion_with_bigO_square_remainder N E hN.det_pos

/-- The affine path really keeps a positive determinant in a neighborhood of zero. -/
theorem actual_affine_positive_determinant_path_has_a_positive_neighborhood
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N E : Matrix ι ι ℝ) (hdet : 0 < N.det) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 < (N+t • E).det := by
  have hh : (0 : ℝ) < (N+(0 : ℝ) • E).det := by simpa using hdet
  exact (actual_affine_matrix_determinant_path_is_analytic N E).continuousAt.eventually
    (eventually_gt_nhds hh)

/-- For a positive step approaching zero, the hidden-constant convention is exactly
an eventual C*eta absolute error bound with C independent of the step. -/
theorem actual_small_positive_step_bigO_is_an_eventual_constant_times_step_bound
    (error : ℝ → ℝ) :
    error =O[𝓝[>] 0] (fun eta : ℝ => eta) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ eta : ℝ in 𝓝[>] 0, |error eta| ≤ C*eta := by
  rw [isBigO_iff']
  apply exists_congr
  intro C
  apply and_congr_right
  intro hC
  apply Filter.eventually_congr
  filter_upwards [self_mem_nhdsWithin] with eta heta
  have hp : 0 < eta := heta
  simp only [Real.norm_eq_abs,abs_of_pos hp]

end SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31

#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_printed_quadratic_bounds
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_printed_quadratic_has_source_theta_growth
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_logarithm_is_little_o_of_every_positive_real_power
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_every_real_power_is_little_o_of_positive_exponential_growth
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_analytic_scalar_first_order_remainder_is_bigO_square
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_affine_matrix_determinant_path_is_analytic
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_generic_logdet_linear_expansion_with_bigO_square_remainder
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_logdet_expansion_on_the_printed_positive_definite_domain
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_affine_positive_determinant_path_has_a_positive_neighborhood
#print axioms SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.actual_small_positive_step_bigO_is_an_eventual_constant_times_step_bound
