import SafeLearning.CompleteFoundationsTelescopingModels
import SafeLearning.CompleteFoundationsLessonSeries
import SafeLearning.CompleteFoundationsTemporalLogDet

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace SafeLearning.CompleteFoundationsTelescopingApplications
open CompleteFoundationsTelescopingModels CompleteFoundationsLessonSeries
open CompleteFoundationsTemporalLogDet

theorem actual_arbitrary_supply_inequality_sums_with_terminal_storage
    (value supply : ℕ → ℝ) (hstep : ∀ t, value (t+1)-value t ≤ supply t) (T : ℕ) :
    value T-value 0≤∑ t∈Finset.range T,supply t := by
  rw [← actual_arbitrary_additive_group_sequence_telescopes value T]
  exact Finset.sum_le_sum (fun t _ => hstep t)

theorem actual_nonnegative_terminal_storage_bounds_total_extracted_supply
    (value supply : ℕ → ℝ) (hvalue : ∀ t,0≤value t)
    (hstep : ∀ t,value (t+1)-value t ≤ supply t) (T : ℕ) :
    -value 0≤∑ t∈Finset.range T,supply t := by
  linarith [actual_arbitrary_supply_inequality_sums_with_terminal_storage value supply hstep T,
    hvalue T]

theorem actual_input_output_energy_inequality_keeps_initial_storage
    (value inputEnergy outputEnergy : ℕ → ℝ)
    (hvalue : ∀ t,0≤value t)
    (hstep : ∀ t,value (t+1)-value t ≤ inputEnergy t-outputEnergy t) (T : ℕ) :
    (∑ t∈Finset.range T,outputEnergy t)≤
      (∑ t∈Finset.range T,inputEnergy t)+value 0 := by
  have h := actual_nonnegative_terminal_storage_bounds_total_extracted_supply
    value (fun t => inputEnergy t-outputEnergy t) hvalue hstep T
  rw [Finset.sum_sub_distrib] at h
  linarith

theorem actual_zero_initial_storage_gives_every_finite_horizon_energy_bound
    (value inputEnergy outputEnergy : ℕ → ℝ)
    (hvalue : ∀ t,0≤value t) (hzero : value 0=0)
    (hstep : ∀ t,value (t+1)-value t ≤ inputEnergy t-outputEnergy t) (T : ℕ) :
    (∑ t∈Finset.range T,outputEnergy t)≤∑ t∈Finset.range T,inputEnergy t := by
  simpa [hzero] using actual_input_output_energy_inequality_keeps_initial_storage
    value inputEnergy outputEnergy hvalue hstep T

theorem actual_discounted_value_terms_cancel_at_every_horizon
    (gamma : ℝ) (reward value : ℕ → ℝ) (T : ℕ) :
    (∑ t∈Finset.range T,gamma^t*(reward t+gamma*value (t+1)-value t))=
      (∑ t∈Finset.range T,gamma^t*reward t)+gamma^T*value T-value 0 := by
  have he (t : ℕ) : gamma^t*(reward t+gamma*value (t+1)-value t)=
      gamma^t*reward t+(gamma^(t+1)*value (t+1)-gamma^t*value t) := by
    rw [pow_succ]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,
    actual_arbitrary_additive_group_sequence_telescopes (fun t => gamma^t*value t) T]
  simp
  ring

theorem actual_bounded_discounted_terminal_value_tends_to_zero
    (gamma B : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1)
    (value : ℕ → ℝ) (hb : ∀ t,|value t|≤B) :
    Tendsto (fun T => gamma^T*value T) atTop (𝓝 0) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hg0 hg1).mul_const B
  have hab : Tendsto (fun T => |gamma^T*value T|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun T => ?_)
    · simpa using hpow
    · rw [abs_mul,abs_of_nonneg (pow_nonneg hg0 T)]
      exact mul_le_mul_of_nonneg_left (hb T) (pow_nonneg hg0 T)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hab)

theorem actual_discounted_td_partial_sums_have_the_true_infinite_limit
    (gamma R B : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1)
    (reward value : ℕ → ℝ) (hr : ∀ t,|reward t|≤R) (hb : ∀ t,|value t|≤B) :
    Tendsto (fun T => ∑ t∈Finset.range T,
      gamma^t*(reward t+gamma*value (t+1)-value t)) atTop
      (𝓝 ((∑' t : ℕ,gamma^t*reward t)-value 0)) := by
  have hs := (actual_bounded_discounted_return_and_tail gamma R reward hg0 hg1 hr 0).1.hasSum
  have ht := actual_bounded_discounted_terminal_value_tends_to_zero gamma B hg0 hg1 value hb
  have h := (hs.tendsto_sum_nat.add ht).sub_const (value 0)
  simpa only [actual_discounted_value_terms_cancel_at_every_horizon,add_zero] using h

theorem actual_inclusive_finite_discount_sum_has_the_printed_formula
    (gamma : ℝ) (hgamma : gamma≠1) (T : ℕ) :
    (∑ t∈Finset.range (T+1),gamma^t)=(1-gamma^(T+1))/(1-gamma) := by
  exact CompleteFoundationsDiscountHorizons.actual_finite_geometric_induction gamma hgamma (T+1)

section MatrixLog
variable {feature : Type*} [Fintype feature] [DecidableEq feature]

theorem actual_temporal_determinants_and_update_factors_are_positive
    (lambda : ℝ) (hl : 0<lambda) (phi : ℕ → feature → ℝ) (t : ℕ) :
    0<(temporalCovariance lambda phi t).det ∧ 0<1+temporalVariance lambda phi t/lambda := by
  have hd := (actual_temporal_covariance_positive_and_nonsingular lambda hl phi t).1.det_pos
  have hdnext := (actual_temporal_covariance_positive_and_nonsingular lambda hl phi (t+1)).1.det_pos
  constructor
  · exact hd
  · rw [actual_temporal_determinant_step lambda hl phi t] at hdnext
    exact (mul_pos_iff_of_pos_left hd).mp hdnext

theorem actual_log_determinant_is_the_sum_of_true_sequential_log_factors
    (lambda : ℝ) (hl : 0<lambda) (phi : ℕ → feature → ℝ) (T : ℕ) :
    Real.log ((temporalCovariance lambda phi T).det/lambda^(Fintype.card feature))=
      ∑ t∈Finset.range T,Real.log (1+temporalVariance lambda phi t/lambda) := by
  rw [actual_all_horizons_determinant_product lambda hl phi T]
  exact Real.log_prod (fun t _ =>
    (actual_temporal_determinants_and_update_factors_are_positive lambda hl phi t).2.ne')

theorem actual_kernel_log_determinant_is_the_sum_of_sequential_log_factors
    (lambda : ℝ) (hl : 0<lambda) (phi : ℕ → feature → ℝ) (T : ℕ) :
    Real.log ((1+lambda⁻¹ • CompleteFoundationsSequentialLogDet.kernelGram
      (temporalFeatures phi T)).det)=
      ∑ t∈Finset.range T,Real.log (1+temporalVariance lambda phi t/lambda) := by
  rw [actual_all_horizons_kernel_determinant_product lambda hl phi T]
  exact Real.log_prod (fun t _ =>
    (actual_temporal_determinants_and_update_factors_are_positive lambda hl phi t).2.ne')
end MatrixLog
end SafeLearning.CompleteFoundationsTelescopingApplications
