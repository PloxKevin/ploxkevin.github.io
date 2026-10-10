import SafeLearning.CompleteModulesGPLinearInformationBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter Asymptotics Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationGrowth
open SafeLearning.CompleteModulesGPLinearInformationBounds

theorem actual_positive_scale_shifted_log_is_bigO_log_at_real_atTop
    (c : ℝ) (hc : 0 < c) :
    (fun t : ℝ => Real.log (1+t/c)) =O[atTop] Real.log := by
  have hcmp : (fun t : ℝ => Real.log (1+t/c)) =O[atTop]
      (fun t : ℝ => Real.log ((1+c⁻¹)*t)) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have hnonneg : 0 ≤ Real.log (1+t/c) :=
      Real.log_nonneg (by positivity)
    have har : 1+t/c ≤ (1+c⁻¹)*t := by
      rw [div_eq_mul_inv]
      nlinarith
    have hle := Real.log_le_log (show 0 < 1+t/c by positivity) har
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hnonneg,
      abs_of_nonneg (hnonneg.trans hle)]
    exact hle
  exact hcmp.trans (Real.isBigO_log_const_mul_log_atTop (1+c⁻¹))

theorem actual_dimension_trace_bound_is_bigO_dimension_log_at_real_atTop
    (d lambda : ℝ) (hd : 0 < d) (hlambda : 0 < lambda) :
    (fun t : ℝ => d/2*Real.log (1+t/(lambda*d))) =O[atTop]
      (fun t : ℝ => d*Real.log t) := by
  exact ((actual_positive_scale_shifted_log_is_bigO_log_at_real_atTop
      (lambda*d) (mul_pos hlambda hd)).const_mul_left (d/2)).const_mul_right hd.ne'

theorem actual_dimension_trace_bound_is_bigO_dimension_log_at_nat_atTop
    (d lambda : ℝ) (hd : 0 < d) (hlambda : 0 < lambda) :
    (fun t : ℕ => d/2*Real.log (1+(t:ℝ)/(lambda*d))) =O[atTop]
      (fun t : ℕ => d*Real.log (t:ℝ)) :=
  (actual_dimension_trace_bound_is_bigO_dimension_log_at_real_atTop
    d lambda hd hlambda).comp_tendsto tendsto_natCast_atTop_atTop

theorem actual_positive_semidefinite_information_is_nonnegative
    {D : Type*} [Fintype D] [DecidableEq D]
    (G : Matrix D D ℝ) (hG : G.PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    0 ≤ information G lambda := by
  unfold information
  rw [actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
    G hG lambda hlambda]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ => Real.log_nonneg
    (by have hp := hG.eigenvalues_nonneg i; positivity))

theorem actual_every_unit_ball_design_sequence_has_information_bigO_dimension_log_samples
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (X : (t : ℕ) → Matrix (Fin t) D ℝ)
    (hX : ∀ t j, ‖(WithLp.toLp 2 (fun i => X t j i) : EuclideanSpace ℝ D)‖ ≤ 1)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (fun t : ℕ => information ((X t)ᵀ*X t) lambda) =O[atTop]
      (fun t : ℕ => (Fintype.card D:ℝ)*Real.log (t:ℝ)) := by
  have hd : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hcmp : (fun t : ℕ => information ((X t)ᵀ*X t) lambda) =O[atTop]
      (fun t : ℕ => (Fintype.card D:ℝ)/2*
        Real.log (1+(t:ℝ)/(lambda*(Fintype.card D:ℝ)))) := by
    apply IsBigO.of_bound'
    apply Filter.Eventually.of_forall
    intro t
    have hn := actual_positive_semidefinite_information_is_nonnegative
      ((X t)ᵀ*X t) (actual_design_gram_is_positive_semidefinite (X t)) lambda hlambda
    have hb := actual_linear_design_information_has_the_dimension_trace_bound
      (X t) lambda hlambda (hX t)
    simp only [Fintype.card_fin] at hb
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hn,
      abs_of_nonneg (hn.trans hb)]
    exact hb
  exact hcmp.trans (actual_dimension_trace_bound_is_bigO_dimension_log_at_nat_atTop
    (Fintype.card D:ℝ) lambda hd hlambda)

end SafeLearning.CompleteModulesGPLinearInformationGrowth
