import SafeLearning.CompleteAppliedOneStateOccupancy

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedOneStateConsequences
open MeasureTheory ProbabilityTheory Set
open SafeLearning.CompleteAppliedOneStateOccupancy

def actualState (_time : ℕ) (_path : ℕ → Bool) : Unit := ()

theorem actual_one_state_dynamics_is_the_self_loop (time : ℕ) (path : ℕ → Bool) :
    actualState (time+1) path=actualState time path := rfl

theorem actual_normalized_state_occupancy_is_one (parameter : unitInterval) :
    (1-(4/5:ℝ))*(∑' time : ℕ,(4/5:ℝ)^time*
      (actualActionPathLaw parameter).real {path | actualState time path=()})=1 ∧
    actualNormalizedOccupancy parameter true+actualNormalizedOccupancy parameter false=1 := by
  constructor
  · simp only [actualState,Set.ofPred_true,probReal_univ,mul_one]
    rw [(hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 4/5)
      (by norm_num : (4/5:ℝ)<1)).tsum_eq]
    norm_num
  · rw [(actual_normalized_occupancies_equal_the_stationary_probabilities parameter).1,
      (actual_normalized_occupancies_equal_the_stationary_probabilities parameter).2]
    ring

theorem actual_every_path_discounted_return_has_an_absolute_bound
    (amount : ℝ) (path : ℕ → Bool) :
    |actualDiscountedReturn amount path| ≤ 5*|amount| := by
  have hg : Summable (fun time : ℕ => (4/5:ℝ)^time*|amount|) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hb (time : ℕ) : ‖(4/5:ℝ)^time*actualPathQuantity amount time path‖ ≤
      (4/5:ℝ)^time*|amount| := by
    rw [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<4/5)]
    exact mul_le_mul_of_nonneg_left (actual_path_quantity_is_bounded amount time path)
      (pow_nonneg (by norm_num) _)
  have hs : Summable (fun time : ℕ => ‖(4/5:ℝ)^time*actualPathQuantity amount time path‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg
  have h := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hg)
  have he := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 4/5)
    (by norm_num : (4/5:ℝ)<1)).mul_right |amount|).tsum_eq
  rw [he] at h
  have hr : (1-(4/5:ℝ))⁻¹*|amount|=5*|amount| := by ring
  simpa only [actualDiscountedReturn,Real.norm_eq_abs,hr] using h

theorem actual_pathwise_discounted_return_is_integrable
    (parameter : unitInterval) (amount : ℝ) :
    Integrable (actualDiscountedReturn amount) (actualActionPathLaw parameter) := by
  have hm : Measurable (actualDiscountedReturn amount) := by
    apply Measurable.tsum
    intro time
    have hq : Measurable (actualActionQuantity amount) := measurable_of_countable _
    exact measurable_const.mul (hq.comp (measurable_pi_apply time))
  apply Integrable.of_bound hm.aestronglyMeasurable (5*|amount|)
  exact Filter.Eventually.of_forall (fun path => by
    simpa only [Real.norm_eq_abs] using
      actual_every_path_discounted_return_has_an_absolute_bound amount path)

theorem actual_occupancy_weighted_quantity_is_the_true_expected_return
    (parameter : unitInterval) (amount : ℝ) :
    (∫ path,actualDiscountedReturn amount path ∂actualActionPathLaw parameter)=
      (actualNormalizedOccupancy parameter true*actualActionQuantity amount true+
        actualNormalizedOccupancy parameter false*actualActionQuantity amount false)/(1-(4/5:ℝ)) := by
  rw [actual_true_infinite_expected_discounted_return,
    (actual_normalized_occupancies_equal_the_stationary_probabilities parameter).1,
    (actual_normalized_occupancies_equal_the_stationary_probabilities parameter).2]
  simp [actualActionQuantity]
  ring

end SafeLearning.CompleteAppliedOneStateConsequences
