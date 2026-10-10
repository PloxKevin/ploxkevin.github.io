import Mathlib
import SafeLearning.CompleteCoreBook
import SafeLearning.CompleteAppliedReturns

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace SafeLearning.CompleteCoreReturns

local instance : MeasurableSpace (Fin 2) := ⊤

theorem one_step_mode_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (action : Ω → Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hlaw : HasLaw action (CompleteCoreBook.modeLaw p hp).toMeasure μ)
    (slow fast : ℝ) :
    (∫ omega, (![slow,fast] : Fin 2 → ℝ) (action omega) ∂μ)=
      CompleteCoreBook.expectedMode p hp slow fast := by
  have hm : Measurable (![slow,fast] : Fin 2 → ℝ) := measurable_from_top
  rw [show (fun omega => (![slow,fast] : Fin 2 → ℝ) (action omega))=
    (![slow,fast] : Fin 2 → ℝ) ∘ action from rfl]
  rw [hlaw.integral_comp hm.aestronglyMeasurable,PMF.integral_eq_sum]
  rfl

theorem pathwise_mode_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (action : ℕ → Ω → Fin 2)
    (p : ℝ≥0) (hp : p ≤ 1)
    (hlaw : ∀ n, HasLaw (action n) (CompleteCoreBook.modeLaw p hp).toMeasure μ)
    (gamma slow fast : ℝ) (hg : |gamma| < 1) :
    (∫ omega, ∑' n : ℕ, gamma^n*(![slow,fast] : Fin 2 → ℝ) (action n omega) ∂μ)=
      CompleteCoreBook.modeReturn p hp gamma slow fast := by
  have hm : Measurable (![slow,fast] : Fin 2 → ℝ) := measurable_from_top
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun omega => (![slow,fast] : Fin 2 → ℝ) (action n omega)) μ := by
    intro n
    exact (hm.comp_aemeasurable (hlaw n).aemeasurable).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ omega ∂μ,
      |(![slow,fast] : Fin 2 → ℝ) (action n omega)| ≤ |slow|+|fast| := by
    intro n
    exact ae_of_all μ (fun omega => by
      generalize action n omega=i
      fin_cases i <;> simp <;> positivity)
  rw [CompleteAppliedReturns.discounted_expectation_interchange μ _ gamma (|slow|+|fast|) hg hmeas hbound]
  unfold CompleteCoreBook.modeReturn
  apply tsum_congr
  intro n
  rw [one_step_mode_expectation μ (action n) p hp (hlaw n)]

theorem optimal_reward_budget_derivative (budget : ℝ) :
    HasDerivAt (fun d : ℝ => (50/3)*d+50/3) (50/3) budget := by
  convert ((hasDerivAt_id budget).const_mul (50/3)).add_const (50/3) using 1 <;>
    simp [id_eq]

theorem discounted_constant_budget_meaning (cost budget gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    cost/(1-gamma) ≤ budget ↔ cost ≤ (1-gamma)*budget := by
  rw [div_le_iff₀ (by linarith : 0 < 1-gamma)]
  rw [mul_comm]

theorem normalized_mode_occupancy (p : ℝ≥0) (hp : p ≤ 1) (i : Fin 2)
    (gamma : ℝ) (hg : |gamma| < 1) :
    (1-gamma)*(∑' n : ℕ, gamma^n*(CompleteCoreBook.modeLaw p hp i).toReal)=
      (CompleteCoreBook.modeLaw p hp i).toReal := by
  rw [CoreModules.discounted_constant _ _ hg]
  have hn : 1-gamma ≠ 0 := by have hh := (abs_lt.mp hg).2; linarith
  field_simp

theorem mixed_half_discount_returns (p : ℝ≥0) (hp : p ≤ 1) :
    CompleteCoreBook.modeReturn p hp (1/2) 1 3=2+4*(p : ℝ) ∧
    CompleteCoreBook.modeReturn p hp (1/2) 0 2=4*(p : ℝ) ∧
    CompleteCoreBook.modeReturn p hp (1/2) 1 4=2+6*(p : ℝ) := by
  simp_rw [CompleteCoreBook.mode_discounted_return p hp _ _ _ (by norm_num : |(1/2 : ℝ)|<1)]
  constructor
  · ring
  constructor <;> ring

theorem mixed_occupancies_example :
    (CompleteCoreBook.modeLaw (3/10) (by rw [← NNReal.coe_le_coe];norm_num) 0).toReal=7/10 ∧
    (CompleteCoreBook.modeLaw (3/10) (by rw [← NNReal.coe_le_coe];norm_num) 1).toReal=3/10 ∧
    CompleteCoreBook.modeReturn (3/10) (by rw [← NNReal.coe_le_coe];norm_num) (1/2) 1 3=16/5 ∧
    CompleteCoreBook.modeReturn (3/10) (by rw [← NNReal.coe_le_coe];norm_num) (1/2) 0 2=6/5 := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [CompleteCoreBook.modeLaw]
    rw [ENNReal.toReal_sub_of_le (by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      norm_num) (by norm_num)]
    norm_num
  · norm_num [CompleteCoreBook.modeLaw]
  · rw [CompleteCoreBook.mode_discounted_return _ _ _ _ _ (by norm_num)]
    norm_num
  · rw [CompleteCoreBook.mode_discounted_return _ _ _ _ _ (by norm_num)]
    norm_num

theorem constant_cost_discount_doubling (cost : ℝ) :
    cost/(1-(19/20 : ℝ))=2*(cost/(1-(9/10 : ℝ))) ∧
      (cost/(1-(9/10 : ℝ)) ≤ 1 ↔ cost ≤ 1/10) ∧
        (cost/(1-(19/20 : ℝ)) ≤ 1 ↔ cost ≤ 1/20) := by
  norm_num [div_eq_mul_inv]
  constructor
  · ring
  constructor <;> constructor <;> intro h <;> linarith

end SafeLearning.CompleteCoreReturns
