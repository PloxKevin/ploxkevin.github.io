import SafeLearning.CompleteAppliedSmallGainGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SafeLearning.CompleteAppliedSmallGainSource
open CompleteAppliedSmallGainGlobal CompleteAppliedSmallGainStorage

theorem actual_source_storage_derivative_follows_from_the_actual_trajectory_ode
    (phi x : ℝ → ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0 = 0) (time : ℝ)
    (hd : HasDerivAt x (sourceField phi (x time)) time) :
    HasDerivAt (fun t => (x t)^2)
      (-2*(x time)^2+(8/5)*(x time)*phi (x time)) time ∧
      -2*(x time)^2+(8/5)*(x time)*phi (x time) ≤ -(2/5)*(x time)^2 := by
  have hpoly := actual_source_positive_feedback_storage_derivative_is_derived phi hl hz (x time)
  constructor
  · convert hd.pow 2 using 1 <;> dsimp [sourceField] <;> ring
  · rw [←hpoly.1]
    exact hpoly.2

theorem actual_linear_source_denominator_has_exactly_its_stable_pole :
    (∀ s : ℂ, s+1=0 ↔ s=-1) ∧ ((-1:ℂ).re<0) := by
  constructor
  · intro s
    constructor <;> intro h <;> linear_combination h
  · norm_num

theorem actual_linear_homogeneous_trajectory_is_derived_and_tends_to_zero (initial : ℝ) :
    (∀ time : ℝ, HasDerivAt (fun t => initial*Real.exp (-t))
      (-(initial*Real.exp (-time))) time) ∧
      Tendsto (fun t : ℝ => initial*Real.exp (-t)) atTop (𝓝 0) := by
  constructor
  · intro time
    convert (((hasDerivAt_id time).neg).exp).const_mul initial using 1 <;> simp [Pi.neg_apply]
  · have ht : Tendsto (fun t : ℝ => -t) atTop atBot := tendsto_neg_atTop_atBot
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)

end SafeLearning.CompleteAppliedSmallGainSource
