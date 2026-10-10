import SafeLearning.CompleteModulesLoSBOPracticeModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesLoSBOPracticeConsequences
open SafeLearning.CompleteModulesLoSBOPracticeModels

theorem actual_every_observed_nonzero_secant_is_a_necessary_lower_bound_on_the_global_constant
    (f : ℝ → ℝ) (constant x y : ℝ) (hxy : x≠y)
    (hglobal : ∀ a b, |f a-f b| ≤ constant*|a-b|) :
    |f x-f y| / |x-y| ≤ constant := by
  have hd : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  apply (div_le_iff₀ hd).mpr
  exact hglobal x y

theorem actual_larger_valid_lipschitz_constant_remains_a_valid_upper_bound
    (f : ℝ → ℝ) (first second : ℝ) (hc : first ≤ second)
    (hf : ∀ x y, |f x-f y| ≤ first*|x-y|) :
    ∀ x y, |f x-f y| ≤ second*|x-y| := by
  intro x y
  exact (hf x y).trans (mul_le_mul_of_nonneg_right hc (abs_nonneg (x-y)))

theorem actual_triangular_bump_has_the_literal_derivative_height_on_the_open_left_half
    (height x : ℝ) (hx : x<(1/2:ℝ)) :
    HasDerivAt (actualBump height) height x := by
  have he : actualBump height =ᶠ[𝓝 x] (fun y:ℝ => height*y) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp only [actualBump,min_eq_left (by linarith : y≤1-y)]
  have hd : HasDerivAt (fun y:ℝ => height*y) height x := by
    simpa using (hasDerivAt_id x).const_mul height
  exact hd.congr_of_eventuallyEq he

theorem actual_triangular_bump_has_the_literal_derivative_negative_height_on_the_open_right_half
    (height x : ℝ) (hx : (1/2:ℝ)<x) :
    HasDerivAt (actualBump height) (-height) x := by
  have he : actualBump height =ᶠ[𝓝 x] (fun y:ℝ => height*(1-y)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [actualBump,min_eq_right (by linarith : 1-y≤y)]
  have hd : HasDerivAt (fun y:ℝ => height*(1-y)) (-height) x := by
    simpa using ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).const_mul height
  exact hd.congr_of_eventuallyEq he

end SafeLearning.CompleteModulesLoSBOPracticeConsequences
