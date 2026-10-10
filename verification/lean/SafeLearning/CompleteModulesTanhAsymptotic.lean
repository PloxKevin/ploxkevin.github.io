import SafeLearning.CompleteModulesTanhChords

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesTanhAsymptotic
open CompleteModulesTheory CompleteModulesTanhChords

theorem actual_cosh_tends_to_infinity_at_positive_infinity :
    Tendsto Real.cosh atTop atTop := by
  apply tendsto_atTop_mono (fun x => ?_)
    (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0:ℝ)<2))
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

theorem actual_tanh_derivative_tends_to_zero_at_positive_infinity :
    Tendsto (fun x : ℝ => deriv Real.tanh x) atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero.comp actual_cosh_tends_to_infinity_at_positive_infinity
  have hs := hi.pow 2
  convert hs using 1
  · funext x
    simp only [Function.comp_apply,(tanh_derivative x).deriv,one_div,inv_pow]
  · norm_num

theorem actual_tanh_derivative_tends_to_zero_as_absolute_input_tends_to_infinity :
    Tendsto (fun x : ℝ => deriv Real.tanh x)
      (comap (abs : ℝ → ℝ) atTop) (nhds 0) := by
  have h := actual_tanh_derivative_tends_to_zero_at_positive_infinity.comp
    (tendsto_comap : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop)
  convert h using 1
  funext x
  simp only [Function.comp_apply,(tanh_derivative x).deriv,
    (tanh_derivative |x|).deriv,Real.cosh_abs]

theorem actual_tanh_origin_secant_is_antitone_on_positive_inputs :
    AntitoneOn (fun x : ℝ => Real.tanh x / x) (Ioi 0) := by
  have h := tanh_concave_nonnegative.antitoneOn_slope_gt (show (0:ℝ) ∈ Ici 0 by simp)
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have he : slope Real.tanh 0 y ≤ slope Real.tanh 0 x :=
    h (show x ∈ {z ∈ Ici 0 | 0 < z} from ⟨hx0.le,hx0⟩)
      (show y ∈ {z ∈ Ici 0 | 0 < z} from ⟨hy0.le,hy0⟩) hxy
  simpa only [slope_def_field,Real.tanh_zero,sub_zero] using he

theorem actual_tanh_origin_secant_depends_only_on_absolute_input (x : ℝ) :
    Real.tanh x / x = Real.tanh |x| / |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx),Real.tanh_neg,neg_div_neg_eq]

theorem actual_origin_secant_larger_on_a_smaller_positive_interval
    (firstRadius secondRadius : ℝ) (hfirst : 0 < firstRadius)
    (hsecond : 0 < secondRadius) (hle : firstRadius ≤ secondRadius) :
    Real.tanh secondRadius / secondRadius ≤ Real.tanh firstRadius / firstRadius :=
  actual_tanh_origin_secant_is_antitone_on_positive_inputs hfirst hsecond hle

end SafeLearning.CompleteModulesTanhAsymptotic
