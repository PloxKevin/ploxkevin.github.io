import SafeLearning.CompleteModulesGoSafeToyFeasibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyGridGainBounds
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility

theorem actual_source_gain_range_on_the_grid (i : Fin 25) :
    actualGain ((i.val:ℝ)/24) ∈ Icc (3:ℝ) 8 := by
  have hi : (i.val:ℝ) ≤ 24 := by exact_mod_cast (show i.val ≤ 24 by omega)
  have h0 : (0:ℝ) ≤ i.val := by positivity
  constructor <;> unfold actualGain <;> linarith

theorem actual_source_fixed_gain_margin_difference_is_the_literal_cosine_difference
    (gain x y : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    |actualSourceSafety gain x-actualSourceSafety gain y|=
      ((4/5)*gain/(1+gain))*|Real.cos (4*Real.pi*x)-Real.cos (4*Real.pi*y)| := by
  have hgain : 0 ≤ gain := by linarith [hg.1]
  have hden : 0 ≤ 1+gain := by linarith [hg.1]
  have hg0 : 0 ≤ (4/5)*gain/(1+gain) := by positivity
  have heq : actualSourceSafety gain x-actualSourceSafety gain y=
      -((4/5)*gain/(1+gain))*(Real.cos (4*Real.pi*x)-Real.cos (4*Real.pi*y)) := by
    rw [actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hg,
      actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hg]
    unfold actualEquilibrium actualReference
    ring
  rw [heq,abs_mul,abs_neg,abs_of_nonneg hg0]

theorem actual_source_gain_cosine_coefficient_is_nonnegative_and_at_most_thirty_two_over_forty_five
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    0 ≤ ((4/5)*gain/(1+gain)) ∧ ((4/5)*gain/(1+gain)) ≤ 32/45 := by
  have hd : 0 < 1+gain := by linarith [hg.1]
  constructor
  · apply div_nonneg <;> nlinarith [hg.1]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [hg.2]

theorem actual_source_gain_difference_has_the_true_vertical_parameter_bound
    (x y z : ℝ) (hy : y ∈ Icc (0:ℝ) 1) (hz : z ∈ Icc (0:ℝ) 1) :
    |actualSourceSafety (actualGain y) x-actualSourceSafety (actualGain z) x| ≤
      (5/16)*|y-z| := by
  have hgy : actualGain y ∈ Icc (3:ℝ) 8 := by constructor <;> unfold actualGain <;> linarith [hy.1,hy.2]
  have hgz : actualGain z ∈ Icc (3:ℝ) 8 := by constructor <;> unfold actualGain <;> linarith [hz.1,hz.2]
  have hdy : 0 < 1+actualGain y := by linarith [hgy.1]
  have hdz : 0 < 1+actualGain z := by linarith [hgz.1]
  have hd : 0 < (1+actualGain y)*(1+actualGain z) := mul_pos hdy hdz
  have hden : (16:ℝ) ≤ (1+actualGain y)*(1+actualGain z) := by
    have h := mul_le_mul (show (4:ℝ) ≤ 1+actualGain y by linarith [hgy.1])
      (show (4:ℝ) ≤ 1+actualGain z by linarith [hgz.1]) (by norm_num : (0:ℝ) ≤ 4) hdy.le
    norm_num at h
    exact h
  have hr : |actualReference x-3/5| ≤ (1:ℝ) := by
    rw [abs_le]
    unfold actualReference
    constructor <;> linarith [Real.neg_one_le_cos (4*Real.pi*x),Real.cos_le_one (4*Real.pi*x)]
  have heq : actualSourceSafety (actualGain y) x-actualSourceSafety (actualGain z) x=
      -(5*(y-z)*(actualReference x-3/5)/((1+actualGain y)*(1+actualGain z))) := by
    rw [actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hgy,
      actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hgz]
    unfold actualEquilibrium
    field_simp
    unfold actualGain
    ring
  rw [heq,abs_neg,abs_div,abs_mul,abs_mul,abs_of_pos hd]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5)]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5*|y-z| by positivity)
  have hn := mul_le_mul_of_nonneg_left hden (show 0 ≤ (5/16)*|y-z| by positivity)
  nlinarith

theorem actual_far_horizontal_and_vertical_bounds_give_the_source_euclidean_grid_constant
    (value dx dy : ℝ) (hx : 0 ≤ dx) (hy : 0 ≤ dy)
    (hv : |value| ≤ 8*dx+(5/16)*dy) :
    |value| ≤ (128/15)*Real.sqrt (dx^2+dy^2) := by
  have hs0 : 0 ≤ Real.sqrt (dx^2+dy^2) := Real.sqrt_nonneg _
  have hs : (Real.sqrt (dx^2+dy^2))^2=dx^2+dy^2 := Real.sq_sqrt (by positivity)
  have hc := sq_nonneg ((5/16)*dx-8*dy)
  have hv0 := abs_nonneg value
  have hu : 0 ≤ 8*dx+(5/16)*dy := by positivity
  have hsq := mul_self_le_mul_self hv0 hv
  nlinarith [sq_nonneg dx,sq_nonneg dy]

theorem actual_close_horizontal_steps_with_nonzero_vertical_steps_give_the_source_euclidean_grid_constant
    (value dx dy : ℝ) (hx : 0 ≤ dx) (hy : 0 ≤ dy) (hxy : dx ≤ 2*dy)
    (hv : |value| ≤ (128/15)*dx+(5/16)*dy) :
    |value| ≤ (128/15)*Real.sqrt (dx^2+dy^2) := by
  have hs0 := Real.sqrt_nonneg (dx^2+dy^2)
  have hs : (Real.sqrt (dx^2+dy^2))^2=dx^2+dy^2 := Real.sq_sqrt (by positivity)
  have hm := mul_le_mul_of_nonneg_right hxy hy
  have hv0 := abs_nonneg value
  have hu : 0 ≤ (128/15)*dx+(5/16)*dy := by positivity
  have hsq := mul_self_le_mul_self hv0 hv
  nlinarith [sq_nonneg dx,sq_nonneg dy]

end SafeLearning.CompleteModulesGoSafeToyGridGainBounds
