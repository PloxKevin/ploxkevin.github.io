import SafeLearning.CompleteModulesGoSafeToyAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyFeasibility
open SafeLearning.CompleteModulesGoSafeToyAffine

def actualSourceSafety (gain firstParameter : ℝ) : ℝ :=
  actualTrajectoryInfimum (actualRatio gain) (actualEquilibrium gain (actualReference firstParameter)) 0

theorem actual_source_zero_start_safety_is_the_true_equilibrium_margin
    (gain firstParameter : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    actualSourceSafety gain firstParameter=1-actualEquilibrium gain (actualReference firstParameter) := by
  have hr : 0 ≤ actualReference firstParameter := by
    unfold actualReference
    linarith [Real.neg_one_le_cos (4*Real.pi*firstParameter)]
  have h := actual_source_euler_ratio_and_positive_equilibrium gain (actualReference firstParameter) hg hr
  have hq : 0 ≤ actualRatio gain := by linarith [h.1.1]
  have hq1 : actualRatio gain < 1 := by linarith [h.1.2]
  unfold actualSourceSafety
  rw [actual_infinite_horizon_trajectory_infimum_is_the_literal_source_formula _ _ _ hq hq1 h.2.le]
  simp [max_eq_right h.2.le]

theorem actual_source_feasibility_is_exactly_the_literal_cosine_threshold
    (gain firstParameter : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    0 ≤ actualSourceSafety gain firstParameter ↔
      Real.cos (4*Real.pi*firstParameter) ≤ 1/4+1/(2*gain) := by
  have hgain : 0 < gain := by linarith [hg.1]
  have hden : 0 < 1+gain := by linarith
  rw [actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hg]
  unfold actualEquilibrium actualReference
  rw [sub_nonneg,div_le_iff₀ hden]
  have hid : (1/4:ℝ)+1/(2*gain)=(gain/4+1/2)/gain := by
    field_simp
  rw [hid,le_div_iff₀ hgain]
  constructor <;> intro h <;> nlinarith

theorem actual_quarter_and_three_quarter_references_are_zero_and_the_three_boundary_references_are_one_point_six :
    actualReference (1/4)=0 ∧ actualReference (3/4)=0 ∧
      actualReference 0=8/5 ∧ actualReference (1/2)=8/5 ∧ actualReference 1=8/5 := by
  have hquarter : 4*Real.pi*(1/4)=Real.pi := by ring
  have hthree : 4*Real.pi*(3/4)=3*Real.pi := by ring
  have hhalf : 4*Real.pi*(1/2)=2*Real.pi := by ring
  have hone : 4*Real.pi*1=2*(2*Real.pi) := by ring
  have hcos3 : Real.cos (3*Real.pi)=(-1:ℝ) := by
    have hc := Real.cos_nat_mul_pi 3
    norm_num at hc
    exact hc
  have hcos4 : Real.cos (2*(2*Real.pi))=1 := by simpa using Real.cos_nat_mul_two_pi 2
  simp only [actualReference,hquarter,hthree,hhalf,hone,Real.cos_pi,
    hcos3,Real.cos_two_pi,hcos4,mul_zero,Real.cos_zero]
  norm_num

theorem actual_quarter_and_three_quarter_are_safe_and_zero_half_one_are_unsafe_for_every_source_gain
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    0 < actualSourceSafety gain (1/4) ∧ 0 < actualSourceSafety gain (3/4) ∧
      actualSourceSafety gain 0 < 0 ∧ actualSourceSafety gain (1/2) < 0 ∧
      actualSourceSafety gain 1 < 0 := by
  have hden : 0 < 1+gain := by linarith [hg.1]
  have h := actual_quarter_and_three_quarter_references_are_zero_and_the_three_boundary_references_are_one_point_six
  have hsafe : (3/5:ℝ)/(1+gain)<1 := by
    apply (div_lt_one hden).mpr
    linarith [hg.1]
  have hunsafe : (1:ℝ)<(gain*(8/5)+3/5)/(1+gain) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [hg.1]
  simp only [actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hg,
    actualEquilibrium,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,mul_zero,zero_add]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SafeLearning.CompleteModulesGoSafeToyFeasibility
