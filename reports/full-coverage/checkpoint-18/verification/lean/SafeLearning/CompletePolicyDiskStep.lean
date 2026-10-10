import Mathlib

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompletePolicyDiskStep

def upperBoundary (t : ℝ) : ℝ := t + Real.sqrt (1 - t ^ 2)
def height : ℝ := Real.sqrt (24 / 25)

theorem actual_height_properties : 0 < height ∧ height ^ 2 = 24 / 25 ∧
    (1 / 5 : ℝ) < height := by
  have hp : 0 < height := Real.sqrt_pos.mpr (by norm_num)
  have hs : height ^ 2 = 24 / 25 := Real.sq_sqrt (by norm_num)
  exact ⟨hp, hs, by nlinarith⟩

theorem genuine_best_second_coordinate (a b : ℝ) (hdisk : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ 1 - a ^ 2 ∧ b ≤ Real.sqrt (1 - a ^ 2) := by
  have hr : 0 ≤ 1 - a ^ 2 := by nlinarith [sq_nonneg b]
  have hs := Real.sq_sqrt hr
  have hp := Real.sqrt_nonneg (1 - a ^ 2)
  exact ⟨hr, by nlinarith⟩

theorem actual_upper_boundary_derivative (t : ℝ) (hl : -1 < t) (hu : t < 1) :
    HasDerivAt upperBoundary (1 - t / Real.sqrt (1 - t ^ 2)) t := by
  have hr : 0 < 1 - t ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - t) (by linarith : 0 < 1 + t)]
  have hp : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hr
  have hd := (hasDerivAt_id t).add
    ((((hasDerivAt_id t).pow 2).const_sub 1).sqrt (ne_of_gt hr))
  simp only [id_eq, Pi.pow_apply] at hd
  convert hd using 1
  · ext x
    simp [upperBoundary]
  · field_simp
    ring

theorem actual_boundary_derivative_is_positive (t : ℝ)
    (hl : -1 < t) (hu : t ≤ 1 / 5) :
    0 < 1 - t / Real.sqrt (1 - t ^ 2) := by
  have ht : t < 1 := by linarith
  have hr : 0 < 1 - t ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - t) (by linarith : 0 < 1 + t)]
  have hp : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hr
  have hs := Real.sq_sqrt hr.le
  have hb : t < Real.sqrt (1 - t ^ 2) := by
    by_cases hn : t < 0
    · linarith
    · have hn' : 0 ≤ t := le_of_not_gt hn
      nlinarith [mul_nonneg hn' (by linarith : 0 ≤ 1 / 5 - t)]
  have hd : t / Real.sqrt (1 - t ^ 2) < 1 := (div_lt_one hp).mpr hb
  linarith

theorem genuine_cost_constrained_global_optimum (a b : ℝ)
    (hdisk : a ^ 2 + b ^ 2 ≤ 1) (hcost : a ≤ 1 / 5) :
    a + b ≤ 1 / 5 + height := by
  obtain ⟨hp, hs, ht⟩ := actual_height_properties
  have hsupport : a / 5 + height * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - height)]
  have hprice : 0 ≤ 1 - 1 / (5 * height) := by
    have h := (div_le_one (by positivity : 0 < 5 * height)).mpr
      (by linarith : (1 : ℝ) ≤ 5 * height)
    linarith
  have hweighted := mul_le_mul_of_nonneg_left hsupport (by positivity : 0 ≤ 1 / height)
  have hcostweighted := mul_le_mul_of_nonneg_left hcost hprice
  have hid : (1 / height) * (a / 5 + height * b) +
      (1 - 1 / (5 * height)) * a = a + b := by
    field_simp
    ring
  have hvalue : 1 / height + (1 - 1 / (5 * height)) / 5 = 1 / 5 + height := by
    field_simp
    nlinarith
  linarith

theorem actual_optimizer_and_active_constraints :
    (1 / 5 : ℝ) ^ 2 + height ^ 2 = 1 ∧
      upperBoundary (1 / 5) = 1 / 5 + height := by
  obtain ⟨_, hs, _⟩ := actual_height_properties
  constructor
  · nlinarith
  · unfold upperBoundary height
    congr 2
    norm_num

theorem actual_optimizer_and_objective_rounding :
    |height - (979796 / 1000000 : ℝ)| < 1 / 2000000 ∧
      |(1 / 5 + height) - (1179796 / 1000000 : ℝ)| < 1 / 2000000 := by
  obtain ⟨hp, hs, _⟩ := actual_height_properties
  have hl : (9797955 / 10000000 : ℝ) < height := by nlinarith
  have hu : height < (9797965 / 10000000 : ℝ) := by nlinarith
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_unconstrained_direction_fails_cost :
    (1 / Real.sqrt (2 : ℝ)) ^ 2 + (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 ∧
      (1 / 5 : ℝ) < 1 / Real.sqrt (2 : ℝ) := by
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · field_simp
    nlinarith
  · rw [lt_div_iff₀ hp]
    nlinarith

theorem genuine_unconstrained_disk_optimum (a b : ℝ) (hdisk : a ^ 2 + b ^ 2 ≤ 1) :
    a + b ≤ Real.sqrt 2 ∧
      1 / Real.sqrt (2 : ℝ) + 1 / Real.sqrt (2 : ℝ) = Real.sqrt 2 := by
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · nlinarith [sq_nonneg (a - b)]
  · field_simp
    nlinarith

end SafeLearning.CompletePolicyDiskStep
