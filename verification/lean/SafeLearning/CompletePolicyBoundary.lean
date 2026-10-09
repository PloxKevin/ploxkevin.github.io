import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompletePolicyBoundary

def residual (x : ℝ) : ℝ := -(1 / 10) + x + 2 * x ^ 2
def linearized (x : ℝ) : ℝ := -(1 / 10) + x
def largestStep : ℝ := (-1 + Real.sqrt (9 / 5)) / 4

theorem actual_residual_derivative (x : ℝ) : HasDerivAt residual (1 + 4 * x) x := by
  convert ((hasDerivAt_const x (-(1 / 10 : ℝ))).add (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 2).const_mul 2) using 1 <;>
    first | (ext y; simp [residual, id_eq]) | (simp [id_eq]; ring)

theorem actual_first_order_model (x : ℝ) :
    residual 0 + deriv residual 0 * (x - 0) = linearized x ∧
      residual x - linearized x = 2 * x ^ 2 := by
  rw [(actual_residual_derivative 0).deriv]
  constructor <;> unfold residual linearized <;> ring

theorem linearized_boundary_is_truly_infeasible :
    linearized (1 / 10) = 0 ∧ residual (1 / 10) = 1 / 50 ∧
      0 < residual (1 / 10) := by norm_num [linearized, residual]

theorem actual_positive_root : 0 < largestStep ∧ residual largestStep = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 / 5 by norm_num)
  have hn := Real.sqrt_nonneg (9 / 5 : ℝ)
  constructor
  · unfold largestStep
    nlinarith
  · unfold largestStep residual
    nlinarith

theorem residual_increases_on_nonnegative_steps : StrictMonoOn residual (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold residual
  nlinarith [mul_pos (by linarith : 0 < y - x) (by linarith : 0 < x + y)]

theorem exact_nonnegative_feasible_interval (x : ℝ) :
    0 ≤ x ∧ residual x ≤ 0 ↔ x ∈ Set.Icc 0 largestStep := by
  obtain ⟨hr, hzero⟩ := actual_positive_root
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    by_contra h
    have hs := residual_increases_on_nonnegative_steps hr.le hx (lt_of_not_ge h)
    rw [hzero] at hs
    linarith
  · rintro ⟨hx, hxr⟩
    refine ⟨hx, ?_⟩
    rcases hxr.eq_or_lt with h | h
    · simpa [h] using hzero.le
    · exact (residual_increases_on_nonnegative_steps hx hr.le h).le.trans hzero.le

theorem actual_six_decimal_rounding :
    (8541 / 100000 : ℝ) < largestStep ∧ largestStep < 170821 / 2000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 / 5 by norm_num)
  have hn := Real.sqrt_nonneg (9 / 5 : ℝ)
  unfold largestStep
  constructor <;> nlinarith

theorem exact_remainder_margin (x : ℝ) (hmargin : linearized x ≤ -(2 * x ^ 2)) :
    residual x ≤ 0 := by
  have hm := (actual_first_order_model x).2
  linarith

end SafeLearning.CompletePolicyBoundary
