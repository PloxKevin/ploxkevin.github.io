import SafeLearning.CompleteCoreMPCFirstSuccessor27
import Mathlib.Algebra.Field.GeomSum

set_option autoImplicit false
noncomputable section
open Finset

namespace SafeLearning.CompleteCoreMPCExactTightening28

def originalTrackingRadius (rho cL cU lambda eta : ℝ) (j : ℕ) : ℝ :=
  (Real.sqrt rho) ^ j * (lambda * eta * Real.sqrt (cU / cL))

def originalTightening (epsilon rho : ℝ) (j : ℕ) : ℝ :=
  epsilon * ∑ i ∈ Finset.range j, (Real.sqrt rho) ^ i

/-- The source radius budget is an exact identity, not an upper bound supplied
as a premise. This includes zero input disturbance and singular row norms. -/
theorem actual_original_radius_has_the_exact_geometric_value_budget
    (rho cL cU lambda eta : ℝ) (j : ℕ)
    (hrho : 0 ≤ rho) (hcL : 0 < cL) (hcU : 0 ≤ cU)
    (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) :
    0 ≤ originalTrackingRadius rho cL cU lambda eta j ∧
    rho ^ j * (cU * (lambda * eta) ^ 2) =
      cL * originalTrackingRadius rho cL cU lambda eta j ^ 2 := by
  have hratio : 0 ≤ cU / cL := div_nonneg hcU hcL.le
  have hq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho
  have hp : ((Real.sqrt rho) ^ j) ^ 2 = rho ^ j := by
    calc
      ((Real.sqrt rho) ^ j) ^ 2 = ((Real.sqrt rho) ^ 2) ^ j := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = rho ^ j := by rw [hq]
  have hcancel : cL * (cU / cL) = cU := by
    field_simp
  constructor
  · exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg rho) j)
      (mul_nonneg (mul_nonneg hlambda heta) (Real.sqrt_nonneg _))
  · dsimp [originalTrackingRadius]
    rw [mul_pow, hp, mul_pow, Real.sq_sqrt hratio]
    nlinarith [hcancel]

/-- Increasing the finite tightening by one stage adds exactly the current
geometric increment. Every budget is nonnegative and the levels are monotone. -/
theorem actual_original_tightening_has_exact_increments_and_is_monotone
    (epsilon rho : ℝ) (hepsilon : 0 ≤ epsilon) :
    (∀ j, 0 ≤ originalTightening epsilon rho j) ∧
    (∀ j, originalTightening epsilon rho (j+1)-originalTightening epsilon rho j =
      epsilon * (Real.sqrt rho) ^ j) ∧
    Monotone (originalTightening epsilon rho) := by
  have hnonneg : ∀ j, 0 ≤ originalTightening epsilon rho j := by
    intro j
    exact mul_nonneg hepsilon (Finset.sum_nonneg (fun i _ => pow_nonneg (Real.sqrt_nonneg rho) i))
  have hincrement : ∀ j,
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j =
        epsilon * (Real.sqrt rho) ^ j := by
    intro j
    simp only [originalTightening, Finset.sum_range_succ]
    ring
  refine ⟨hnonneg, hincrement, monotone_nat_of_le_succ ?_⟩
  intro j
  have h := hincrement j
  have hp := mul_nonneg hepsilon (pow_nonneg (Real.sqrt_nonneg rho) j)
  linarith

/-- The printed max of row norms bounds both actual state and input tracking
increments with the source's exact radius and tightening formula. -/
theorem actual_original_max_norm_tightening_covers_both_tracking_rows
    (rho cL cU lambda eta H L k : ℝ) (j : ℕ)
    (hcL : 0 < cL) (hcU : 0 ≤ cU) (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hk : 0 ≤ k) :
    let epsilon := lambda * eta * Real.sqrt (cU/cL) * max H (L*k)
    0 ≤ epsilon ∧
    H * originalTrackingRadius rho cL cU lambda eta j ≤
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j ∧
    L * (k * originalTrackingRadius rho cL cU lambda eta j) ≤
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j := by
  dsimp
  let R := lambda * eta * Real.sqrt (cU/cL)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg hlambda heta) (Real.sqrt_nonneg _)
  have hM : 0 ≤ max H (L*k) := hH.trans (le_max_left _ _)
  have hepsilon : 0 ≤ R * max H (L*k) := mul_nonneg hR hM
  have hinc := (actual_original_tightening_has_exact_increments_and_is_monotone
    (R * max H (L*k)) rho hepsilon).2.1 j
  have hq := pow_nonneg (Real.sqrt_nonneg rho) j
  have hstate := mul_le_mul_of_nonneg_left (le_max_left H (L*k)) (mul_nonneg hq hR)
  have hinput := mul_le_mul_of_nonneg_left (le_max_right H (L*k)) (mul_nonneg hq hR)
  refine ⟨hepsilon, ?_, ?_⟩
  · change H * ((Real.sqrt rho)^j * R) ≤ _
    rw [hinc]
    nlinarith [hstate]
  · change L * (k * ((Real.sqrt rho)^j * R)) ≤ _
    rw [hinc]
    nlinarith [hinput]

/-- The finite sum is exactly the displayed quotient when the contraction
rate is in its original interval. The denominator is strictly positive. -/
theorem actual_original_tightening_is_the_printed_geometric_quotient
    (epsilon rho : ℝ) (j : ℕ) (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    0 < 1-Real.sqrt rho ∧
    originalTightening epsilon rho j =
      epsilon * (1-(Real.sqrt rho)^j)/(1-Real.sqrt rho) := by
  have hq0 := Real.sqrt_nonneg rho
  have hq2 := Real.sq_sqrt hrho
  have hq1 : Real.sqrt rho < 1 := by nlinarith
  constructor
  · linarith
  · dsimp [originalTightening]
    rw [geom_sum_eq (ne_of_lt hq1)]
    field_simp
    ring

end SafeLearning.CompleteCoreMPCExactTightening28
