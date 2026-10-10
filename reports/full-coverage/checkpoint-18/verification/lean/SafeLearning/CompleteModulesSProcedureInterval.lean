import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesSProcedureInterval

def actualIntervalConstraint (point : ℝ) : ℝ := 1-point^2
def actualIntervalTarget (point : ℝ) : ℝ := 2-point^2
def actualIntervalResidual (multiplier point : ℝ) : ℝ :=
  actualIntervalTarget point-multiplier*actualIntervalConstraint point

theorem actual_scalar_even_quadratic_globally_nonnegative_iff_each_coefficient_nonnegative
    (constant coefficient : ℝ) :
    (∀ point : ℝ,0 ≤ constant+coefficient*point^2) ↔ 0 ≤ constant ∧ 0 ≤ coefficient := by
  constructor
  · intro h
    have hconstant : 0 ≤ constant := by simpa using h 0
    refine ⟨hconstant,?_⟩
    by_contra hcoefficient
    have hc : coefficient<0 := lt_of_not_ge hcoefficient
    have hd : 0 ≤ (constant+1)/(-coefficient) := div_nonneg (by linarith) (by linarith)
    have hs := Real.sq_sqrt hd
    have hm : coefficient*((constant+1)/(-coefficient))= -(constant+1) := by
      field_simp [ne_of_lt hc]
    have hw := h (Real.sqrt ((constant+1)/(-coefficient)))
    rw [hs,hm] at hw;linarith
  · rintro ⟨hconstant,hcoefficient⟩ point
    exact add_nonneg hconstant (mul_nonneg hcoefficient (sq_nonneg point))

theorem actual_interval_residual_has_the_literal_source_coefficients (multiplier point : ℝ) :
    actualIntervalResidual multiplier point=(2-multiplier)+(multiplier-1)*point^2 := by
  unfold actualIntervalResidual actualIntervalConstraint actualIntervalTarget;ring

theorem actual_interval_all_globally_valid_multipliers_are_exactly_one_through_two
    (multiplier : ℝ) :
    (0 ≤ multiplier ∧ ∀ point : ℝ,0 ≤ actualIntervalResidual multiplier point) ↔
      1 ≤ multiplier ∧ multiplier ≤ 2 := by
  simp only [actual_interval_residual_has_the_literal_source_coefficients,
    actual_scalar_even_quadratic_globally_nonnegative_iff_each_coefficient_nonnegative]
  constructor
  · rintro ⟨_,hconstant,hcoefficient⟩;constructor <;> linarith
  · rintro ⟨hl,hu⟩;exact ⟨by linarith,by linarith,by linarith⟩

theorem actual_nonnegative_certificate_proves_the_true_pointwise_implication
    {Signal : Type*} (target constraint : Signal→ℝ) (multiplier : ℝ)
    (hmultiplier : 0 ≤ multiplier)
    (hcertificate : ∀ point,0 ≤ target point-multiplier*constraint point) :
    ∀ point,0 ≤ constraint point→0 ≤ target point := by
  intro point hpoint
  have hm := mul_nonneg hmultiplier hpoint
  have hc := hcertificate point
  linarith

theorem actual_source_multiplier_one_leaves_the_constant_one (point : ℝ) :
    actualIntervalResidual 1 point=1 := by
  rw [actual_interval_residual_has_the_literal_source_coefficients];ring

theorem actual_source_interval_implication_follows_from_the_nonnegative_multiplier_certificate :
    ∀ point : ℝ,0 ≤ actualIntervalConstraint point→0 ≤ actualIntervalTarget point := by
  apply actual_nonnegative_certificate_proves_the_true_pointwise_implication
    actualIntervalTarget actualIntervalConstraint 1 (by norm_num)
  intro point
  change 0 ≤ actualIntervalResidual 1 point
  rw [actual_source_multiplier_one_leaves_the_constant_one];norm_num

theorem actual_source_constraint_is_strictly_feasible_at_zero :
    0 < actualIntervalConstraint 0 := by norm_num [actualIntervalConstraint]

theorem actual_general_quadratic_implication_can_fail_to_admit_a_certificate_without_strict_feasibility :
    (∀ point : ℝ,-point^2 ≤ 0) ∧
    (∀ point : ℝ,0 ≤ -point^2→0 ≤ point) ∧
    ¬∃ multiplier : ℝ,0 ≤ multiplier ∧ ∀ point : ℝ,0 ≤ point-multiplier*(-point^2) := by
  refine ⟨fun point => by nlinarith [sq_nonneg point],?_,?_⟩
  · intro point hpoint
    have hz : point=0 := by nlinarith [sq_nonneg point]
    rw [hz]
  · rintro ⟨multiplier,hmultiplier,hcertificate⟩
    have hd : 0 < multiplier+1 := by linarith
    have hw := hcertificate (-1/(multiplier+1))
    have he : (-1/(multiplier+1))-multiplier*(-(-1/(multiplier+1))^2)=
        -1/(multiplier+1)^2 := by field_simp;ring
    rw [he] at hw
    have hn : -1/(multiplier+1)^2<0 := div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hd)
    linarith

end SafeLearning.CompleteModulesSProcedureInterval
