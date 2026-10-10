import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteExponentialBarrierClassK

def alpha (pole r : ℝ) : ℝ := pole * r

theorem actual_positive_linear_extended_class_K (pole : ℝ) (hpole : 0 < pole) :
    Continuous (alpha pole) ∧ StrictMono (alpha pole) ∧ alpha pole 0 = 0 := by
  refine ⟨continuous_const.mul continuous_id, ?_, by simp [alpha]⟩
  intro x y hxy
  exact mul_lt_mul_of_pos_left hxy hpole

theorem both_actual_nested_functions_are_class_K (p1 p2 : ℝ)
    (h1 : 0 < p1) (h2 : 0 < p2) :
    (Continuous (alpha p1) ∧ StrictMono (alpha p1) ∧ alpha p1 0 = 0) ∧
      (Continuous (alpha p2) ∧ StrictMono (alpha p2) ∧ alpha p2 0 = 0) :=
  ⟨actual_positive_linear_extended_class_K p1 h1,
    actual_positive_linear_extended_class_K p2 h2⟩

end SafeLearning.CompleteExponentialBarrierClassK
