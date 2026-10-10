import SafeLearning.CompleteModulesRKHSStructure
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeKnownBounds
open CompleteModulesRKHSStructure

theorem actual_known_linear_RKHS_coefficient_has_an_exact_squared_norm_bound
    (coefficient : ℝ) :
    ‖coefficient‖^2=coefficient^2 ∧
      (∀B : ℝ, ‖coefficient‖^2≤B ↔ coefficient^2≤B) ∧
      ∀x : ℝ, linearFunction coefficient x=coefficient*x := by
  refine ⟨by rw [Real.norm_eq_abs,sq_abs],?_,linear_function_evaluation coefficient⟩
  intro B
  rw [Real.norm_eq_abs,sq_abs]

theorem actual_known_linear_RKHS_function_has_the_exact_least_global_Lipschitz_constant
    (coefficient : ℝ) :
    IsLeast {L : ℝ | 0≤L ∧ ∀x y : ℝ,
      |linearFunction coefficient x-linearFunction coefficient y|≤L*dist x y} |coefficient| := by
  constructor
  · refine ⟨abs_nonneg _,?_⟩
    intro x y
    rw [linear_function_evaluation,linear_function_evaluation,Real.dist_eq,
      ←mul_sub,abs_mul]
  · intro L hL
    have hh := hL.2 1 0
    simpa [linear_function_evaluation,Real.dist_eq] using hh

def design (a : Bool) : ℝ := if a then 2 else 1

theorem actual_underestimated_Lipschitz_constant_can_still_certify_only_safe_points :
    (0:ℝ)<1 ∧
      ¬(∀x y : ℝ, |linearFunction 1 x-linearFunction 1 y|≤(0:ℝ)*dist x y) ∧
      (∀a : Bool, 0≤(1:ℝ)-(0:ℝ)*dist 1 (design a)) ∧
      ∀a : Bool, 0≤linearFunction 1 (design a) := by
  refine ⟨by norm_num,?_,by intro a;norm_num,?_⟩
  · intro h
    have hh := h 1 0
    norm_num [linear_function_evaluation] at hh
  · intro a
    cases a <;> norm_num [linear_function_evaluation,design]

theorem actual_safe_positive_design_keeps_every_query_safe_even_under_wrong_bounds
    (queries : ℕ → Bool) :
    (1/4:ℝ)<‖(1:ℝ)‖^2 ∧
      ∀t : ℕ, 0≤linearFunction 1 (design (queries t)) := by
  refine ⟨by norm_num,?_⟩
  intro t
  cases queries t <;> norm_num [linear_function_evaluation,design]
end SafeLearning.CompleteModulesLandscapeKnownBounds
