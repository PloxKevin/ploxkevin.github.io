import SafeLearning.CompleteModulesKernel
import SafeLearning.CompleteModulesKernelMetric
import SafeLearning.CompleteModulesKernelFunctional

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsRKHSBounds22

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ]

 theorem actual_diagonal_kernel_bound_gives_the_uniform_rkhs_ball_pointwise_bound
    (B kappa : ℝ≥0) (function : H) (hfunction : ‖function‖ ≤ (B : ℝ))
    (hkernel : ∀ x : X, CompleteModulesKernel.scalarKernel (H := H) x x ≤ (kappa : ℝ)^2)
    (x : X) : |function x| ≤ (B : ℝ)*(kappa : ℝ) := by
  have hsection : ‖RKHS.kerFun H x 1‖ ≤ (kappa : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) kappa.coe_nonneg).mp
    simpa only [CompleteModulesKernel.scalarKernel, CompleteModulesKernel.featureKernel,
      CompleteModulesKernel.scalarSection, real_inner_self_eq_norm_sq] using hkernel x
  have hpoint := CompleteModulesKernelMetric.point_evaluation_bound function x
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] at hpoint
  exact hpoint.trans (mul_le_mul hfunction hsection (norm_nonneg _) B.coe_nonneg)

 theorem actual_diagonal_kernel_bound_gives_the_literal_uniform_supremum_bound
    (B kappa : ℝ≥0) (function : H) (hfunction : ‖function‖ ≤ (B : ℝ))
    (hkernel : ∀ x : X, CompleteModulesKernel.scalarKernel (H := H) x x ≤ (kappa : ℝ)^2) :
    BddAbove (Set.range (fun x : X => |function x|)) ∧
      sSup (Set.range (fun x : X => |function x|)) ≤ (B : ℝ)*(kappa : ℝ) := by
  have hbound (x : X) :=
    actual_diagonal_kernel_bound_gives_the_uniform_rkhs_ball_pointwise_bound
      B kappa function hfunction hkernel x
  have hb : BddAbove (Set.range (fun x : X => |function x|)) :=
    ⟨(B : ℝ)*(kappa : ℝ), by rintro value ⟨x,rfl⟩; exact hbound x⟩
  refine ⟨hb, ?_⟩
  by_cases hx : Nonempty X
  · letI : Nonempty X := hx
    exact csSup_le (Set.range_nonempty _) (by rintro value ⟨x,rfl⟩; exact hbound x)
  · letI : IsEmpty X := ⟨fun x => hx ⟨x⟩⟩
    simpa using mul_nonneg B.coe_nonneg kappa.coe_nonneg

 theorem actual_linear_kernel_unit_ball_contains_the_unbounded_identity_function :
    ‖(1 : ℝ)‖ = 1 ∧
      (∀ x : ℝ, CompleteModulesRKHSStructure.linearFunction 1 x = x) ∧
      ¬ BddAbove (Set.range (fun x : ℝ =>
        |CompleteModulesRKHSStructure.linearFunction 1 x|)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro x
    simp [CompleteModulesRKHSStructure.linear_function_evaluation]
  · rintro ⟨bound,hbound⟩
    have h := hbound (Set.mem_range_self (|bound|+1))
    simp only [CompleteModulesRKHSStructure.linear_function_evaluation, one_mul] at h
    rw [abs_of_pos (by positivity : 0 < |bound|+1)] at h
    linarith [le_abs_self bound]

 theorem actual_linear_rkhs_has_the_source_kernel_and_a_norm_one_unbounded_function :
    letI : RKHS ℝ ℝ ℝ ℝ := CompleteModulesRKHSStructure.linearRKHS
    (∀ x y : ℝ, (RKHS.kernel ℝ x y) 1 = x*y) ∧
      ‖(1 : ℝ)‖ = 1 ∧ (∀ x : ℝ, (1 : ℝ) x = x) ∧
      ¬ BddAbove (Set.range (fun x : ℝ => |(1 : ℝ) x|)) := by
  letI : RKHS ℝ ℝ ℝ ℝ := CompleteModulesRKHSStructure.linearRKHS
  have hw := actual_linear_kernel_unit_ball_contains_the_unbounded_identity_function
  refine ⟨CompleteModulesKernelFunctional.actual_linear_kernel_formula, hw.1, ?_, ?_⟩
  · intro x
    change x*1=x
    ring
  · change ¬ BddAbove (Set.range (fun x : ℝ => |CompleteModulesRKHSStructure.linearFunction 1 x|))
    exact hw.2.2

end SafeLearning.CompleteFoundationsRKHSBounds22
