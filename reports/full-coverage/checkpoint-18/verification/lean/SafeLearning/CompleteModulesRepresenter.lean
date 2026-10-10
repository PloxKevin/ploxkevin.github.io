import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesRepresenter

variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]

def regularizedLoss (feature : I → H) (loss : I → ℝ → ℝ) (regularizer : ℝ) (function : H) : ℝ :=
  (∑ i, loss i (inner ℝ function (feature i)))+regularizer*‖function‖^2

theorem every_regularized_minimizer_has_finite_representation
    (feature : I → H) (loss : I → ℝ → ℝ) (regularizer : ℝ) (hl : 0 < regularizer)
    (function : H)
    (hmin : ∀ candidate, regularizedLoss feature loss regularizer function ≤
      regularizedLoss feature loss regularizer candidate) :
    ∃ weight : I → ℝ, function=∑ i, weight i • feature i := by
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range feature)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range feature)
  let projected : H := S.starProjection function
  have hp : projected ∈ S := Submodule.starProjection_apply_mem S function
  have heval : ∀ i, inner ℝ function (feature i)=inner ℝ projected (feature i) := by
    intro i
    have hi : feature i ∈ S := Submodule.subset_span ⟨i,rfl⟩
    have he := Submodule.starProjection_inner_eq_zero (K:=S) function (feature i) hi
    rw [inner_sub_left] at he
    exact sub_eq_zero.mp he
  have ho : inner ℝ projected (function-projected)=0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero (K:=S) function projected hp
  have hnorm : ‖function‖^2=‖projected‖^2+‖function-projected‖^2 := by
    have hn := norm_add_sq_real projected (function-projected)
    rw [add_sub_cancel,ho,mul_zero,add_zero] at hn
    exact hn
  have hgap : regularizedLoss feature loss regularizer function=
      regularizedLoss feature loss regularizer projected+regularizer*‖function-projected‖^2 := by
    simp only [regularizedLoss,heval,hnorm]
    ring
  have hcomparison := hmin projected
  rw [hgap] at hcomparison
  have hprod : regularizer*‖function-projected‖^2 ≤ 0 := by linarith
  have hzsq : ‖function-projected‖^2=0 := le_antisymm
    ((mul_le_mul_iff_of_pos_left hl).mp (by simpa only [mul_zero] using hprod)) (sq_nonneg _)
  have he : function=projected := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq))
  obtain ⟨weight,hweight⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  exact ⟨weight,he.trans hweight.symm⟩

section ActualRKHS
variable [CompleteSpace H] [RKHS ℝ H X ℝ]

def rkhsRegularizedLoss (input : I → X) (loss : I → ℝ → ℝ)
    (regularizer : ℝ) (function : H) : ℝ :=
  (∑ i, loss i (function (input i)))+regularizer*‖function‖^2

theorem actual_rkhs_representer_theorem (input : I → X) (loss : I → ℝ → ℝ)
    (regularizer : ℝ) (hl : 0 < regularizer) (function : H)
    (hmin : ∀ candidate : H, rkhsRegularizedLoss input loss regularizer function ≤
      rkhsRegularizedLoss input loss regularizer candidate) :
    ∃ weight : I → ℝ, function=∑ i, weight i • RKHS.kerFun H (input i) 1 := by
  apply every_regularized_minimizer_has_finite_representation
    (fun i => RKHS.kerFun H (input i) 1) loss regularizer hl function
  simpa [regularizedLoss,rkhsRegularizedLoss] using hmin

theorem finite_rkhs_expansion_evaluates (input : I → X) (weight : I → ℝ) (x : X) :
    (∑ i, weight i • RKHS.kerFun H (input i) 1) x =
      ∑ i, weight i*(RKHS.kernel H x (input i)) 1 := by
  have hreproduce : ∀ f : H, inner ℝ f (RKHS.kerFun H x 1)=f x := by intro f; simp
  rw [← hreproduce]
  simp only [sum_inner,real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro i hi
  simp

end ActualRKHS
end SafeLearning.CompleteModulesRepresenter
