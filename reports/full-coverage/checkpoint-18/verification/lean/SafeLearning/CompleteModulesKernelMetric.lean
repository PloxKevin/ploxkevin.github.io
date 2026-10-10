import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesKernelMetric

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def kernelDistance (feature : X → H) (x y : X) : ℝ := dist (feature x) (feature y)

theorem kernel_distance_nonnegative (feature : X → H) (x y : X) :
    0 ≤ kernelDistance feature x y := dist_nonneg

theorem kernel_distance_self (feature : X → H) (x : X) :
    kernelDistance feature x x=0 := dist_self _

theorem kernel_distance_symmetric (feature : X → H) (x y : X) :
    kernelDistance feature x y=kernelDistance feature y x := dist_comm _ _

theorem kernel_distance_triangle (feature : X → H) (x y z : X) :
    kernelDistance feature x z ≤ kernelDistance feature x y+kernelDistance feature y z :=
  dist_triangle _ _ _

theorem kernel_distance_zero_iff (feature : X → H) (x y : X) :
    kernelDistance feature x y=0 ↔ feature x=feature y := dist_eq_zero

theorem kernel_distance_squared_identity (feature : X → H) (x y : X) :
    kernelDistance feature x y^2=inner ℝ (feature x) (feature x)+
      inner ℝ (feature y) (feature y)-2*inner ℝ (feature x) (feature y) := by
  rw [kernelDistance,dist_eq_norm, norm_sub_sq_real]
  simp only [real_inner_self_eq_norm_sq]
  ring

theorem kernel_distance_separates_iff_injective (feature : X → H) :
    (∀ x y, kernelDistance feature x y=0 ↔ x=y) ↔ Function.Injective feature := by
  constructor
  · intro h x y he
    exact (h x y).mp ((kernel_distance_zero_iff feature x y).mpr he)
  · intro hinj x y
    rw [kernel_distance_zero_iff]
    exact ⟨fun h => hinj h,fun h => congrArg feature h⟩

theorem constant_kernel_does_not_separate :
    kernelDistance (fun _ : Bool => (0:ℝ)) false true=0 ∧ false≠true := by
  simp [kernelDistance]

theorem strictly_positive_two_point_gram_gives_injectivity (feature : X → H)
    (hpositive : ∀ x y, x≠y →
      (Matrix.gram ℝ (fun i : Fin 2 => if i=0 then feature x else feature y)).PosDef) :
    Function.Injective feature := by
  intro x y he
  by_contra hxy
  have hli := Matrix.linearIndependent_of_posDef_gram (hpositive x y hxy)
  have he01 : (if (0 : Fin 2)=0 then feature x else feature y)=
      (if (1 : Fin 2)=0 then feature x else feature y) := by simpa using he
  have h01 : (0 : Fin 2)=1 := hli.injective he01
  norm_num at h01

theorem se_distance_bounded (radius lengthscale : ℝ) :
    Real.sqrt (2*(1-Real.exp (-(radius^2/(2*lengthscale^2))))) ≤ Real.sqrt 2 := by
  apply Real.sqrt_le_sqrt
  linarith [Real.exp_pos (-(radius^2/(2*lengthscale^2)))]

section ActualRKHS
variable [CompleteSpace H] [RKHS ℝ H X ℝ]

theorem point_evaluation_bound (function : H) (x : X) :
    |function x| ≤ ‖function‖*Real.sqrt (inner ℝ (RKHS.kerFun H x 1) (RKHS.kerFun H x 1)) := by
  have hr : inner ℝ function (RKHS.kerFun H x 1)=function x := by simp
  rw [← hr,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem norm_zero_is_zero_function (function : H) (hn : ‖function‖=0) :
    ∀ x, function x=0 := by
  rw [norm_eq_zero.mp hn]
  simp

end ActualRKHS
end SafeLearning.CompleteModulesKernelMetric
