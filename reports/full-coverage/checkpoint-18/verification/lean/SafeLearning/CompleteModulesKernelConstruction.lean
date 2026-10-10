import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace SafeLearning.CompleteModulesKernelConstruction

variable {X I : Type*}

def operatorKernel (kernel : Matrix X X ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => kernel x y • ContinuousLinearMap.id ℝ ℝ

theorem operator_kernel_applies (kernel : Matrix X X ℝ) (x y : X) (value : ℝ) :
    operatorKernel kernel x y value=kernel x y*value := by
  simp [operatorKernel]

theorem scalar_kernel_operator_positive (kernel : Matrix X X ℝ) (hp : kernel.PosSemidef) :
    (operatorKernel kernel).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  constructor
  · apply Matrix.IsHermitian.ext
    intro x y
    have hs : kernel y x=kernel x y := by simpa using hp.isHermitian.apply x y
    simp [operatorKernel,hs,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_id]
  · intro coefficient
    have h := hp.2 coefficient
    have he : (coefficient.sum fun x value => coefficient.sum fun y other =>
        RCLike.re (inner ℝ (operatorKernel kernel y x value) other)) =
        coefficient.sum (fun x value => coefficient.sum fun y other =>
          star value*kernel x y*other) := by
      apply Finsupp.sum_congr
      intro x hx
      apply Finsupp.sum_congr
      intro y hy
      rw [operator_kernel_applies]
      have hs : kernel y x=kernel x y := by simpa using hp.isHermitian.apply x y
      simp only [hs,RCLike.re_to_real,RCLike.inner_apply,conj_trivial,star_trivial]
      ring
    simpa only [map_finsuppSum] using he ▸ h

instance operatorKernelPSD (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef] :
    Fact (operatorKernel kernel).PosSemidef := ⟨scalar_kernel_operator_positive kernel Fact.out⟩

abbrev constructedSpace (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef] :=
  RKHS.OfKernel (operatorKernel kernel)

theorem constructed_kernel_is_given (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef]
    (x y : X) : (RKHS.kernel (constructedSpace kernel) x y) 1=kernel x y := by
  rw [RKHS.OfKernel.kernel_ofKernel]
  simp [operatorKernel]

theorem constructed_sections_reproduce (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef]
    (function : constructedSpace kernel) (x : X) :
    inner ℝ function (RKHS.kerFun (constructedSpace kernel) x 1)=function x := by simp

theorem constructed_section_evaluates (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef]
    (x y : X) : (RKHS.kerFun (constructedSpace kernel) y 1) x=kernel x y := by
  rw [RKHS.kerFun_apply]
  exact constructed_kernel_is_given kernel x y

theorem constructed_section_inner (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef]
    (x y : X) : inner ℝ (RKHS.kerFun (constructedSpace kernel) x 1)
      (RKHS.kerFun (constructedSpace kernel) y 1)=kernel x y := by
  rw [constructed_sections_reproduce,constructed_section_evaluates]
  have hs : kernel y x=kernel x y := by
    simpa using (Fact.out : kernel.PosSemidef).isHermitian.apply x y
  exact hs

theorem constructed_finite_expansion_evaluates [Fintype I]
    (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef] (input : I → X) (weight : I → ℝ) (x : X) :
    (∑ i, weight i • RKHS.kerFun (constructedSpace kernel) (input i) 1) x=
      ∑ i, weight i*kernel x (input i) := by
  rw [← constructed_sections_reproduce]
  simp only [sum_inner,real_inner_smul_left,constructed_section_inner]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : kernel (input i) x=kernel x (input i) := by
    simpa using (Fact.out : kernel.PosSemidef).isHermitian.apply x (input i)
  rw [hs]

theorem constructed_finite_expansion_squared_norm [Fintype I]
    (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef] (input : I → X) (weight : I → ℝ) :
    ‖∑ i, weight i • RKHS.kerFun (constructedSpace kernel) (input i) 1‖^2=
      ∑ i, ∑ j, weight i*weight j*kernel (input i) (input j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    constructed_section_inner]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hs : kernel (input j) (input i)=kernel (input i) (input j) := by
    simpa using (Fact.out : kernel.PosSemidef).isHermitian.apply (input i) (input j)
  rw [hs]
  ring

theorem constructed_kernel_sections_dense (kernel : Matrix X X ℝ) [Fact kernel.PosSemidef] :
    Submodule.topologicalClosure (Submodule.span ℝ
      {RKHS.kerFun (constructedSpace kernel) x value | (x : X) (value : ℝ)})=⊤ :=
  RKHS.kerFun_dense (constructedSpace kernel)

end SafeLearning.CompleteModulesKernelConstruction
