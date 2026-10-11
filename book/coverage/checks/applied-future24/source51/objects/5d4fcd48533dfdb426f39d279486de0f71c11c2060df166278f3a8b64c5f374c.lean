import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsFunctionExamples

theorem projection_integrals :
    (∫ x : ℝ in (0 : ℝ)..1, x)=1/2 ∧
    (∫ _x : ℝ in (0 : ℝ)..1, (1 : ℝ))=1 ∧
    (∫ x : ℝ in (0 : ℝ)..1, x^2)=1/3 ∧
    (∫ x : ℝ in (0 : ℝ)..1, (x-1/2)^2)=1/12 := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · have he : (fun x : ℝ => (x-1/2)^2)=(fun x => x^2-x+1/4) := by ext x;ring
    rw [he,intervalIntegral.integral_add,intervalIntegral.integral_sub]
    · norm_num
    all_goals apply Continuous.intervalIntegrable;fun_prop

theorem constant_projection_characterization (c : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..1, x-c)=1/2-c ∧
    ((∫ x : ℝ in (0 : ℝ)..1, x-c)=0 ↔ c=1/2) := by
  have he : (∫ x : ℝ in (0 : ℝ)..1, x-c)=1/2-c := by
    rw [intervalIntegral.integral_sub] <;> norm_num
    all_goals fun_prop
  exact ⟨he,by rw [he];constructor <;> intro h <;> linarith⟩

theorem projection_norms :
    Real.sqrt (1 : ℝ)=1 ∧ Real.sqrt (1/3 : ℝ)=1/Real.sqrt 3 ∧
    (1/3 : ℝ)=(1/2)^2+1/12 := by
  constructor
  · norm_num
  constructor
  · rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ))];norm_num
  · norm_num

theorem polynomial_l2_norm (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, (x^n)^2)=1/(2*(n : ℝ)+1) := by
  simp only [← pow_mul,integral_pow]
  norm_num [Nat.cast_add,Nat.cast_mul,Nat.cast_one,mul_comm]

theorem affine_feature_kernel (x y : ℝ) :
    (1 : ℝ)*1+x*y=1+x*y := by ring

def affineGram : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,2]

theorem affine_gram_quadratic (a : Fin 2 → ℝ) :
    a ⬝ᵥ (affineGram.mulVec a)=(a 0+a 1)^2+(a 1)^2 := by
  simp [affineGram,Matrix.mulVec,dotProduct,Fin.sum_univ_succ];ring

theorem affine_gram_pd : affineGram.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j;fin_cases i <;> fin_cases j <;> norm_num [affineGram,Matrix.conjTranspose_apply]
  · intro a ha
    simp only [star_trivial,affine_gram_quadratic]
    have hn : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply ha
      ext i;fin_cases i <;> simp [h]
    rcases hn with h | h
    · nlinarith [sq_nonneg (a 0+a 1),sq_nonneg (a 1),sq_pos_of_ne_zero h]
    · nlinarith [sq_nonneg (a 0+a 1),sq_pos_of_ne_zero h]

theorem affine_gram_inverse : affineGram⁻¹=!![2,-1;-1,1] := by
  apply Matrix.inv_eq_right_inv
  ext i j;fin_cases i <;> fin_cases j <;>
    norm_num [affineGram,Matrix.mul_apply,Fin.sum_univ_succ]

theorem affine_interpolation_unique (w₁ w₂ : ℝ) :
    (w₁+w₂*0=1 ∧ w₁+w₂*1=3) ↔ w₁=1 ∧ w₂=2 := by
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem affine_interpolation_norm :
    affineGram⁻¹.mulVec (![1,3] : Fin 2 → ℝ)=![-1,2] ∧
    (![1,3] : Fin 2 → ℝ) ⬝ᵥ (affineGram⁻¹.mulVec ![1,3])=5 ∧
    (1 : ℝ)^2+2^2=5 := by
  rw [affine_gram_inverse]
  constructor
  · ext i;fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem affine_representer (x : ℝ) : -(1+0*x)+2*(1+1*x)=1+2*x := by ring

theorem affine_reproducing_bound (x : ℝ) :
    |1+2*x| ≤ Real.sqrt 5*Real.sqrt (1+x^2) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (1 : ℝ)+x^2)
  have h5 : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hp := mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg (1+x^2))
  have habs := sq_abs (1+2*x)
  have hm : (Real.sqrt 5*Real.sqrt (1+x^2))^2=5*(1+x^2) := by rw [mul_pow,h5,hs]
  nlinarith [sq_nonneg (x-2),abs_nonneg (1+2*x)]

theorem affine_not_uniformly_bounded :
    ¬ ∃ M : ℝ, ∀ x : ℝ, |1+2*x| ≤ M := by
  rintro ⟨M,hM⟩
  have hh := hM (|M|+1)
  have hp := le_abs_self M
  have hvalue : 0 ≤ 1+2*(|M|+1) := by positivity
  rw [abs_of_nonneg hvalue] at hh
  linarith

theorem affine_compact_uniform_bound (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    |1+2*x| ≤ Real.sqrt 10 := by
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  have ha : |1+2*x| ≤ 3 := by rw [abs_le];constructor <;> linarith [hx.1,hx.2]
  have hh : (3 : ℝ) ≤ Real.sqrt 10 := by nlinarith [Real.sqrt_nonneg 10]
  exact ha.trans hh

theorem polynomial_feature_kernel (x y : ℝ) :
    1+(Real.sqrt 2*x)*(Real.sqrt 2*y)+x^2*y^2=(1+x*y)^2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hm : (Real.sqrt 2*x)*(Real.sqrt 2*y)=2*x*y := by
    calc _ = (Real.sqrt 2)^2*(x*y) := by ring
         _ = _ := by rw [hs];ring
  rw [hm];ring

theorem riesz_representation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (L : E →L[ℝ] ℝ) :
    ∃! w : E, ∀ x : E, ⟪w,x⟫=L x := by
  refine ⟨(InnerProductSpace.toDual ℝ E).symm L,?_,?_⟩
  · intro x; exact InnerProductSpace.toDual_symm_apply
  · intro y hy
    apply (InnerProductSpace.toDual ℝ E).injective
    ext x
    simpa using hy x

end SafeLearning.CompleteFoundationsFunctionExamples
