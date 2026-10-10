import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
namespace SafeLearning.CompleteModulesSDPTrace

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

theorem actual_psd_matrices_have_nonnegative_trace_pairing
    (first second : Matrix Index Index ℝ) (hf : first.PosSemidef) (hs : second.PosSemidef) :
    0 ≤ (first*second).trace := by
  obtain ⟨factor,hfactor⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hs.nonneg
  have he : second=factorᵀ*factor := by simpa [Matrix.star_eq_conjTranspose] using hfactor
  rw [he,←Matrix.mul_assoc,Matrix.trace_mul_cycle]
  have hc : (factor*first*factorᵀ).PosSemidef := by simpa using hf.mul_mul_conjTranspose_same factor
  exact hc.trace_nonneg

theorem actual_psd_cone_is_self_dual_under_the_true_trace_pairing
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix.PosSemidef ↔ ∀ test : Matrix Index Index ℝ,test.PosSemidef→0 ≤ (test*matrix).trace := by
  constructor
  · intro hm test ht
    exact actual_psd_matrices_have_nonnegative_trace_pairing test matrix ht hm
  · intro htests
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymmetric
    intro vector
    have htest : (Matrix.vecMulVec vector vector).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star vector
    have h := htests (Matrix.vecMulVec vector vector) htest
    rw [Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm] at h
    simpa only [star_trivial] using h

theorem actual_trace_zero_of_two_psd_matrices_iff_actual_matrix_product_zero
    (first second : Matrix Index Index ℝ) (hf : first.PosSemidef) (hs : second.PosSemidef) :
    (first*second).trace=0 ↔ first*second=0 := by
  constructor
  · intro htrace
    obtain ⟨firstFactor,hfirst⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hf.nonneg
    obtain ⟨secondFactor,hsecond⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hs.nonneg
    have hefirst : first=firstFactorᵀ*firstFactor := by simpa [Matrix.star_eq_conjTranspose] using hfirst
    have hesecond : second=secondFactorᵀ*secondFactor := by simpa [Matrix.star_eq_conjTranspose] using hsecond
    have he : (first*second).trace=
        ((firstFactor*secondFactorᵀ)*(firstFactor*secondFactorᵀ)ᵀ).trace := by
      rw [hefirst,hesecond]
      calc
        _ = (firstFactorᵀ*(firstFactor*(secondFactorᵀ*secondFactor))).trace := by rw [Matrix.mul_assoc]
        _ = ((firstFactor*(secondFactorᵀ*secondFactor))*firstFactorᵀ).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    rw [he] at htrace
    have hfactor : firstFactor*secondFactorᵀ=0 := by
      apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
      simpa using htrace
    rw [hefirst,hesecond]
    calc
      _ = firstFactorᵀ*(firstFactor*secondFactorᵀ)*secondFactor := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hfactor,Matrix.mul_zero,Matrix.zero_mul]
  · intro hzero;rw [hzero];simp

omit [DecidableEq Index] in
theorem actual_trace_pairing_zero_iff_frobenius_factor_zero
    (firstFactor secondFactor : Matrix Index Index ℝ) :
    ((firstFactorᵀ*firstFactor)*(secondFactorᵀ*secondFactor)).trace=0 ↔
      firstFactor*secondFactorᵀ=0 := by
  have he : ((firstFactorᵀ*firstFactor)*(secondFactorᵀ*secondFactor)).trace=
      ((firstFactor*secondFactorᵀ)*(firstFactor*secondFactorᵀ)ᵀ).trace := by
    calc
      _ = (firstFactorᵀ*(firstFactor*(secondFactorᵀ*secondFactor))).trace := by rw [Matrix.mul_assoc]
      _ = ((firstFactor*(secondFactorᵀ*secondFactor))*firstFactorᵀ).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
  rw [he]
  simpa using Matrix.trace_mul_conjTranspose_self_eq_zero_iff (A:=firstFactor*secondFactorᵀ)

end SafeLearning.CompleteModulesSDPTrace
