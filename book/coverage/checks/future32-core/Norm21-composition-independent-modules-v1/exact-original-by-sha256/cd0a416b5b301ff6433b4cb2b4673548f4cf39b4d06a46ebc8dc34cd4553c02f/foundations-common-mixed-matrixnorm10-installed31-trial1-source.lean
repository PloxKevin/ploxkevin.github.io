import SafeLearning.CompleteFoundationsHolderDualNormWholeUnits30
import SafeLearning.CompleteFoundationsInducedNormProductCertificates30
import SafeLearning.CompleteFoundationsRayleighQuotientWhole30
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Matrix Set
open scoped BigOperators ENNReal RealInnerProductSpace
namespace SafeLearning.CompleteFoundationsCommonMixedInducedNormFormulas32
open CompleteFoundationsHolderDualNormWholeUnits30
open CompleteFoundationsInducedNormProductCertificates30
open CompleteFoundationsRayleighQuotientWhole30
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def columnMaximum [Nonempty n] (p : ℝ≥0∞) (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => sourcePNorm p (fun i => A i j))
def rowMaximum [Nonempty m] (q : ℝ≥0∞) (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => sourcePNorm q (A i))

private theorem column_maximum_nonnegative [Nonempty n]
    (p : ℝ≥0∞) [Fact (1≤p)] (A : Matrix m n ℝ) : 0≤columnMaximum p A := by
  let j : n := Classical.choice inferInstance
  exact (actual_pnorm_nonnegative (fun i => A i j)).trans
    (Finset.le_sup' (fun j => sourcePNorm p (fun i => A i j)) (Finset.mem_univ j))

private theorem row_maximum_nonnegative [Nonempty m]
    (q : ℝ≥0∞) [Fact (1≤q)] (A : Matrix m n ℝ) : 0≤rowMaximum q A := by
  let i : m := Classical.choice inferInstance
  exact (actual_pnorm_nonnegative (A i)).trans
    (Finset.le_sup' (fun i => sourcePNorm q (A i)) (Finset.mem_univ i))

theorem actual_matrix_action_is_the_sum_of_its_input_scaled_columns
    (p : ℝ≥0∞) [Fact (1≤p)] (A : Matrix m n ℝ) (x : n → ℝ) :
    (WithLp.toLp p (A *ᵥ x) : PiLp p (fun _ : m => ℝ))=
      ∑ j,x j • (WithLp.toLp p (fun i => A i j) : PiLp p (fun _ : m => ℝ)) := by
  ext i
  simp [Matrix.mulVec,dotProduct,Finset.sum_apply,PiLp.sum_apply,PiLp.smul_apply,mul_comm]

theorem actual_one_to_p_column_bound_for_every_input [Nonempty n]
    (p : ℝ≥0∞) [Fact (1≤p)] (A : Matrix m n ℝ) (x : n → ℝ) :
    sourcePNorm p (A *ᵥ x)≤columnMaximum p A*sourcePNorm 1 x := by
  unfold sourcePNorm
  rw [actual_matrix_action_is_the_sum_of_its_input_scaled_columns]
  calc
    ‖∑ j,x j • (WithLp.toLp p (fun i => A i j) : PiLp p (fun _ : m => ℝ))‖
      ≤∑ j,‖x j • (WithLp.toLp p (fun i => A i j) : PiLp p (fun _ : m => ℝ))‖ := norm_sum_le _ _
    _=∑ j,|x j|*sourcePNorm p (fun i => A i j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_smul,Real.norm_eq_abs,sourcePNorm]
    _≤∑ j,|x j|*columnMaximum p A := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun j => sourcePNorm p (fun i => A i j)) (Finset.mem_univ j))
        (abs_nonneg _)
    _=columnMaximum p A*‖WithLp.toLp 1 x‖ := by
      rw [PiLp.norm_eq_of_L1,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.norm_eq_abs]
      ring

theorem actual_one_to_p_induced_norm_is_the_largest_actual_column_norm [Nonempty n]
    (p : ℝ≥0∞) [Fact (1≤p)] (A : Matrix m n ℝ) :
    ‖sourceMatrixMap 1 p A‖=columnMaximum p A := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (column_maximum_nonnegative p A)
    intro x
    have h:=actual_one_to_p_column_bound_for_every_input p A (WithLp.ofLp x)
    simpa only [sourcePNorm,WithLp.toLp_ofLp] using h
  · obtain ⟨j,hj,hmax⟩:=Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => sourcePNorm p (fun i => A i j))
    change columnMaximum p A=sourcePNorm p (fun i => A i j) at hmax
    let x : PiLp 1 (fun _ : n => ℝ) := WithLp.toLp 1 (Pi.single j 1)
    have hx : ‖x‖=1 := by simp [x,PiLp.norm_eq_of_L1]
    have he : sourceMatrixMap 1 p A x=WithLp.toLp p (fun i => A i j) := by
      ext i
      simp [x,sourceMatrixMap,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct]
    have h:=(sourceMatrixMap 1 p A).le_opNorm x
    rw [he,hx,mul_one] at h
    rw [hmax]
    exact h

theorem actual_conjugate_p_to_infinity_row_bound_for_every_input [Nonempty m]
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q] [Fact (1≤p)] [Fact (1≤q)]
    (A : Matrix m n ℝ) (x : n → ℝ) :
    sourcePNorm ∞ (A *ᵥ x)≤rowMaximum q A*sourcePNorm p x := by
  rw [actual_infinity_norm_formula]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (row_maximum_nonnegative q A) (actual_pnorm_nonnegative x))).mpr
  intro i
  rw [Real.norm_eq_abs]
  have h:=actual_all_conjugate_holder p q x (A i)
  rw [dotProduct_comm] at h
  change |A i ⬝ᵥ x|≤_
  calc
    |A i ⬝ᵥ x|≤sourcePNorm p x*sourcePNorm q (A i) := h
    _≤sourcePNorm p x*rowMaximum q A :=
      mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun i => sourcePNorm q (A i)) (Finset.mem_univ i))
        (actual_pnorm_nonnegative x)
    _=rowMaximum q A*sourcePNorm p x := mul_comm _ _

theorem actual_all_conjugate_p_to_infinity_induced_norm_is_the_largest_row_q_norm [Nonempty m]
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q] [Fact (1≤p)] [Fact (1≤q)]
    (A : Matrix m n ℝ) : ‖sourceMatrixMap p ∞ A‖=rowMaximum q A := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (row_maximum_nonnegative q A)
    intro x
    have h:=actual_conjugate_p_to_infinity_row_bound_for_every_input p q A (WithLp.ofLp x)
    simpa only [sourcePNorm,WithLp.toLp_ofLp] using h
  · obtain ⟨i,hi,hmax⟩:=Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => sourcePNorm q (A i))
    change rowMaximum q A=sourcePNorm q (A i) at hmax
    obtain ⟨x,hx,hdot⟩:=actual_all_conjugate_unit_attainer p q (A i)
    have hrow : sourcePNorm q (A i)≤‖A *ᵥ x‖ := by
      rw [←hdot]
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs,Matrix.mulVec] using norm_le_pi_norm (A *ᵥ x) i)
    have hb:=(sourceMatrixMap p ∞ A).le_opNorm (WithLp.toLp p x)
    change sourcePNorm ∞ (A *ᵥ x)≤‖sourceMatrixMap p ∞ A‖*sourcePNorm p x at hb
    rw [actual_infinity_norm_formula] at hb
    have hs:=mul_le_mul_of_nonneg_left hx (norm_nonneg (sourceMatrixMap p ∞ A))
    rw [mul_one] at hs
    rw [hmax]
    exact hrow.trans (hb.trans hs)

theorem actual_one_induced_norm_is_the_largest_absolute_column_sum [Nonempty n]
    (A : Matrix m n ℝ) :
    ‖sourceMatrixMap 1 1 A‖=
      Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ i,|A i j|) := by
  rw [actual_one_to_p_induced_norm_is_the_largest_actual_column_norm]
  unfold columnMaximum
  congr 1
  funext j
  exact actual_one_norm_formula _

theorem actual_infinity_induced_norm_is_the_largest_absolute_row_sum [Nonempty m]
    (A : Matrix m n ℝ) :
    ‖sourceMatrixMap ∞ ∞ A‖=
      Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j,|A i j|) := by
  rw [actual_all_conjugate_p_to_infinity_induced_norm_is_the_largest_row_q_norm ∞ 1]
  unfold rowMaximum
  congr 1
  funext i
  exact actual_one_norm_formula _

private theorem actual_gram_hermitian (A : Matrix m n ℝ) : (Aᵀ*A).IsHermitian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self A

theorem actual_Euclidean_image_norm_square_is_the_Gram_quadratic_form
    (A : Matrix m n ℝ) (x : n → ℝ) :
    ‖sourceMatrixMap 2 2 A (WithLp.toLp 2 x)‖^2=x ⬝ᵥ ((Aᵀ*A)*ᵥ x) := by
  have he : x ⬝ᵥ ((Aᵀ*A)*ᵥ x)=(A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  rw [he,←real_inner_self_eq_norm_sq]
  simp [sourceMatrixMap,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct]

theorem actual_largest_Gram_eigenvalue_is_nonnegative [Nonempty n]
    (A : Matrix m n ℝ) : 0≤actualLambdaMax (Aᵀ*A) (actual_gram_hermitian A) := by
  obtain ⟨x,hx,heigen,hform⟩:=actual_unit_eigenvector_attains_largest_eigenvalue
    (Aᵀ*A) (actual_gram_hermitian A)
  rw [←hform,←actual_Euclidean_image_norm_square_is_the_Gram_quadratic_form]
  exact sq_nonneg _

theorem actual_spectral_induced_norm_is_the_square_root_of_the_largest_Gram_eigenvalue [Nonempty n]
    (A : Matrix m n ℝ) :
    ‖sourceMatrixMap 2 2 A‖=Real.sqrt (actualLambdaMax (Aᵀ*A) (actual_gram_hermitian A)) := by
  let lambda : ℝ := actualLambdaMax (Aᵀ*A) (actual_gram_hermitian A)
  have hnonneg : 0≤lambda := actual_largest_Gram_eigenvalue_is_nonnegative A
  have hs : (Real.sqrt lambda)^2=lambda := Real.sq_sqrt hnonneg
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg lambda)
    intro x
    have hupper:=(actual_Euclidean_quadratic_form_is_squeezed_by_extreme_eigenvalues
      (Aᵀ*A) (actual_gram_hermitian A) (WithLp.ofLp x)).2
    rw [←actual_Euclidean_image_norm_square_is_the_Gram_quadratic_form] at hupper
    simp only [WithLp.toLp_ofLp] at hupper
    change ‖sourceMatrixMap 2 2 A x‖^2≤lambda*‖x‖^2 at hupper
    nlinarith [norm_nonneg (sourceMatrixMap 2 2 A x),norm_nonneg x,Real.sqrt_nonneg lambda]
  · obtain ⟨x,hx,heigen,hform⟩:=actual_unit_eigenvector_attains_largest_eigenvalue
      (Aᵀ*A) (actual_gram_hermitian A)
    have he : ‖sourceMatrixMap 2 2 A (WithLp.toLp 2 x)‖^2=lambda :=
      (actual_Euclidean_image_norm_square_is_the_Gram_quadratic_form A x).trans hform
    have hn : ‖sourceMatrixMap 2 2 A (WithLp.toLp 2 x)‖=Real.sqrt lambda := by
      nlinarith [norm_nonneg (sourceMatrixMap 2 2 A (WithLp.toLp 2 x)),Real.sqrt_nonneg lambda]
    have hb:=(sourceMatrixMap 2 2 A).le_opNorm (WithLp.toLp 2 x)
    rw [hx,mul_one,hn] at hb
    exact hb

end SafeLearning.CompleteFoundationsCommonMixedInducedNormFormulas32
