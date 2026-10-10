import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesRidgeResidualBounds
open CompleteModulesMatrixGP

theorem actual_psd_ridge_inverse_error_is_bounded_by_the_true_residual
    {I : Type*} [Fintype I] [DecidableEq I]
    (gram : Matrix I I ℝ) (hgram : gram.PosSemidef)
    (regularizer : ℝ) (hreg : 0 < regularizer) (rhs approximate : I → ℝ) :
    regularizer^2 * (∑ i, (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i)^2) ≤
      ∑ i, (rhs i - (ridgeMatrix gram regularizer *ᵥ approximate) i)^2 := by
  let A := ridgeMatrix gram regularizer
  let error := A⁻¹ *ᵥ rhs - approximate
  let residual := rhs - A *ᵥ approximate
  have hpd : A.PosDef := hgram.posDef_add (Matrix.PosDef.one.smul hreg)
  have hnormal : A *ᵥ (A⁻¹ *ᵥ rhs) = rhs := by
    rw [Matrix.mulVec_mulVec, A.mul_nonsing_inv hpd.det_pos.ne', Matrix.one_mulVec]
  have herror : A *ᵥ error = residual := by
    dsimp only [error, residual]
    rw [Matrix.mulVec_sub, hnormal]
  let S := ∑ i, (error i)^2
  let R := ∑ i, (residual i)^2
  let Q := error ⬝ᵥ residual
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hquadratic : regularizer*S ≤ Q := by
    have hg := hgram.dotProduct_mulVec_nonneg error
    simp only [star_trivial] at hg
    have h : error ⬝ᵥ (A *ᵥ error) =
        error ⬝ᵥ (gram *ᵥ error) + regularizer*S := by
      simp only [A,ridgeMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
        dotProduct_add,dotProduct_smul,smul_eq_mul]
      congr 1
      dsimp [S,dotProduct]
      simp only [pow_two]
    rw [herror] at h
    dsimp only [Q]
    linarith
  have hQ : 0 ≤ Q := le_trans (mul_nonneg hreg.le hS) hquadratic
  have hc : Q^2 ≤ S*R := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ error residual
  have hm : (regularizer*S)^2 ≤ Q^2 := by nlinarith
  have hsquared : regularizer^2*S ≤ R := by
    rcases eq_or_lt_of_le hS with hz | hp
    · rw [← hz]
      simpa using hR
    · have hmul : S*(regularizer^2*S) ≤ S*R := by nlinarith
      exact (mul_le_mul_left hp).mp hmul
  exact hsquared

theorem actual_eleven_dimensional_ridge_inverse_error_bound_from_component_residuals
    (gram : Matrix (Fin 11) (Fin 11) ℝ) (hgram : gram.PosSemidef)
    (regularizer tolerance : ℝ) (hreg : 0 < regularizer) (htol : 0 ≤ tolerance)
    (rhs approximate : Fin 11 → ℝ)
    (hresidual : ∀ i, |rhs i - (ridgeMatrix gram regularizer *ᵥ approximate) i| ≤ tolerance) :
    ∀ i, |((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i| ≤
      4*tolerance/regularizer := by
  have htotal := actual_psd_ridge_inverse_error_is_bounded_by_the_true_residual
    gram hgram regularizer hreg rhs approximate
  have hr : (∑ i, (rhs i - (ridgeMatrix gram regularizer *ᵥ approximate) i)^2) ≤
      11*tolerance^2 := by
    calc
      _ ≤ ∑ _i : Fin 11, tolerance^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hresidual i
        have hn := abs_nonneg (rhs i - (ridgeMatrix gram regularizer *ᵥ approximate) i)
        nlinarith [sq_abs (rhs i - (ridgeMatrix gram regularizer *ᵥ approximate) i)]
      _ = _ := by simp
  intro i
  have hi : (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i)^2 ≤
      ∑ j, (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) j - approximate j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hb := mul_le_mul_of_nonneg_left hi (sq_nonneg regularizer)
  have hs : regularizer^2 * (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i)^2 ≤
      11*tolerance^2 := le_trans hb (le_trans htotal hr)
  have hn := abs_nonneg (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i)
  have hle : regularizer * |((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i| ≤
      4*tolerance := by
    nlinarith [sq_abs (((ridgeMatrix gram regularizer)⁻¹ *ᵥ rhs) i - approximate i)]
  apply (le_div_iff₀ hreg).2
  simpa only [mul_comm] using hle

end SafeLearning.CompleteModulesRidgeResidualBounds
