import SafeLearning.CompleteModulesDynamicLayerSoundness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFullyConnectedLayer
open CompleteModulesLipSDP CompleteModulesDynamicLayer CompleteModulesDynamicLayerSoundness
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]

def actualFullyConnectedCertificate (weight : Matrix O I ℝ)
    (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ) :
    Matrix (I ⊕ O) (I ⊕ O) ℝ :=
  Matrix.fromBlocks Xin (-weightᵀ*Matrix.diagonal multiplier)
    (-Matrix.diagonal multiplier*weight) ((2:ℝ) • Matrix.diagonal multiplier-Xout)

def actualStatelessCoordinateEmbedding : I ⊕ O → (Fin 0 ⊕ I) ⊕ O :=
  Sum.elim (fun coordinate => Sum.inl (Sum.inr coordinate)) Sum.inr

omit [Fintype I] in
theorem actual_fully_connected_two_block_matrix_is_stateless_source_specialization
    (weight : Matrix O I ℝ) (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ) :
    (actualLayerCertificate (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 weight 0 Xin Xout multiplier).submatrix
      actualStatelessCoordinateEmbedding actualStatelessCoordinateEmbedding=
        actualFullyConnectedCertificate weight Xin Xout multiplier := by
  ext row column
  cases row <;> cases column <;>
    simp [actualLayerCertificate,actualStatelessCoordinateEmbedding,actualFullyConnectedCertificate]

def actualStatelessCoordinateEquivalence : I ⊕ O ≃ (Fin 0 ⊕ I) ⊕ O where
  toFun := actualStatelessCoordinateEmbedding
  invFun := Sum.elim (Sum.elim Fin.elim0 Sum.inl) Sum.inr
  left_inv := by intro coordinate; cases coordinate <;> rfl
  right_inv := by
    intro coordinate
    rcases coordinate with (impossible | input) | output
    · exact Fin.elim0 impossible
    · rfl
    · rfl

omit [Fintype I] in
theorem actual_fully_connected_certificate_is_equivalent_to_stateless_source_lmi
    (weight : Matrix O I ℝ) (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ) :
    (actualLayerCertificate (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 weight 0 Xin Xout multiplier).PosSemidef ↔
      (actualFullyConnectedCertificate weight Xin Xout multiplier).PosSemidef := by
  have h := Matrix.posSemidef_submatrix_equiv
    (M := actualLayerCertificate (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 weight 0 Xin Xout multiplier)
    (actualStatelessCoordinateEquivalence (I := I) (O := O))
  change ((actualLayerCertificate (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 weight 0 Xin Xout multiplier).submatrix
    actualStatelessCoordinateEmbedding actualStatelessCoordinateEmbedding).PosSemidef ↔ _ at h
  rw [actual_fully_connected_two_block_matrix_is_stateless_source_specialization] at h
  exact h.symm

theorem actual_fully_connected_certificate_quadratic_identity
    (weight : Matrix O I ℝ) (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ)
    (input : I → ℝ) (output : O → ℝ) :
    quadratic (actualFullyConnectedCertificate weight Xin Xout multiplier) (Sum.elim input output)=
      quadratic Xin input-quadratic Xout output-
        ∑ coordinate,multiplier coordinate*(2*(weight*ᵥinput) coordinate*output coordinate-2*(output coordinate)^2) := by
  have hqc : (∑ coordinate,multiplier coordinate*(2*(weight*ᵥinput) coordinate*output coordinate-2*(output coordinate)^2))=
      2*(∑ coordinate,multiplier coordinate*output coordinate*(weight*ᵥinput) coordinate)-
        2*(∑ coordinate,multiplier coordinate*(output coordinate)^2) := by
    calc
      _ = ∑ coordinate,(2*(multiplier coordinate*output coordinate*(weight*ᵥinput) coordinate)-
          2*(multiplier coordinate*(output coordinate)^2)) := by
            apply Finset.sum_congr rfl
            intro coordinate _
            ring
      _ = _ := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
  rw [hqc]
  simp only [actualFullyConnectedCertificate,quadratic,Matrix.fromBlocks_mulVec,
    sumElim_dotProduct_sumElim,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Matrix.sub_mulVec,
    Matrix.neg_mulVec,Matrix.neg_mul,Matrix.smul_mulVec,dotProduct_add,dotProduct_sub,
    dotProduct_neg,← Matrix.mulVec_mulVec,dotProduct_smul]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_diagonal,dotProduct,smul_eq_mul,pow_two]
  simp only [mul_left_comm,mul_assoc]
  ring

def actualFullyConnectedOutput (weight : Matrix O I ℝ) (bias : O → ℝ)
    (activation : ℝ → ℝ) (input : I → ℝ) : O → ℝ :=
  fun coordinate => activation ((weight*ᵥinput) coordinate+bias coordinate)

theorem actual_fully_connected_layer_lmi_implies_weighted_incremental_gain
    (weight : Matrix O I ℝ) (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ)
    (bias : O → ℝ) (activation : ℝ → ℝ) (hactivation : slopeRestricted activation 0 1)
    (multiplier : O → ℝ) (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (actualFullyConnectedCertificate weight Xin Xout multiplier).PosSemidef)
    (first second : I → ℝ) :
    quadratic Xout (actualFullyConnectedOutput weight bias activation first-
      actualFullyConnectedOutput weight bias activation second) ≤ quadratic Xin (first-second) := by
  let output := actualFullyConnectedOutput weight bias activation first-
    actualFullyConnectedOutput weight bias activation second
  have hc : 0 ≤ quadratic (actualFullyConnectedCertificate weight Xin Xout multiplier)
      (Sum.elim (first-second) output) := by
    simpa only [quadratic,star_trivial] using
      hcertificate.dotProduct_mulVec_nonneg (Sum.elim (first-second) output)
  rw [actual_fully_connected_certificate_quadratic_identity] at hc
  have hqc : 0 ≤ ∑ coordinate,multiplier coordinate*
      (2*(weight*ᵥ(first-second)) coordinate*output coordinate-2*(output coordinate)^2) := by
    apply Finset.sum_nonneg
    intro coordinate _
    have h := scalar_slope_quadratic_constraint activation 0 1 hactivation
      ((weight*ᵥfirst) coordinate+bias coordinate) ((weight*ᵥsecond) coordinate+bias coordinate)
    have he : (weight*ᵥ(first-second)) coordinate=
        ((weight*ᵥfirst) coordinate+bias coordinate)-((weight*ᵥsecond) coordinate+bias coordinate) := by
      simp [Matrix.mulVec_sub]
    rw [he]
    apply mul_nonneg (hweight coordinate)
    change 0 ≤ 2*(((weight*ᵥfirst) coordinate+bias coordinate)-((weight*ᵥsecond) coordinate+bias coordinate))*
      (activation ((weight*ᵥfirst) coordinate+bias coordinate)-activation ((weight*ᵥsecond) coordinate+bias coordinate))-
      2*(activation ((weight*ᵥfirst) coordinate+bias coordinate)-activation ((weight*ᵥsecond) coordinate+bias coordinate))^2
    norm_num at h
    linarith
  change quadratic Xout output ≤ quadratic Xin (first-second)
  linarith

end SafeLearning.CompleteModulesFullyConnectedLayer
