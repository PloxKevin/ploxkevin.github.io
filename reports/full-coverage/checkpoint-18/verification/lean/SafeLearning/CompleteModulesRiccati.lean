import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesRiccati

variable {State Input Output : Type*} [Fintype State] [Fintype Input] [Fintype Output]
  [DecidableEq State] [DecidableEq Input] [DecidableEq Output]

omit [DecidableEq State] in
theorem actual_negative_block_schur_equivalence
    (first : Matrix State State ℝ) (cross : Matrix State Input ℝ)
    (positiveCorner : Matrix Input Input ℝ) (hcorner : positiveCorner.PosDef) :
    (-(Matrix.fromBlocks first cross crossᵀ (-positiveCorner))).PosSemidef ↔
      (-(first+cross*positiveCorner⁻¹*crossᵀ)).PosSemidef := by
  let := hcorner.isUnit.invertible
  have hblock : -(Matrix.fromBlocks first cross crossᵀ (-positiveCorner))=
      Matrix.fromBlocks (-first) (-cross) (-cross)ᴴ positiveCorner := by
    ext row column
    cases row <;> cases column <;> simp [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hblock,Matrix.PosDef.fromBlocks₂₂ _ _ hcorner]
  have he : -first-(-cross)*positiveCorner⁻¹*(-cross)ᴴ=
      -(first+cross*positiveCorner⁻¹*crossᵀ) := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_neg,
      Matrix.neg_mul,Matrix.mul_neg]
    abel
  rw [he]

omit [Fintype State] [Fintype Output] [DecidableEq State] [DecidableEq Output] in
theorem actual_negative_corner_inverse_has_the_source_sign
    (positiveCorner : Matrix Input Input ℝ) (hcorner : positiveCorner.PosDef) :
    (-positiveCorner)⁻¹= -positiveCorner⁻¹ := by
  let : Invertible (-1 : ℝ) := invertibleOfNonzero (by norm_num)
  simpa using Matrix.inv_smul (A:=positiveCorner) (-1:ℝ)
    (positiveCorner.isUnit_iff_isUnit_det.mp hcorner.isUnit)

def actualRiccatiRemainder (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) : Matrix State State ℝ :=
  Aᵀ*P+P*A+Cᵀ*C+(P*B+Cᵀ*D)*
    (squaredGain • (1 : Matrix Input Input ℝ)-Dᵀ*D)⁻¹*(Bᵀ*P+Dᵀ*C)

def actualTwoBlockBoundedReal (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) : Matrix (State⊕Input) (State⊕Input) ℝ :=
  Matrix.fromBlocks (Aᵀ*P+P*A+Cᵀ*C) (P*B+Cᵀ*D) (Bᵀ*P+Dᵀ*C)
    (Dᵀ*D-squaredGain • (1 : Matrix Input Input ℝ))

omit [DecidableEq State] [DecidableEq Output] in
theorem actual_riccati_remainder_iff_literal_two_block_lmi
    (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ)
    (hP : P.IsHermitian)
    (hcorner : (squaredGain • (1 : Matrix Input Input ℝ)-Dᵀ*D).PosDef) :
    (-(actualTwoBlockBoundedReal A P B C D squaredGain)).PosSemidef ↔
      (-(actualRiccatiRemainder A P B C D squaredGain)).PosSemidef := by
  have hPt : Pᵀ=P := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eq
  have hcross : (P*B+Cᵀ*D)ᵀ=Bᵀ*P+Dᵀ*C := by simp [Matrix.transpose_mul,hPt]
  have hcornerSign : Dᵀ*D-squaredGain • (1 : Matrix Input Input ℝ)=
      -(squaredGain • (1 : Matrix Input Input ℝ)-Dᵀ*D) := by abel
  simpa only [actualTwoBlockBoundedReal,actualRiccatiRemainder,hcross,hcornerSign]
    using actual_negative_block_schur_equivalence (Aᵀ*P+P*A+Cᵀ*C)
      (P*B+Cᵀ*D) (squaredGain • (1 : Matrix Input Input ℝ)-Dᵀ*D) hcorner


def actualThreeBlockBoundedReal (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) :
    Matrix ((State⊕Input)⊕Output) ((State⊕Input)⊕Output) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks (Aᵀ*P+P*A) (P*B) (Bᵀ*P)
    (-squaredGain • (1 : Matrix Input Input ℝ)))
    (Matrix.fromRows Cᵀ Dᵀ) (Matrix.fromCols C D) (-(1 : Matrix Output Output ℝ))

omit [Fintype Input] [DecidableEq State] in
theorem actual_output_schur_remainder_is_the_literal_two_block_lmi
    (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) :
    Matrix.fromBlocks (Aᵀ*P+P*A) (P*B) (Bᵀ*P)
      (-squaredGain • (1 : Matrix Input Input ℝ))+
      (Matrix.fromRows Cᵀ Dᵀ)*(1 : Matrix Output Output ℝ)⁻¹*(Matrix.fromRows Cᵀ Dᵀ)ᵀ=
      actualTwoBlockBoundedReal A P B C D squaredGain := by
  simp only [inv_one,Matrix.mul_one,Matrix.transpose_fromRows,Matrix.transpose_transpose,
    Matrix.fromRows_mul_fromCols]
  ext row column
  cases row <;> cases column <;> simp [actualTwoBlockBoundedReal]
  all_goals ring

omit [DecidableEq State] in
theorem actual_literal_three_block_lmi_iff_literal_two_block_lmi
    (A P : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) :
    (-(actualThreeBlockBoundedReal A P B C D squaredGain)).PosSemidef ↔
      (-(actualTwoBlockBoundedReal A P B C D squaredGain)).PosSemidef := by
  have he : (Matrix.fromRows Cᵀ Dᵀ)ᵀ=Matrix.fromCols C D := by
    rw [Matrix.transpose_fromRows,Matrix.transpose_transpose,Matrix.transpose_transpose]
  unfold actualThreeBlockBoundedReal
  rw [←he,actual_negative_block_schur_equivalence _ _ _ Matrix.PosDef.one,
    actual_output_schur_remainder_is_the_literal_two_block_lmi]

omit [Fintype Input] [Fintype Output] in
theorem actual_three_block_lmi_is_jointly_affine_in_storage_output_feedthrough_and_squared_gain
    (A : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (firstP secondP : Matrix State State ℝ) (firstC secondC : Matrix Output State ℝ)
    (firstD secondD : Matrix Output Input ℝ) (firstGain secondGain left right : ℝ)
    (hsum : left+right=1) :
    actualThreeBlockBoundedReal A (left • firstP+right • secondP) B
      (left • firstC+right • secondC) (left • firstD+right • secondD)
      (left*firstGain+right*secondGain)=
    left • actualThreeBlockBoundedReal A firstP B firstC firstD firstGain+
      right • actualThreeBlockBoundedReal A secondP B secondC secondD secondGain := by
  ext row column
  rcases row with (row|row)|row <;> rcases column with (column|column)|column <;>
    simp [actualThreeBlockBoundedReal,Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.add_apply,
      Matrix.smul_apply,Matrix.transpose_apply] <;> try (first | ring1 | ring_nf)
  all_goals linear_combination (1 : Matrix Output Output ℝ) row column*hsum


omit [Fintype Input] [DecidableEq State] [DecidableEq Output] in
theorem actual_two_block_lmi_is_affine_in_storage_with_system_fixed
    (A : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ)
    (firstP secondP : Matrix State State ℝ) (left right : ℝ) (hsum : left+right=1) :
    actualTwoBlockBoundedReal A (left • firstP+right • secondP) B C D squaredGain=
      left • actualTwoBlockBoundedReal A firstP B C D squaredGain+
        right • actualTwoBlockBoundedReal A secondP B C D squaredGain := by
  ext row column
  cases row with
  | inl row =>
    cases column with
    | inl column =>
      simp [actualTwoBlockBoundedReal,Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,
        Matrix.mul_smul,Matrix.add_apply,Matrix.smul_apply]
      linear_combination -(Cᵀ*C) row column*hsum
    | inr column =>
      simp [actualTwoBlockBoundedReal,Matrix.add_mul,Matrix.smul_mul,Matrix.add_apply,Matrix.smul_apply]
      linear_combination -(Cᵀ*D) row column*hsum
  | inr row =>
    cases column with
    | inl column =>
      simp [actualTwoBlockBoundedReal,Matrix.mul_add,Matrix.mul_smul,Matrix.add_apply,Matrix.smul_apply]
      linear_combination -(Dᵀ*C) row column*hsum
    | inr column =>
      simp [actualTwoBlockBoundedReal,Matrix.add_apply,Matrix.smul_apply]
      linear_combination -((Dᵀ*D) row column-squaredGain*(1 : Matrix Input Input ℝ) row column)*hsum

omit [DecidableEq State] [DecidableEq Output] in
theorem actual_riccati_remainder_has_the_true_quadratic_storage_second_difference
    (A P direction : Matrix State State ℝ) (B : Matrix State Input ℝ)
    (C : Matrix Output State ℝ) (D : Matrix Output Input ℝ) (squaredGain : ℝ) :
    actualRiccatiRemainder A (P+direction) B C D squaredGain+
      actualRiccatiRemainder A (P-direction) B C D squaredGain=
    (2 : ℝ) • actualRiccatiRemainder A P B C D squaredGain+
      (2 : ℝ) • (direction*B*(squaredGain • (1 : Matrix Input Input ℝ)-Dᵀ*D)⁻¹*(Bᵀ*direction)) := by
  simp only [two_smul,actualRiccatiRemainder,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sub,Matrix.sub_mul]
  abel

end SafeLearning.CompleteModulesRiccati
