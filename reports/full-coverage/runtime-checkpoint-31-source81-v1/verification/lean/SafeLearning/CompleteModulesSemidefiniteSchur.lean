import SafeLearning.CompleteModulesPseudoinverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesSemidefiniteSchur
open CompleteModulesPseudoinverse

variable {Left Right : Type*} [Fintype Left] [DecidableEq Left]
  [Fintype Right] [DecidableEq Right]

def actualSymmetricBlock (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ)
    (D : Matrix Right Right ℝ) : Matrix (Left ⊕ Right) (Left ⊕ Right) ℝ :=
  Matrix.fromBlocks A B Bᵀ D

def actualRangeCondition (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ) : Prop :=
  Set.range (fun x : Left→ℝ => Bᵀ *ᵥ x) ⊆ Set.range (fun y : Right→ℝ => D *ᵥ y)

omit [DecidableEq Left] [DecidableEq Right] in
theorem actual_block_psd_implies_the_off_diagonal_annihilates_the_corner_kernel
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ)
    (h : (actualSymmetricBlock A B D).PosSemidef)
    (y : Right→ℝ) (hy : D *ᵥ y=0) : B *ᵥ y=0 := by
  let v : Left ⊕ Right→ℝ := Sum.elim 0 y
  have hmv : actualSymmetricBlock A B D *ᵥ v=Sum.elim (B *ᵥ y) 0 := by
    rw [actualSymmetricBlock,Matrix.fromBlocks_mulVec]
    change Sum.elim (A*ᵥ 0+B*ᵥ y) (Bᵀ*ᵥ 0+D*ᵥ y)=_
    simp [hy]
  have hzero : star v ⬝ᵥ (actualSymmetricBlock A B D *ᵥ v)=0 := by
    rw [hmv]
    simp [v,dotProduct,Fintype.sum_sum_type]
  have hk := h.dotProduct_mulVec_zero_iff.mp hzero
  rw [hmv] at hk
  funext index
  have he:=congrFun hk (Sum.inl index)
  simpa using he

theorem actual_block_psd_implies_the_true_pseudoinverse_range_identity
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ)
    (hsymmetric : D.IsHermitian) (h : (actualSymmetricBlock A B D).PosSemidef) :
    B*actualPseudoinverse D hsymmetric*D=B := by
  have hker := actual_pseudoinverse_null_projection_has_image_in_the_actual_kernel D hsymmetric
  have hzero : B*(1-actualPseudoinverse D hsymmetric*D)=0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    have hy : D *ᵥ ((1-actualPseudoinverse D hsymmetric*D)*ᵥ y)=0 := by
      rw [Matrix.mulVec_mulVec,hker,Matrix.zero_mulVec]
    simpa only [←Matrix.mulVec_mulVec,Matrix.zero_mulVec] using
      actual_block_psd_implies_the_off_diagonal_annihilates_the_corner_kernel A B D h _ hy
  rw [Matrix.mul_sub,Matrix.mul_one,←Matrix.mul_assoc] at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem actual_true_range_condition_iff_pseudoinverse_identity
    (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ) (hsymmetric : D.IsHermitian) :
    actualRangeCondition B D ↔ B*actualPseudoinverse D hsymmetric*D=B := by
  let T:=actualPseudoinverse D hsymmetric
  have hdt : Dᵀ=D := by simpa using hsymmetric.eq
  have htt : Tᵀ=T := by simpa using (actual_pseudoinverse_is_symmetric D hsymmetric).eq
  have hgd : D*T*D=D :=
    (actual_pseudoinverse_satisfies_both_generalized_inverse_equations D hsymmetric).1
  constructor
  · intro hr
    have he : D*T*Bᵀ=Bᵀ := by
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      obtain ⟨y,hy⟩ := hr (mem_range_self x)
      change D*ᵥ y=Bᵀ*ᵥ x at hy
      rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,←hy,
        Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hgd]
    have ht:=congrArg Matrix.transpose he
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,hdt,htt,
      Matrix.mul_assoc] using ht
  · intro hr
    change B*T*D=B at hr
    have he : D*T*Bᵀ=Bᵀ := by
      have ht:=congrArg Matrix.transpose hr
      simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,hdt,htt,
        Matrix.mul_assoc] using ht
    rintro z ⟨x,rfl⟩
    refine ⟨T*ᵥ (Bᵀ*ᵥ x),?_⟩
    change D*ᵥ (T*ᵥ (Bᵀ*ᵥ x))=Bᵀ*ᵥ x
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,he]

omit [DecidableEq Left] [DecidableEq Right] in
theorem actual_block_diagonal_psd_iff_both_true_corners_are_psd
    (A : Matrix Left Left ℝ) (D : Matrix Right Right ℝ) :
    (Matrix.fromBlocks A (0 : Matrix Left Right ℝ) 0 D).PosSemidef ↔
      A.PosSemidef ∧ D.PosSemidef := by
  constructor
  · intro h
    have ha:=h.submatrix Sum.inl
    have hd:=h.submatrix Sum.inr
    change A.PosSemidef at ha
    change D.PosSemidef at hd
    exact ⟨ha,hd⟩
  · rintro ⟨ha,hd⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (ha.isHermitian.fromBlocks (by simp) hd.isHermitian)
    intro v
    have hl:=ha.dotProduct_mulVec_nonneg (v ∘ Sum.inl)
    have hr:=hd.dotProduct_mulVec_nonneg (v ∘ Sum.inr)
    simpa [Matrix.fromBlocks_mulVec,Function.comp_def,dotProduct,Fintype.sum_sum_type,
      star_trivial] using add_nonneg hl hr

def actualCompletionMap (B : Matrix Left Right ℝ) (T : Matrix Right Right ℝ) :
    Matrix (Left ⊕ Right) (Left ⊕ Right) ℝ :=
  Matrix.fromBlocks 1 0 (T*Bᵀ) 1

theorem actual_completion_map_is_invertible
    (B : Matrix Left Right ℝ) (T : Matrix Right Right ℝ) :
    IsUnit (actualCompletionMap B T) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Matrix.fromBlocks 1 0 (-(T*Bᵀ)) 1,?_⟩
  simp only [actualCompletionMap,Matrix.fromBlocks_multiply,Matrix.one_mul,
    Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,add_neg_cancel]
  ext (i|i) (j|j) <;> simp [Matrix.fromBlocks,Matrix.one_apply]

theorem actual_range_condition_gives_the_true_block_square_completion
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ)
    (hsymmetric : D.IsHermitian)
    (hrange : B*actualPseudoinverse D hsymmetric*D=B) :
    actualSymmetricBlock A B D=
      (actualCompletionMap B (actualPseudoinverse D hsymmetric))ᵀ*
        Matrix.fromBlocks (A-B*actualPseudoinverse D hsymmetric*Bᵀ) 0 0 D*
        actualCompletionMap B (actualPseudoinverse D hsymmetric) := by
  let T:=actualPseudoinverse D hsymmetric
  have hdt : Dᵀ=D := by simpa using hsymmetric.eq
  have htt : Tᵀ=T := by simpa using (actual_pseudoinverse_is_symmetric D hsymmetric).eq
  have hr : B*T*D=B := hrange
  have ht : D*(T*Bᵀ)=Bᵀ := by
    have he:=congrArg Matrix.transpose hr
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,hdt,htt,
      Matrix.mul_assoc] using he
  change Matrix.fromBlocks A B Bᵀ D=
    (Matrix.fromBlocks 1 0 (T*Bᵀ) 1)ᵀ*
      Matrix.fromBlocks (A-B*T*Bᵀ) 0 0 D*Matrix.fromBlocks 1 0 (T*Bᵀ) 1
  simp only [Matrix.fromBlocks_transpose,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.transpose_one,Matrix.transpose_zero,htt,Matrix.fromBlocks_multiply,
    Matrix.one_mul,Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  rw [hr,ht,←Matrix.mul_assoc B T Bᵀ,sub_add_cancel]

theorem actual_semidefinite_schur_iff_corner_range_and_pseudoinverse_remainder
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ)
    (hsymmetric : D.IsHermitian) :
    (actualSymmetricBlock A B D).PosSemidef ↔
      D.PosSemidef ∧ actualRangeCondition B D ∧
        (A-B*actualPseudoinverse D hsymmetric*Bᵀ).PosSemidef := by
  constructor
  · intro h
    have hd:=h.submatrix Sum.inr
    change D.PosSemidef at hd
    have hdp : D.PosSemidef := hd
    have hr:=actual_block_psd_implies_the_true_pseudoinverse_range_identity A B D hsymmetric h
    have he:=actual_range_condition_gives_the_true_block_square_completion A B D hsymmetric hr
    have hc : (Matrix.fromBlocks (A-B*actualPseudoinverse D hsymmetric*Bᵀ) 0 0 D).PosSemidef := by
      rw [he] at h
      exact (actual_completion_map_is_invertible B (actualPseudoinverse D hsymmetric)).posSemidef_star_left_conjugate_iff.mp
        (by simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using h)
    exact ⟨hdp,(actual_true_range_condition_iff_pseudoinverse_identity B D hsymmetric).mpr hr,
      (actual_block_diagonal_psd_iff_both_true_corners_are_psd _ _).mp hc |>.1⟩
  · rintro ⟨hd,hr,hs⟩
    rw [actual_range_condition_gives_the_true_block_square_completion A B D hsymmetric
      ((actual_true_range_condition_iff_pseudoinverse_identity B D hsymmetric).mp hr)]
    have hc := (actual_block_diagonal_psd_iff_both_true_corners_are_psd _ _).mpr ⟨hs,hd⟩
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hc.conjTranspose_mul_mul_same (actualCompletionMap B (actualPseudoinverse D hsymmetric))

end SafeLearning.CompleteModulesSemidefiniteSchur
