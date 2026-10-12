import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set Unitary
open scoped MatrixOrder
namespace SafeLearning.CompleteFoundationsGeneralizedSchur30
variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def actualSpectralAut (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :=
  Unitary.conjStarAlgAut ℝ _ hsymmetric.eigenvectorUnitary

def actualPseudoinverse (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    Matrix Index Index ℝ :=
  actualSpectralAut matrix hsymmetric (Matrix.diagonal (fun index =>
    (hsymmetric.eigenvalues index)⁻¹))

private theorem actual_matrix_is_its_true_spectral_conjugate
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix=actualSpectralAut matrix hsymmetric (Matrix.diagonal hsymmetric.eigenvalues) := by
  simpa [actualSpectralAut,Function.comp_def] using hsymmetric.spectral_theorem

private theorem actual_pseudoinverse_is_symmetric
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    (actualPseudoinverse matrix hsymmetric).IsHermitian := by
  unfold actualPseudoinverse actualSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ (Matrix.isHermitian_diagonal _)

private theorem actual_pseudoinverse_satisfies_both_generalized_inverse_equations
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric*matrix=matrix ∧
    actualPseudoinverse matrix hsymmetric*matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric := by
  let aut:=actualSpectralAut matrix hsymmetric
  let values:=hsymmetric.eigenvalues
  have hm : matrix=aut (Matrix.diagonal values) :=
    actual_matrix_is_its_true_spectral_conjugate matrix hsymmetric
  have hp : actualPseudoinverse matrix hsymmetric=
      aut (Matrix.diagonal (fun index => (values index)⁻¹)) := rfl
  rw [hp,hm]
  simp only [←map_mul,Matrix.diagonal_mul_diagonal]
  constructor
  · congr 2
    funext index
    by_cases hv : values index=0
    · simp [hv]
    · field_simp
  · congr 2
    funext index
    by_cases hv : values index=0
    · simp [hv]
    · field_simp

private theorem actual_pseudoinverse_commutes_with_the_matrix
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric*matrix := by
  let aut:=actualSpectralAut matrix hsymmetric
  let values:=hsymmetric.eigenvalues
  have hm : matrix=aut (Matrix.diagonal values) :=
    actual_matrix_is_its_true_spectral_conjugate matrix hsymmetric
  have hp : actualPseudoinverse matrix hsymmetric=
      aut (Matrix.diagonal (fun index => (values index)⁻¹)) := rfl
  rw [hp,hm]
  simp only [←map_mul,Matrix.diagonal_mul_diagonal]
  congr 2
  funext index
  exact mul_comm _ _

private theorem actual_pseudoinverse_satisfies_all_four_moore_penrose_equations
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric*matrix=matrix ∧
    actualPseudoinverse matrix hsymmetric*matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric ∧
    (matrix*actualPseudoinverse matrix hsymmetric)ᵀ=
      matrix*actualPseudoinverse matrix hsymmetric ∧
    (actualPseudoinverse matrix hsymmetric*matrix)ᵀ=
      actualPseudoinverse matrix hsymmetric*matrix := by
  obtain ⟨hm,hp⟩:=actual_pseudoinverse_satisfies_both_generalized_inverse_equations matrix hsymmetric
  have hmt : matrixᵀ=matrix := by simpa using hsymmetric.eq
  have hpt : (actualPseudoinverse matrix hsymmetric)ᵀ=actualPseudoinverse matrix hsymmetric := by
    simpa using (actual_pseudoinverse_is_symmetric matrix hsymmetric).eq
  refine ⟨hm,hp,?_,?_⟩
  · rw [Matrix.transpose_mul,hmt,hpt]
    exact (actual_pseudoinverse_commutes_with_the_matrix matrix hsymmetric).symm
  · rw [Matrix.transpose_mul,hmt,hpt]
    exact actual_pseudoinverse_commutes_with_the_matrix matrix hsymmetric

private theorem actual_zero_matrix_pseudoinverse_is_zero :
    actualPseudoinverse (0 : Matrix Index Index ℝ) (Matrix.isHermitian_zero)=0 := by
  have h:=actual_pseudoinverse_satisfies_both_generalized_inverse_equations
    (0 : Matrix Index Index ℝ) Matrix.isHermitian_zero
  simpa using h.2.symm

private theorem actual_pseudoinverse_null_projection_has_image_in_the_actual_kernel
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*(1-actualPseudoinverse matrix hsymmetric*matrix)=0 := by
  rw [Matrix.mul_sub,Matrix.mul_one,←Matrix.mul_assoc,
    (actual_pseudoinverse_satisfies_both_generalized_inverse_equations matrix hsymmetric).1,
    sub_self]


variable {Left Right : Type*} [Fintype Left] [DecidableEq Left]
  [Fintype Right] [DecidableEq Right]

def actualSymmetricBlock (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ)
    (D : Matrix Right Right ℝ) : Matrix (Left ⊕ Right) (Left ⊕ Right) ℝ :=
  Matrix.fromBlocks A B Bᵀ D

def actualRangeCondition (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ) : Prop :=
  Set.range (fun x : Left→ℝ => Bᵀ *ᵥ x) ⊆ Set.range (fun y : Right→ℝ => D *ᵥ y)

omit [DecidableEq Left] [DecidableEq Right] in
private theorem actual_block_psd_implies_the_off_diagonal_annihilates_the_corner_kernel
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

private theorem actual_block_psd_implies_the_true_pseudoinverse_range_identity
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

private theorem actual_true_range_condition_iff_pseudoinverse_identity
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
private theorem actual_block_diagonal_psd_iff_both_true_corners_are_psd
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

private theorem actual_completion_map_is_invertible
    (B : Matrix Left Right ℝ) (T : Matrix Right Right ℝ) :
    IsUnit (actualCompletionMap B T) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Matrix.fromBlocks 1 0 (-(T*Bᵀ)) 1,?_⟩
  simp only [actualCompletionMap,Matrix.fromBlocks_multiply,Matrix.one_mul,
    Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,add_neg_cancel]
  ext (i|i) (j|j) <;> simp [Matrix.fromBlocks,Matrix.one_apply]

private theorem actual_range_condition_gives_the_true_block_square_completion
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

private theorem actual_semidefinite_schur_iff_corner_range_and_pseudoinverse_remainder
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

theorem actual_symmetric_pseudoinverse_full_source_identities
    (C : Matrix Right Right ℝ) (hC : C.IsHermitian) :
    (actualPseudoinverse C hC)ᵀ = actualPseudoinverse C hC ∧
      C * actualPseudoinverse C hC = actualPseudoinverse C hC * C ∧
      C * actualPseudoinverse C hC * C = C ∧
      actualPseudoinverse C hC * C * actualPseudoinverse C hC = actualPseudoinverse C hC := by
  obtain ⟨h1,h2⟩ := actual_pseudoinverse_satisfies_both_generalized_inverse_equations C hC
  exact ⟨by simpa using (actual_pseudoinverse_is_symmetric C hC).eq,
    actual_pseudoinverse_commutes_with_the_matrix C hC,h1,h2⟩

theorem actual_product_is_symmetric_idempotent_true_range_projection
    (C : Matrix Right Right ℝ) (hC : C.IsHermitian) :
    let P := C * actualPseudoinverse C hC
    Pᵀ = P ∧ P * P = P ∧
      Set.range (fun x : Right → ℝ => P *ᵥ x) = Set.range (fun x => C *ᵥ x) := by
  dsimp
  obtain ⟨h1,h2,h3,h4⟩ := actual_pseudoinverse_satisfies_all_four_moore_penrose_equations C hC
  refine ⟨h3,?_,?_⟩
  · calc
      (C*actualPseudoinverse C hC)*(C*actualPseudoinverse C hC) =
          (C*actualPseudoinverse C hC*C)*actualPseudoinverse C hC := by noncomm_ring
      _ = C*actualPseudoinverse C hC := by rw [h1]
  · ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨actualPseudoinverse C hC *ᵥ x,Matrix.mulVec_mulVec _ _ _⟩
    · rintro ⟨x,rfl⟩
      refine ⟨C *ᵥ x,?_⟩
      change (C*actualPseudoinverse C hC)*ᵥ (C*ᵥ x)=C*ᵥ x
      rw [Matrix.mulVec_mulVec,h1]

theorem actual_range_condition_iff_printed_zero_matrix
    (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ) (hC : C.IsHermitian) :
    actualRangeCondition B C ↔ (1-C*actualPseudoinverse C hC)*Bᵀ=0 := by
  rw [actual_true_range_condition_iff_pseudoinverse_identity B C hC]
  have ht : (actualPseudoinverse C hC)ᵀ=actualPseudoinverse C hC := by
    simpa using (actual_pseudoinverse_is_symmetric C hC).eq
  have hc : Cᵀ=C := by simpa using hC.eq
  constructor
  · intro h
    have he := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,ht,hc]at he
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,he,sub_self]
  · intro h
    rw [Matrix.sub_mul,Matrix.one_mul]at h
    have he : C*actualPseudoinverse C hC*Bᵀ=Bᵀ := (sub_eq_zero.mp h).symm
    have hs := congrArg Matrix.transpose he
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,ht,hc,Matrix.mul_assoc]using hs

theorem actual_entire_printed_generalized_Schur_criterion
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ)
    (hC : C.IsHermitian) :
    (Matrix.fromBlocks A B Bᵀ C).PosSemidef ↔ C.PosSemidef ∧
      (1-C*actualPseudoinverse C hC)*Bᵀ=0 ∧
      (A-B*actualPseudoinverse C hC*Bᵀ).PosSemidef := by
  simpa only [actualSymmetricBlock,actual_range_condition_iff_printed_zero_matrix B C hC]using
    actual_semidefinite_schur_iff_corner_range_and_pseudoinverse_remainder A B C hC

theorem actual_printed_choice_completes_the_full_quadratic
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ)
    (hC : C.IsHermitian) (hr : (1-C*actualPseudoinverse C hC)*Bᵀ=0)
    (x : Left → ℝ) (w : Right → ℝ) :
    let y := -(actualPseudoinverse C hC *ᵥ (Bᵀ *ᵥ x))+w
    Sum.elim x y ⬝ᵥ (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim x y) =
      x ⬝ᵥ ((A-B*actualPseudoinverse C hC*Bᵀ)*ᵥ x)+w ⬝ᵥ (C*ᵥ w) := by
  have hi := (actual_true_range_condition_iff_pseudoinverse_identity B C hC).mp
    ((actual_range_condition_iff_printed_zero_matrix B C hC).mpr hr)
  have he := actual_range_condition_gives_the_true_block_square_completion A B C hC hi
  dsimp
  change _ = _
  rw [←show actualSymmetricBlock A B C=Matrix.fromBlocks A B Bᵀ C from rfl,he]
  have hv : actualCompletionMap B (actualPseudoinverse C hC) *ᵥ
      Sum.elim x (-(actualPseudoinverse C hC *ᵥ (Bᵀ *ᵥ x))+w) = Sum.elim x w := by
    simp [actualCompletionMap,Matrix.fromBlocks_mulVec,Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
  rw [hv,←Matrix.mulVec_mulVec,hv,Matrix.fromBlocks_mulVec,
    sumElim_dotProduct_sumElim]
  simp

theorem actual_not_in_range_constructs_null_vector_and_nonzero_pairing
    (C : Matrix Right Right ℝ) (hC : C.IsHermitian) (q : Right → ℝ)
    (hq : q ∉ Set.range (fun y : Right → ℝ => C *ᵥ y)) :
    ∃ y : Right → ℝ,C *ᵥ y=0 ∧ y ⬝ᵥ q≠0 := by
  let T := actualPseudoinverse C hC
  let P := C*T
  let y := q-P*ᵥ q
  have hCpC : C*T*C=C := (actual_pseudoinverse_satisfies_both_generalized_inverse_equations C hC).1
  have hcomm : C*T=T*C := actual_pseudoinverse_commutes_with_the_matrix C hC
  have hCp : C*P=C := by
    change C*(C*T)=C
    rw [hcomm,←Matrix.mul_assoc,hCpC]
  have hP := actual_product_is_symmetric_idempotent_true_range_projection C hC
  have ht : Pᵀ=P := hP.1
  have hp2 : P*P=P := hP.2.1
  have hcy : C*ᵥ y=0 := by
    dsimp[y]
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hCp,sub_self]
  have hpy : P*ᵥ y=0 := by
    dsimp[y]
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hp2,sub_self]
  have hyn : y≠0 := by
    intro hy
    have he : P*ᵥ q=q := (sub_eq_zero.mp hy).symm
    apply hq
    refine ⟨T*ᵥ q,?_⟩
    change C*ᵥ (T*ᵥ q)=q
    rw [Matrix.mulVec_mulVec]
    exact he
  have hpq : y ⬝ᵥ (P*ᵥ q)=0 := by
    rw [←ht,Matrix.dotProduct_transpose_mulVec,hpy,dotProduct_zero]
  have hself : y ⬝ᵥ q=y ⬝ᵥ y := by
    calc
      y ⬝ᵥ q = y ⬝ᵥ (q-P*ᵥ q)+y ⬝ᵥ (P*ᵥ q) := by rw [dotProduct_sub];ring
      _ = y ⬝ᵥ y := by change y ⬝ᵥ y + y ⬝ᵥ (P*ᵥ q) = _;rw [hpq,add_zero]
  refine ⟨y,hcy,?_⟩
  rw [hself]
  exact fun hz => hyn (dotProduct_self_eq_zero.mp hz)

theorem actual_failed_range_condition_gives_the_printed_null_pair
    (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ) (hC : C.IsHermitian)
    (hr : (1-C*actualPseudoinverse C hC)*Bᵀ≠0) :
    ∃ (x : Left → ℝ) (y : Right → ℝ),C*ᵥ y=0 ∧ y ⬝ᵥ (Bᵀ*ᵥ x)≠0 := by
  have hn : ¬actualRangeCondition B C := by
    intro h
    exact hr ((actual_range_condition_iff_printed_zero_matrix B C hC).mp h)
  change ¬Set.range (fun x : Left → ℝ => Bᵀ*ᵥ x) ⊆ Set.range (fun y => C*ᵥ y)at hn
  obtain ⟨q,⟨x,rfl⟩,hq⟩ := Set.not_subset.mp hn
  obtain ⟨y,hcy,hpair⟩ := actual_not_in_range_constructs_null_vector_and_nonzero_pairing C hC _ hq
  exact ⟨x,y,hcy,hpair⟩

theorem actual_nonzero_null_pair_gives_a_genuine_negative_scalar_witness
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ)
    (x : Left → ℝ) (y : Right → ℝ) (hy : C*ᵥ y=0) (hc : y ⬝ᵥ (Bᵀ*ᵥ x)≠0) :
    ∃ s : ℝ,Sum.elim x (s • y) ⬝ᵥ
      (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim x (s • y))<0 := by
  have hcross : y ⬝ᵥ (Bᵀ*ᵥ x)=x ⬝ᵥ (B*ᵥ y) := by
    rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
  rw [hcross]at hc
  let a := x ⬝ᵥ (A*ᵥ x)
  let b := x ⬝ᵥ (B*ᵥ y)
  let s := -(a+1)/(2*b)
  refine ⟨s,?_⟩
  rw [Matrix.fromBlocks_mulVec,sumElim_dotProduct_sumElim,dotProduct_add,dotProduct_add]
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,Matrix.mulVec_smul,hy,
    smul_zero,dotProduct_zero,dotProduct_smul,smul_dotProduct,smul_eq_mul]
  rw [hcross]
  change a+s*b+(s*b+0)<0
  have hb : b≠0 := hc
  have he : a+s*b+s*b+0= -1 := by
    dsimp[s]
    field_simp [hb]
    ring
  rw [←add_assoc,he]
  norm_num

def actualSingularZeroCorner (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,0]

theorem actual_zero_corner_PSD_iff_and_actual_negative_witness (a b : ℝ) :
    ((actualSingularZeroCorner a b).PosSemidef ↔ 0≤a ∧ b=0) ∧
      (b≠0 → (![1,-(a+1)/(2*b)] : Fin 2 → ℝ) ⬝ᵥ
        (actualSingularZeroCorner a b *ᵥ ![1,-(a+1)/(2*b)])= -1) := by
  have hq (t : ℝ) : (![1,t] : Fin 2 → ℝ) ⬝ᵥ
      (actualSingularZeroCorner a b *ᵥ ![1,t])=a+2*b*t := by
    simp [actualSingularZeroCorner,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  have hneg (hb : b≠0) : (![1,-(a+1)/(2*b)] : Fin 2 → ℝ) ⬝ᵥ
      (actualSingularZeroCorner a b *ᵥ ![1,-(a+1)/(2*b)])= -1 := by
    rw [hq]
    field_simp
    ring
  refine ⟨?_,hneg⟩
  constructor
  · intro h
    have ha := h.dotProduct_mulVec_nonneg (![1,0] : Fin 2 → ℝ)
    simp only [star_trivial,hq,mul_zero,add_zero]at ha
    refine ⟨ha,?_⟩
    by_contra hb
    have hn := h.dotProduct_mulVec_nonneg (![1,-(a+1)/(2*b)] : Fin 2 → ℝ)
    rw [star_trivial,hneg hb]at hn
    norm_num at hn
  · rintro ⟨ha,rfl⟩
    have he : actualSingularZeroCorner a 0=Matrix.diagonal (![a,0] : Fin 2 → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [actualSingularZeroCorner]
    rw [he,Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp_all


theorem actual_source_range_condition_derives_printed_off_diagonal_identity
    (B : Matrix Left Right ℝ) (C : Matrix Right Right ℝ) (hC : C.IsHermitian)
    (hr : (1-C*actualPseudoinverse C hC)*Bᵀ=0) :
    B*actualPseudoinverse C hC*C=B := by
  exact (actual_true_range_condition_iff_pseudoinverse_identity B C hC).mp
    ((actual_range_condition_iff_printed_zero_matrix B C hC).mpr hr)

theorem actual_projection_residual_is_orthogonal_to_the_entire_true_range
    (C : Matrix Right Right ℝ) (hC : C.IsHermitian) (q z : Right → ℝ)
    (hz : z ∈ Set.range (fun u : Right → ℝ => C*ᵥ u)) :
    (q-(C*actualPseudoinverse C hC)*ᵥ q) ⬝ᵥ z=0 := by
  obtain ⟨u,rfl⟩ := hz
  have hc : Cᵀ=C := by simpa using hC.eq
  have hcomm := actual_pseudoinverse_commutes_with_the_matrix C hC
  have htr := (actual_pseudoinverse_satisfies_both_generalized_inverse_equations C hC).1
  have hprod : C*(C*actualPseudoinverse C hC)=C := by
    rw [hcomm,←Matrix.mul_assoc,htr]
  have hzero : C*ᵥ (q-(C*actualPseudoinverse C hC)*ᵥ q)=0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hprod,sub_self]
  change (q-(C*actualPseudoinverse C hC)*ᵥ q) ⬝ᵥ (C*ᵥ u)=0
  calc
    (q-(C*actualPseudoinverse C hC)*ᵥ q) ⬝ᵥ (C*ᵥ u) =
        (q-(C*actualPseudoinverse C hC)*ᵥ q) ⬝ᵥ (Cᵀ*ᵥ u) := by rw [hc]
    _ = u ⬝ᵥ (C*ᵥ (q-(C*actualPseudoinverse C hC)*ᵥ q)) :=
      Matrix.dotProduct_transpose_mulVec _ _ _
    _ = 0 := by rw [hzero,dotProduct_zero]

theorem actual_zero_corner_has_printed_naive_remainder_for_every_a_b (a b : ℝ) :
    ((!![a] : Matrix (Fin 1) (Fin 1) ℝ)-
      (!![b] : Matrix (Fin 1) (Fin 1) ℝ)*
        actualPseudoinverse (0 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.isHermitian_zero*
        (!![b] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) = !![a] := by
  rw [actual_zero_matrix_pseudoinverse_is_zero,Matrix.mul_zero,Matrix.zero_mul,sub_zero]

end SafeLearning.CompleteFoundationsGeneralizedSchur30

