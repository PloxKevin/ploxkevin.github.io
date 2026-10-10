import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsQuadraticForms

def realQuadratic {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

theorem real_quadratic_double_sum {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : realQuadratic A x=∑ i,∑ j,A i j*x i*x j := by
  simp only [realQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem real_quadratic_transpose {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : realQuadratic A.transpose x=realQuadratic A x := by
  unfold realQuadratic
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,Matrix.transpose_transpose,dotProduct_comm]

def symmetricPart {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1/2 : ℝ) • (A+A.transpose)

theorem real_quadratic_only_symmetric_part {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : realQuadratic (symmetricPart A) x=realQuadratic A x := by
  unfold symmetricPart realQuadratic
  rw [Matrix.smul_mulVec,Matrix.add_mulVec,dotProduct_smul,dotProduct_add]
  change (1/2 : ℝ)*(realQuadratic A x+realQuadratic A.transpose x)=realQuadratic A x
  rw [real_quadratic_transpose]
  ring

theorem symmetric_part_is_symmetric {n : Type*} (A : Matrix n n ℝ) :
    (symmetricPart A).transpose=symmetricPart A := by
  simp [symmetricPart,Matrix.transpose_add,add_comm]

def planeMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,c]

theorem plane_actual_form (a b c : ℝ) (x : Fin 2 → ℝ) :
    realQuadratic (planeMatrix a b c) x=a*(x 0)^2+2*b*x 0*x 1+c*(x 1)^2 := by
  simp [realQuadratic,planeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem plane_completed_square (a b c : ℝ) (ha : a≠0) (x : Fin 2 → ℝ) :
    realQuadratic (planeMatrix a b c) x=
      a*(x 0+(b/a)*x 1)^2+(c-b^2/a)*(x 1)^2 := by
  rw [plane_actual_form]
  field_simp [ha]
  ring

theorem plane_actual_determinant (a b c : ℝ) : (planeMatrix a b c).det=a*c-b^2 := by
  simp [planeMatrix,Matrix.det_fin_two]
  ring

theorem plane_pd_criterion (a b c : ℝ) :
    (planeMatrix a b c).PosDef ↔ 0<a ∧ 0<a*c-b^2 := by
  constructor
  · intro h
    have he0 : (![1,0] : Fin 2 → ℝ)≠0 := by
      intro hh
      have hz := congrFun hh 0
      norm_num at hz
    have ha : 0<a := by
      have hp : 0<realQuadratic (planeMatrix a b c) (![1,0] : Fin 2 → ℝ) := by
        simpa only [realQuadratic,Pi.star_apply,star_trivial] using h.dotProduct_mulVec_pos he0
      simpa [plane_actual_form] using hp
    have hex : (![-b/a,1] : Fin 2 → ℝ)≠0 := by
      intro hh
      have hz := congrFun hh 1
      norm_num at hz
    have hp : 0<realQuadratic (planeMatrix a b c) (![-b/a,1] : Fin 2 → ℝ) := by
      simpa only [realQuadratic,Pi.star_apply,star_trivial] using h.dotProduct_mulVec_pos hex
    have hvalue : realQuadratic (planeMatrix a b c) (![-b/a,1] : Fin 2 → ℝ)=c-b^2/a := by
      rw [plane_actual_form]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,one_pow,mul_one]
      field_simp [ha.ne']
      ring
    rw [hvalue] at hp
    have hm := mul_pos ha hp
    have hid : a*(c-b^2/a)=a*c-b^2 := by field_simp [ha.ne']
    exact ⟨ha,hid ▸ hm⟩
  · rintro ⟨ha,hd⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · change (planeMatrix a b c).conjTranspose=planeMatrix a b c
      ext i j
      fin_cases i <;> fin_cases j <;> simp [planeMatrix,Matrix.conjTranspose_apply]
    · intro x hx
      have hc : 0<c-b^2/a := by
        have heq : c-b^2/a=(a*c-b^2)/a := by field_simp [ha.ne']
        rw [heq]
        exact div_pos hd ha
      have hp : 0<realQuadratic (planeMatrix a b c) x := by
        by_cases hx1 : x 1=0
        · have hx0 : x 0≠0 := by
            intro hz
            apply hx
            ext i
            fin_cases i <;> simp [hz,hx1]
          rw [plane_actual_form,hx1]
          simp
          exact mul_pos ha (sq_pos_of_ne_zero hx0)
        · rw [plane_completed_square _ _ _ ha.ne']
          exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _))
            (mul_pos hc (sq_pos_of_ne_zero hx1))
      simpa only [realQuadratic,Pi.star_apply,star_trivial] using hp

theorem plane_pd_iff_positive_pivot_and_determinant (a b c : ℝ) :
    (planeMatrix a b c).PosDef ↔ 0<a ∧ 0<(planeMatrix a b c).det := by
  rw [plane_actual_determinant,plane_pd_criterion]

theorem all_real_symmetric_plane_matrices (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P.transpose=P) : P=planeMatrix (P 0 0) (P 0 1) (P 1 1) := by
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hP
  simp only [Matrix.transpose_apply] at h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMatrix,h01]

theorem generic_symmetric_plane_criterion (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P.transpose=P) : P.PosDef ↔ 0<P 0 0 ∧ 0<P.det := by
  rw [all_real_symmetric_plane_matrices P hP,
    plane_pd_iff_positive_pivot_and_determinant]
  simp [planeMatrix]

theorem real_psd_definition {n : Type*} [Fintype n] (P : Matrix n n ℝ)
    (hP : P.transpose=P) : P.PosSemidef ↔ ∀ x : n → ℝ,0≤realQuadratic P x := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hH : P.IsHermitian := by
    change P.conjTranspose=P
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,hP]
  simp only [hH,true_and,realQuadratic,Pi.star_apply,star_trivial]

theorem real_pd_definition {n : Type*} [Fintype n] (P : Matrix n n ℝ)
    (hP : P.transpose=P) : P.PosDef ↔ ∀ x : n → ℝ,x≠0 → 0<realQuadratic P x := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : P.IsHermitian := by
    change P.conjTranspose=P
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,hP]
  simp only [hH,true_and,realQuadratic,Pi.star_apply,star_trivial]

theorem real_negative_semidefinite_definition {n : Type*} [Fintype n] (P : Matrix n n ℝ)
    (hP : P.transpose=P) : (-P).PosSemidef ↔ ∀ x : n → ℝ,realQuadratic P x≤0 := by
  rw [real_psd_definition (-P) (by simp [hP])]
  simp [realQuadratic,Matrix.neg_mulVec,dotProduct_neg]

theorem real_negative_definite_definition {n : Type*} [Fintype n] (P : Matrix n n ℝ)
    (hP : P.transpose=P) : (-P).PosDef ↔ ∀ x : n → ℝ,x≠0 → realQuadratic P x<0 := by
  rw [real_pd_definition (-P) (by simp [hP])]
  simp [realQuadratic,Matrix.neg_mulVec,dotProduct_neg]

theorem real_indefinite_iff_both_signs {n : Type*} [Fintype n] (P : Matrix n n ℝ)
    (hP : P.transpose=P) : (¬P.PosSemidef ∧ ¬(-P).PosSemidef) ↔
      (∃ x : n → ℝ,realQuadratic P x<0) ∧ ∃ y : n → ℝ,0<realQuadratic P y := by
  rw [real_psd_definition P hP,real_negative_semidefinite_definition P hP]
  simp

theorem real_diagonal_psd_iff {n : Type*} [Fintype n] [DecidableEq n] (lambda : n → ℝ) :
    (Matrix.diagonal lambda).PosSemidef ↔ ∀ i,0≤lambda i := Matrix.posSemidef_diagonal_iff

end SafeLearning.CompleteFoundationsQuadraticForms
