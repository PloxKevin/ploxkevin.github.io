import SafeLearning.CompleteFoundationsQuadraticForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix ComplexOrder

namespace SafeLearning.CompleteFoundationsCongruence

open SafeLearning.CompleteFoundationsQuadraticForms

def congruence {m n : Type*} [Fintype m] (M : Matrix m m ℝ) (T : Matrix m n ℝ) : Matrix n n ℝ :=
  T.transpose*M*T

theorem congruence_quadratic_identity {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℝ) (T : Matrix m n ℝ) (x : n → ℝ) :
    realQuadratic (congruence M T) x=realQuadratic M (T *ᵥ x) := by
  unfold congruence realQuadratic
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem congruence_psd {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℝ) (T : Matrix m n ℝ) (hM : M.PosSemidef) :
    (congruence M T).PosSemidef := by
  simpa only [congruence,Matrix.conjTranspose_eq_transpose_of_trivial] using hM.conjTranspose_mul_mul_same T

theorem congruence_pd_iff_injective {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℝ) (T : Matrix m n ℝ) (hM : M.PosDef) :
    (congruence M T).PosDef ↔ Function.Injective T.mulVec := by
  constructor
  · intro h x y hxy
    by_contra hn
    have hz : x-y≠0 := sub_ne_zero.mpr hn
    have hT : T *ᵥ (x-y)=0 := by simp [Matrix.mulVec_sub,hxy]
    have hp : 0<realQuadratic (congruence M T) (x-y) := by
      simpa only [realQuadratic,star_trivial] using h.dotProduct_mulVec_pos hz
    rw [congruence_quadratic_identity,hT] at hp
    simp [realQuadratic] at hp
  · intro h
    simpa only [congruence,Matrix.conjTranspose_eq_transpose_of_trivial] using hM.conjTranspose_mul_mul_same h

theorem congruence_pd_iff_independent_columns {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℝ) (T : Matrix m n ℝ) (hM : M.PosDef) :
    (congruence M T).PosDef ↔ LinearIndependent ℝ T.col := by
  rw [congruence_pd_iff_injective M T hM,Matrix.mulVec_injective_iff]

theorem inverse_congruence_identity {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℝ) (hT : IsUnit T.det) : congruence (congruence M T) T⁻¹=M := by
  unfold congruence
  calc
    T⁻¹.transpose*(T.transpose*M*T)*T⁻¹=(T*T⁻¹).transpose*M*(T*T⁻¹) := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = M := by rw [Matrix.mul_nonsing_inv T hT];simp

theorem invertible_congruence_psd_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℝ) (hT : IsUnit T.det) : (congruence M T).PosSemidef ↔ M.PosSemidef := by
  constructor
  · intro h
    have hh := congruence_psd (congruence M T) T⁻¹ h
    rwa [inverse_congruence_identity M T hT] at hh
  · exact congruence_psd M T

theorem invertible_congruence_pd_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℝ) (hT : IsUnit T.det) : (congruence M T).PosDef ↔ M.PosDef := by
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  have hTi : IsUnit T⁻¹ := (Matrix.isUnit_iff_isUnit_det T⁻¹).mpr
    (Matrix.isUnit_det_of_left_inverse (Matrix.mul_nonsing_inv T hT))
  constructor
  · intro h
    have hh := (congruence_pd_iff_injective (congruence M T) T⁻¹ h).mpr
      (Matrix.mulVec_injective_of_isUnit hTi)
    rwa [inverse_congruence_identity M T hT] at hh
  · intro h
    exact (congruence_pd_iff_injective M T h).mpr (Matrix.mulVec_injective_of_isUnit hTu)

theorem complex_congruence_quadratic_identity {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℂ) (T : Matrix m n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((T.conjTranspose*M*T) *ᵥ x)=star (T *ᵥ x) ⬝ᵥ (M *ᵥ (T *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose,star_star]

theorem complex_congruence_psd {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℂ) (T : Matrix m n ℂ) (hM : M.PosSemidef) :
    (T.conjTranspose*M*T).PosSemidef := hM.conjTranspose_mul_mul_same T

theorem complex_congruence_pd_iff_independent_columns {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m m ℂ) (T : Matrix m n ℂ) (hM : M.PosDef) :
    (T.conjTranspose*M*T).PosDef ↔ LinearIndependent ℂ T.col := by
  rw [← Matrix.mulVec_injective_iff]
  constructor
  · intro h x y hxy
    by_contra hn
    have hz : x-y≠0 := sub_ne_zero.mpr hn
    have hT : T *ᵥ (x-y)=0 := by simp [Matrix.mulVec_sub,hxy]
    have hp := h.dotProduct_mulVec_pos hz
    rw [complex_congruence_quadratic_identity,hT] at hp
    simp at hp
  · exact hM.conjTranspose_mul_mul_same

theorem complex_inverse_congruence_identity {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℂ) (hT : IsUnit T.det) :
    T⁻¹.conjTranspose*(T.conjTranspose*M*T)*T⁻¹=M := by
  calc
    T⁻¹.conjTranspose*(T.conjTranspose*M*T)*T⁻¹=(T*T⁻¹).conjTranspose*M*(T*T⁻¹) := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = M := by rw [Matrix.mul_nonsing_inv T hT];simp

theorem complex_invertible_congruence_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℂ) (hT : IsUnit T.det) :
    ((T.conjTranspose*M*T).PosSemidef ↔ M.PosSemidef) ∧
    ((T.conjTranspose*M*T).PosDef ↔ M.PosDef) := by
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  have hTi : IsUnit T⁻¹ := (Matrix.isUnit_iff_isUnit_det T⁻¹).mpr
    (Matrix.isUnit_det_of_left_inverse (Matrix.mul_nonsing_inv T hT))
  constructor
  · constructor
    · intro h
      have hh := h.conjTranspose_mul_mul_same T⁻¹
      rwa [complex_inverse_congruence_identity M T hT] at hh
    · exact fun h => h.conjTranspose_mul_mul_same T
  · constructor
    · intro h
      have hh := h.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hTi)
      rwa [complex_inverse_congruence_identity M T hT] at hh
    · exact fun h => h.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hTu)

theorem real_gram_psd {m n : Type*} [Fintype m] [Fintype n]
    (R : Matrix m n ℝ) : (R.transpose*R).PosSemidef ∧ (R*R.transpose).PosSemidef := by
  constructor
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self R
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose R

theorem real_gram_pd_iff_independent_columns {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (R : Matrix m n ℝ) :
    (R.transpose*R).PosDef ↔ LinearIndependent ℝ R.col := by
  simpa [congruence] using congruence_pd_iff_independent_columns (1 : Matrix m m ℝ) R Matrix.PosDef.one

def singularT : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
def indefiniteM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,-1]
def rectangularT : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i=0 then 1 else 0

theorem singular_congruence_counterexample :
    congruence (1 : Matrix (Fin 2) (Fin 2) ℝ) singularT=singularT ∧
    singularT.det=0 ∧ singularT.PosSemidef ∧ ¬singularT.PosDef := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [congruence,singularT,Matrix.mul_apply,Matrix.diagonal,Matrix.transpose_apply,Fin.sum_univ_succ]
  · norm_num [singularT,Matrix.det_fin_two,Matrix.diagonal]
  · rw [singularT,Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · intro h
    have hx : (![0,1] : Fin 2 → ℝ)≠0 := by
      intro hz
      have hh := congrFun hz 1
      norm_num at hh
    have hh := h.dotProduct_mulVec_pos hx
    norm_num [singularT,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_succ] at hh

theorem rectangular_congruence_counterexample :
    congruence indefiniteM rectangularT=(1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    (congruence indefiniteM rectangularT).PosDef ∧
    realQuadratic indefiniteM (![1,0] : Fin 2 → ℝ)=1 ∧
    realQuadratic indefiniteM (![0,1] : Fin 2 → ℝ)= -1 ∧ ¬indefiniteM.PosSemidef := by
  have heq : congruence indefiniteM rectangularT=(1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j
    norm_num [congruence,indefiniteM,rectangularT,Matrix.mul_apply,Matrix.diagonal,
      Matrix.transpose_apply,Fin.sum_univ_succ]
  refine ⟨heq,heq ▸ Matrix.PosDef.one,?_,?_,?_⟩
  · norm_num [realQuadratic,indefiniteM,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_succ]
  · norm_num [realQuadratic,indefiniteM,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_succ]
  · intro h
    have hh := h.dotProduct_mulVec_nonneg (![0,1] : Fin 2 → ℝ)
    norm_num [indefiniteM,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_succ] at hh

end SafeLearning.CompleteFoundationsCongruence
