import SafeLearning.CompleteFoundationsCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix NNReal

namespace SafeLearning.CompleteFoundationsGramRegularization

open SafeLearning.CompleteFoundationsQuadraticForms
open SafeLearning.CompleteFoundationsCongruence

theorem self_dot_euclidean_norm_squared {n : Type*} [Fintype n] (x : n → ℝ) :
    x ⬝ᵥ x=‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct,pow_two]

theorem gram_actual_quadratic_norm {m n : Type*} [Fintype m] [Fintype n]
    (R : Matrix m n ℝ) (x : n → ℝ) :
    realQuadratic (R.transpose*R) x=‖(WithLp.toLp 2 (R *ᵥ x) : EuclideanSpace ℝ m)‖^2 := by
  unfold realQuadratic
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,self_dot_euclidean_norm_squared]

theorem positive_regularization_pd {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (hK : K.PosSemidef) (lambda : ℝ) (hl : 0<lambda) :
    (K+lambda • (1 : Matrix n n ℝ)).PosDef :=
  Matrix.PosDef.posSemidef_add hK (Matrix.PosDef.one.smul hl)

theorem positive_regularization_is_invertible {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (hK : K.PosSemidef) (lambda : ℝ) (hl : 0<lambda) :
    IsUnit (K+lambda • (1 : Matrix n n ℝ)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (positive_regularization_pd K hK lambda hl).det_pos.ne'

theorem regularized_gram_exact_quadratic {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (R : Matrix m n ℝ) (epsilon : ℝ) (x : n → ℝ) :
    realQuadratic (epsilon • (1 : Matrix n n ℝ)+R.transpose*R) x=
      epsilon*‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖^2+
      ‖(WithLp.toLp 2 (R *ᵥ x) : EuclideanSpace ℝ m)‖^2 := by
  unfold realQuadratic
  rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
    self_dot_euclidean_norm_squared]
  rw [← gram_actual_quadratic_norm]
  rfl

theorem regularized_gram_strict_quad_and_invertible {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (R : Matrix m n ℝ) (epsilon : ℝ) (he : 0<epsilon) :
    (epsilon • (1 : Matrix n n ℝ)+R.transpose*R).PosDef ∧
    IsUnit (epsilon • (1 : Matrix n n ℝ)+R.transpose*R) ∧
    ∀x : n → ℝ,x≠0 → 0<realQuadratic (epsilon • (1 : Matrix n n ℝ)+R.transpose*R) x := by
  have hK := (real_gram_psd R).1
  have hp : (epsilon • (1 : Matrix n n ℝ)+R.transpose*R).PosDef := by
    simpa [add_comm] using positive_regularization_pd _ hK epsilon he
  have hi : IsUnit (epsilon • (1 : Matrix n n ℝ)+R.transpose*R) := by
    simpa [add_comm] using positive_regularization_is_invertible _ hK epsilon he
  refine ⟨hp,hi,?_⟩
  intro x hx
  simpa only [realQuadratic,star_trivial] using hp.dotProduct_mulVec_pos hx

theorem actual_regularized_l1_certificate {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (R : Matrix m n ℝ) (epsilon : ℝ) (he : 0<epsilon)
    (xi xiStar : n → ℝ) (hx : xi≠xiStar) :
    0<‖(WithLp.toLp 1 ((epsilon • (1 : Matrix n n ℝ)+R.transpose*R) *ᵥ (xi-xiStar)) :
      PiLp 1 (fun _ : n => ℝ))‖ := by
  have hi := (regularized_gram_strict_quad_and_invertible R epsilon he).2.1
  have hinj := Matrix.mulVec_injective_of_isUnit hi
  apply norm_pos_iff.mpr
  intro hz
  have hraw : (epsilon • (1 : Matrix n n ℝ)+R.transpose*R) *ᵥ (xi-xiStar)=0 := by
    exact WithLp.toLp_injective 1 hz
  have hx0 : xi-xiStar=0 := hinj (by simpa using hraw)
  exact hx (sub_eq_zero.mp hx0)

def outer {n : Type*} (a : n → ℝ) : Matrix n n ℝ := Matrix.vecMulVec a a

theorem outer_actual_action {n : Type*} [Fintype n] (a x : n → ℝ) :
    outer a *ᵥ x=(a ⬝ᵥ x) • a := by
  ext i
  simp only [outer,Matrix.mulVec,dotProduct,Matrix.vecMulVec,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change a i*a j*x j=(a j*x j)*a i
  ring

theorem outer_psd {n : Type*} [Fintype n] (a : n → ℝ) : (outer a).PosSemidef := by
  simpa only [outer,star_trivial] using Matrix.posSemidef_vecMulVec_self_star a

theorem outer_actual_quadratic {n : Type*} [Fintype n] (a x : n → ℝ) :
    realQuadratic (outer a) x=(a ⬝ᵥ x)^2 := by
  unfold realQuadratic
  rw [outer_actual_action,dotProduct_smul,dotProduct_comm,pow_two]
  rfl

theorem outer_zero {n : Type*} : outer (0 : n → ℝ)=0 := by
  ext i j
  simp [outer,Matrix.vecMulVec]

theorem outer_actual_rank {n : Type*} [Fintype n] [DecidableEq n] (a : n → ℝ) :
    (a=0 → (outer a).rank=0) ∧ (a≠0 → (outer a).rank=1) := by
  constructor
  · rintro rfl
    rw [outer_zero,Matrix.rank_zero]
  · intro ha
    obtain ⟨i,hi⟩ : ∃ i,a i≠0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    let minor : Matrix (Fin 1) (Fin 1) ℝ := (outer a).submatrix (fun _ => i) (fun _ => i)
    have hd : minor.det≠0 := by
      simpa [minor,Matrix.det_fin_one,outer,Matrix.vecMulVec,Matrix.submatrix_apply] using mul_ne_zero hi hi
    have hr : minor.rank=1 := by simpa using Matrix.rank_of_det_ne_zero hd
    have hle := Matrix.rank_submatrix_le (outer a) (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)
    change minor.rank≤(outer a).rank at hle
    rw [hr] at hle
    exact le_antisymm (Matrix.rank_vecMulVec_le a a) hle

theorem outer_eigen_direction {n : Type*} [Fintype n] (a : n → ℝ) :
    outer a *ᵥ a=‖(WithLp.toLp 2 a : EuclideanSpace ℝ n)‖^2 • a := by
  rw [outer_actual_action,self_dot_euclidean_norm_squared]

theorem outer_orthogonal_directions {n : Type*} [Fintype n] (a x : n → ℝ)
    (hx : a ⬝ᵥ x=0) : outer a *ᵥ x=0 := by rw [outer_actual_action,hx,zero_smul]

theorem outer_psd_increase {n : Type*} [Fintype n] (M : Matrix n n ℝ)
    (a : n → ℝ) (beta : ℝ) (hb : 0≤beta) :
    (beta • outer a).PosSemidef ∧ ∀x : n → ℝ,
    realQuadratic (M+beta • outer a) x=realQuadratic M x+beta*(a ⬝ᵥ x)^2 ∧
    realQuadratic M x≤realQuadratic (M+beta • outer a) x := by
  refine ⟨(outer_psd a).smul hb,?_⟩
  intro x
  have heq : realQuadratic (M+beta • outer a) x=realQuadratic M x+beta*(a ⬝ᵥ x)^2 := by
    unfold realQuadratic
    rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul]
    rw [← outer_actual_quadratic]
    rfl
  exact ⟨heq,by rw [heq];nlinarith [sq_nonneg (a ⬝ᵥ x)]⟩

end SafeLearning.CompleteFoundationsGramRegularization
