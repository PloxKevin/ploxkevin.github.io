import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SafeLearning.CompleteFoundationsGeneralizedEigen
open Matrix Set
open scoped BigOperators

def sourceW : Matrix (Fin 1) (Fin 2) ℝ := !![1,1]
def sourceM : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,2]
def inverseM : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,1/2]
def sourceGram : Matrix (Fin 2) (Fin 2) ℝ := sourceW.transpose * sourceW
def sourceA : Matrix (Fin 2) (Fin 2) ℝ := sourceGram * inverseM

theorem actual_source_inverse : sourceM⁻¹ = inverseM := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceM,inverseM,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_source_gram_and_generalized_matrix :
    sourceGram = !![1,1;1,1] ∧ sourceA = !![1,1/2;1,1/2] ∧
    sourceA = sourceW.transpose * sourceW * sourceM⁻¹ := by
  have hg : sourceGram = !![1,1;1,1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [sourceGram,sourceW,Matrix.mul_apply,Fin.sum_univ_succ]
  refine ⟨hg,?_,?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [sourceA,hg,inverseM,Matrix.mul_apply,Fin.sum_univ_succ]
  · rw [actual_source_inverse]; rfl

theorem actual_source_matrix_is_not_symmetric : sourceA.transpose ≠ sourceA := by
  intro he
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) he
  rw [actual_source_gram_and_generalized_matrix.2.1] at hh
  norm_num [Matrix.transpose_apply] at hh

theorem actual_source_trace_determinant_and_charpoly (lambda : ℝ) :
    sourceA.trace = 3/2 ∧ sourceA.det = 0 ∧
      sourceA.charpoly.eval lambda = lambda*(lambda-3/2) := by
  rw [actual_source_gram_and_generalized_matrix.2.1]
  norm_num [Matrix.trace,Matrix.det_fin_two,Matrix.eval_charpoly,
    Matrix.scalar_apply,Matrix.sub_apply,Fin.sum_univ_succ]
  ring

theorem actual_source_complex_characteristic_roots (lambda : ℂ) :
    ((sourceA.map (fun x : ℝ => (x:ℂ))).charpoly.eval lambda = 0) ↔
      lambda = 0 ∨ lambda = 3/2 := by
  have he : (sourceA.map (fun x : ℝ => (x:ℂ))).charpoly.eval lambda =
      lambda*(lambda-3/2) := by
    rw [actual_source_gram_and_generalized_matrix.2.1,Matrix.eval_charpoly]
    simp [Matrix.det_fin_two,Matrix.scalar_apply,Matrix.sub_apply]
    ring
  rw [he,mul_eq_zero,sub_eq_zero]

theorem actual_source_all_real_characteristic_roots (lambda : ℝ) :
    sourceA.charpoly.eval lambda = 0 ↔ lambda = 0 ∨ lambda = 3/2 := by
  rw [actual_source_trace_determinant_and_charpoly lambda |>.2.2,mul_eq_zero,sub_eq_zero]

theorem actual_source_all_complex_roots_are_real_nonnegative (lambda : ℂ)
    (hroot : (sourceA.map (fun x : ℝ => (x:ℂ))).charpoly.eval lambda = 0) :
    lambda.im = 0 ∧ 0 ≤ lambda.re := by
  rcases (actual_source_complex_characteristic_roots lambda).mp hroot with rfl | rfl <;> norm_num

def normalization : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,1/Real.sqrt 2]
def normalizationInverse : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,Real.sqrt 2]
def sourceG : Fin 2 → ℝ := ![1,1/Real.sqrt 2]

theorem actual_source_normalization_square_and_inverse :
    normalization * normalization = inverseM ∧
    normalization * normalizationInverse = 1 ∧
    normalizationInverse * normalization = 1 ∧ normalization⁻¹ = normalizationInverse := by
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : normalization * normalizationInverse = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [normalization,normalizationInverse,Matrix.mul_apply,Fin.sum_univ_succ,hn]
  have h2 : normalizationInverse * normalization = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [normalization,normalizationInverse,Matrix.mul_apply,Fin.sum_univ_succ,hn]
  refine ⟨?_,h1,h2,Matrix.inv_eq_right_inv h1⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [normalization,inverseM,Matrix.mul_apply,Fin.sum_univ_succ]
  field_simp
  nlinarith

theorem actual_source_similarity_to_normalized_gram :
    normalization * sourceA * normalizationInverse = normalization * sourceGram * normalization ∧
    normalization * sourceGram * normalization = Matrix.vecMulVec sourceG sourceG ∧
    sourceG ⬝ᵥ sourceG = 3/2 := by
  have hs : inverseM = normalization * normalization :=
    actual_source_normalization_square_and_inverse.1.symm
  have hcancel := actual_source_normalization_square_and_inverse.2.1
  constructor
  · unfold sourceA
    rw [hs]
    simp only [Matrix.mul_assoc]
    rw [hcancel,Matrix.mul_one]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [normalization,actual_source_gram_and_generalized_matrix.1,sourceG,
        Matrix.vecMulVec,Matrix.mul_apply,Fin.sum_univ_succ]
  · have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    simp [sourceG,dotProduct,Fin.sum_univ_succ]
    field_simp
    nlinarith

theorem actual_source_g_euclidean_norm_squared :
    ‖(WithLp.toLp 2 sourceG : EuclideanSpace ℝ (Fin 2))‖^2 = 3/2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct,mul_comm] using
    actual_source_similarity_to_normalized_gram.2.2

theorem actual_source_normalized_gram_characteristic_roots (lambda : ℝ) :
    (normalization * sourceGram * normalization).charpoly.eval lambda = 0 ↔
      lambda = 0 ∨ lambda = 3/2 := by
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (1/Real.sqrt 2)*(1/Real.sqrt 2) = (1/2:ℝ) := by
    field_simp
    nlinarith
  have hi : (Real.sqrt 2)⁻¹ ^ 2 = (1/2:ℝ) := by
    simpa only [one_div,pow_two] using ht
  have he : (normalization * sourceGram * normalization).charpoly.eval lambda =
      lambda*(lambda-3/2) := by
    rw [actual_source_similarity_to_normalized_gram.2.1,Matrix.eval_charpoly]
    simp [Matrix.det_fin_two,Matrix.vecMulVec,sourceG,Matrix.scalar_apply,
      Matrix.sub_apply]
    ring_nf
    rw [hi]
    ring
  rw [he,mul_eq_zero,sub_eq_zero]

def sourceCertificate (F : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := sourceM - F • sourceGram

theorem actual_source_certificate_matrix_and_determinant (F : ℝ) :
    sourceCertificate F = !![1-F,-F;-F,2-F] ∧
    (sourceCertificate F).det = 2-3*F := by
  have he : sourceCertificate F = !![1-F,-F;-F,2-F] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sourceCertificate,sourceM,actual_source_gram_and_generalized_matrix.1]
  exact ⟨he,by rw [he]; simp [Matrix.det_fin_two]; ring⟩

theorem actual_source_certificate_quadratic_completion (F : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (sourceCertificate F *ᵥ x) =
      (2/3-F)*(x 0+x 1)^2+(1/3)*(x 0-2*x 1)^2 := by
  rw [actual_source_certificate_matrix_and_determinant F |>.1]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_source_certificate_psd_iff (F : ℝ) :
    (sourceCertificate F).PosSemidef ↔ F ≤ 2/3 := by
  constructor
  · intro h
    have hp := h.dotProduct_mulVec_nonneg (![1,1/2] : Fin 2 → ℝ)
    simp only [star_trivial] at hp
    rw [actual_source_certificate_quadratic_completion] at hp
    norm_num at hp
    linarith
  · intro hF
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [actual_source_certificate_matrix_and_determinant F |>.1]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · intro x
      simp only [star_trivial]
      rw [actual_source_certificate_quadratic_completion]
      positivity

theorem actual_source_psd_threshold_and_largest_parameter :
    IsGreatest {F : ℝ | 0 ≤ F ∧ (sourceCertificate F).PosSemidef} (2/3) ∧
    ∀ F : ℝ, (sourceCertificate F).PosSemidef ↔ F*(3/2) ≤ 1 := by
  constructor
  · refine ⟨⟨by norm_num,(actual_source_certificate_psd_iff _).mpr le_rfl⟩,?_⟩
    intro F hF; exact (actual_source_certificate_psd_iff F).mp hF.2
  · intro F; rw [actual_source_certificate_psd_iff]; constructor <;> intro h <;> linarith

theorem actual_source_two_by_two_test (F : ℝ) :
    (sourceCertificate F).det ≥ 0 ↔ F ≤ 2/3 := by
  rw [actual_source_certificate_matrix_and_determinant F |>.2]
  constructor <;> intro h <;> linarith

theorem actual_source_diagonals_nonnegative (F : ℝ) (hF : F ≤ 1) :
    0 ≤ sourceCertificate F 0 0 ∧ 0 ≤ sourceCertificate F 1 1 := by
  rw [actual_source_certificate_matrix_and_determinant F |>.1]
  norm_num
  constructor <;> linarith

def sourceRayleigh (x : Fin 2 → ℝ) : ℝ := (x 0+x 1)^2/((x 0)^2+2*(x 1)^2)

theorem actual_source_nonzero_denominator (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < (x 0)^2+2*(x 1)^2 := by
  by_contra hn
  have hz : x 0 = 0 ∧ x 1 = 0 := by
    constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  apply hx; ext i; fin_cases i <;> simp [hz.1,hz.2]

theorem actual_source_rayleigh_maximizer_iff (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    sourceRayleigh x ≤ 3/2 ∧
    (sourceRayleigh x = 3/2 ↔ ∃ scale : ℝ,scale ≠ 0 ∧ x = scale • ![1,1/2]) := by
  have hd := actual_source_nonzero_denominator x hx
  have hs := sq_nonneg (x 0-2*x 1)
  constructor
  · rw [sourceRayleigh,div_le_iff₀ hd]; nlinarith
  constructor
  · intro he
    have heq : (x 0+x 1)^2=(3/2)*((x 0)^2+2*(x 1)^2) :=
      (div_eq_iff hd.ne').mp he
    have hz : x 0=2*x 1 := by nlinarith
    have hscale : x 0 ≠ 0 := by
      intro h; apply hx; ext i; fin_cases i <;> simp [h] <;> linarith
    refine ⟨x 0,hscale,?_⟩
    ext i; fin_cases i <;> simp <;> linarith
  · rintro ⟨scale,hn,rfl⟩
    unfold sourceRayleigh
    simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
    ring

theorem actual_source_rayleigh_is_greatest_and_sharp_layer_gain :
    IsGreatest (sourceRayleigh '' {x : Fin 2 → ℝ | x ≠ 0}) (3/2) ∧
    (∀ x : Fin 2 → ℝ,(x 0+x 1)^2 ≤ (3/2)*((x 0)^2+2*(x 1)^2)) ∧
    (1/(2/3) : ℝ) = 3/2 := by
  refine ⟨⟨⟨![1,1/2],?_,?_⟩,?_⟩,?_,by norm_num⟩
  · intro he; have h := congrFun he 0; norm_num at h
  · norm_num [sourceRayleigh]
  · rintro _ ⟨x,hx,rfl⟩; exact (actual_source_rayleigh_maximizer_iff x hx).1
  · intro x; nlinarith [sq_nonneg (x 0-2*x 1)]

end SafeLearning.CompleteFoundationsGeneralizedEigen
