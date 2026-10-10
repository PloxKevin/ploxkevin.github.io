import SafeLearning.CompleteModulesScalarSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesScalarBoundedReal
open CompleteModulesScalarSDP

def actualScalarGainMatrix (storage gain : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1-3*storage/4,storage/2;storage/2,storage-gain^2]

theorem actual_scalar_storage_difference_is_source_quadratic
    (a b c storage gain state input : ℝ) :
    storage*(a*state+b*input)^2-storage*state^2-(gain^2*input^2-(c*state)^2)=
      (storage*a^2-storage+c^2)*state^2+2*storage*a*b*state*input+
        (storage*b^2-gain^2)*input^2 := by ring

theorem actual_scalar_matrix_quadratic (storage gain : ℝ) (vector : Fin 2 → ℝ) :
    vector ⬝ᵥ (actualScalarGainMatrix storage gain *ᵥ vector)=
      (1-3*storage/4)*(vector 0)^2+storage*(vector 0)*(vector 1)+
        (storage-gain^2)*(vector 1)^2 := by
  simp [actualScalarGainMatrix,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  ring

theorem actual_scalar_gain_matrix_negative_semidefinite_iff (storage gain : ℝ) :
    (-actualScalarGainMatrix storage gain).PosSemidef ↔
    ∀ state input : ℝ,(1-3*storage/4)*state^2+storage*state*input+
      (storage-gain^2)*input^2 ≤ 0 := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hh : (-actualScalarGainMatrix storage gain).IsHermitian := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [actualScalarGainMatrix,Matrix.conjTranspose_apply]
  constructor
  · intro h state input
    have hv := h.2 (![state,input] : Fin 2 → ℝ)
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hv
    rw [actual_scalar_matrix_quadratic] at hv
    norm_num at hv
    linarith
  · intro h
    refine ⟨hh,?_⟩
    intro vector
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
    rw [actual_scalar_matrix_quadratic]
    exact neg_nonneg.mpr (h (vector 0) (vector 1))

theorem actual_scalar_source_matrix_is_negative_semidefinite :
    (-actualScalarGainMatrix 2 2).PosSemidef := by
  rw [actual_scalar_gain_matrix_negative_semidefinite_iff]
  intro state input
  nlinarith [sq_nonneg (state-2*input)]

theorem actual_scalar_source_matrix_trace_determinant_characteristic_polynomial :
    (actualScalarGainMatrix 2 2).trace= -(5/2:ℝ) ∧
    (actualScalarGainMatrix 2 2).det=0 ∧
    (actualScalarGainMatrix 2 2).charpoly=Polynomial.X*(Polynomial.X+Polynomial.C (5/2:ℝ)) := by
  constructor
  · norm_num [actualScalarGainMatrix,Matrix.trace_fin_two]
  constructor
  · norm_num [actualScalarGainMatrix,Matrix.det_fin_two]
  · rw [Matrix.charpoly_fin_two]
    norm_num [actualScalarGainMatrix]
    ring

theorem actual_scalar_certificate_requires_storage_strictly_above_four_thirds
    (storage gain : ℝ) (hcertificate : (-actualScalarGainMatrix storage gain).PosSemidef) :
    (4/3:ℝ) < storage := by
  rw [actual_scalar_gain_matrix_negative_semidefinite_iff] at hcertificate
  have hfirst := hcertificate 1 0
  have hlower : (4/3:ℝ) ≤ storage := by nlinarith
  by_contra hn
  have he : storage=(4/3:ℝ) := by linarith
  have hbad := hcertificate (3*gain^2/4) 1
  rw [he] at hbad
  nlinarith

theorem actual_scalar_certificate_requires_gain_at_least_two
    (storage gain : ℝ) (hgain : 0 ≤ gain)
    (hcertificate : (-actualScalarGainMatrix storage gain).PosSemidef) :
    2 ≤ gain := by
  rw [actual_scalar_gain_matrix_negative_semidefinite_iff] at hcertificate
  have hsteady := hcertificate 2 1
  nlinarith

def actualScalarRequiredGainSquared (storage : ℝ) : ℝ :=
  storage+storage^2/(3*storage-4)

theorem actual_scalar_schur_required_gain_formula (storage gain : ℝ)
    (hstorage : (4/3:ℝ) < storage) :
    (-actualScalarGainMatrix storage gain).PosSemidef ↔
      actualScalarRequiredGainSquared storage ≤ gain^2 := by
  rw [actual_scalar_gain_matrix_negative_semidefinite_iff]
  have hnegative : 1-3*storage/4 < 0 := by linarith
  have he : (∀ state input : ℝ,(1-3*storage/4)*state^2+storage*state*input+
      (storage-gain^2)*input^2 ≤ 0) ↔
      (∀ state input : ℝ,(storage-gain^2)*state^2+2*(storage/2)*state*input+
        (1-3*storage/4)*input^2 ≤ 0) := by
    constructor <;> intro h state input
    · convert h input state using 1 <;> ring
    · convert h input state using 1 <;> ring
  rw [he,negative_scalar_schur_iff _ _ _ hnegative]
  have hden : 3*storage-4≠0 := by linarith
  have hden' : 1-3*storage/4≠0 := hnegative.ne
  have hi : (storage-gain^2)-(storage/2)^2/(1-3*storage/4)=
      actualScalarRequiredGainSquared storage-gain^2 := by
    unfold actualScalarRequiredGainSquared
    rw [show 1-3*storage/4= -(3*storage-4)/4 by ring]
    field_simp [hden]
    ring
  rw [hi]
  constructor <;> intro h <;> linarith

theorem actual_scalar_required_gain_gap_identity (storage : ℝ)
    (hden : 3*storage-4≠0) :
    actualScalarRequiredGainSquared storage-4=4*(storage-2)^2/(3*storage-4) := by
  apply (mul_right_cancel₀ hden)
  unfold actualScalarRequiredGainSquared
  rw [div_mul_cancel₀ _ hden]
  calc
    (storage+storage^2/(3*storage-4)-4)*(3*storage-4)=
        (storage-4)*(3*storage-4)+(storage^2/(3*storage-4))*(3*storage-4) := by ring
    _ = (storage-4)*(3*storage-4)+storage^2 := by rw [div_mul_cancel₀ _ hden]
    _ = 4*(storage-2)^2 := by ring

theorem actual_scalar_required_gain_global_minimum (storage : ℝ)
    (hstorage : (4/3:ℝ) < storage) :
    4 ≤ actualScalarRequiredGainSquared storage ∧
    (actualScalarRequiredGainSquared storage=4 ↔ storage=2) := by
  have hden : 0 < 3*storage-4 := by linarith
  have hi := actual_scalar_required_gain_gap_identity storage hden.ne'
  have hnonneg : 0 ≤ 4*(storage-2)^2/(3*storage-4) := by positivity
  constructor
  · linarith
  · constructor
    · intro h
      have hzero : 4*(storage-2)^2=0 := by
        have hz : 4*(storage-2)^2/(3*storage-4)=0 := by linarith
        exact (div_eq_zero_iff.mp hz).resolve_right hden.ne'
      nlinarith
    · intro h
      norm_num [h,actualScalarRequiredGainSquared]

end SafeLearning.CompleteModulesScalarBoundedReal
