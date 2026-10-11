import SafeLearning.CompleteModulesComplexCayley

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesComplexCayleyInverse

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualComplexInverseCayley (unitary : Matrix N N ℂ) : Matrix N N ℂ :=
  (1-unitary)*(1+unitary)⁻¹

theorem actual_inverse_cayley_right_denominator_identity
    (unitary : Matrix N N ℂ) (hunit : IsUnit (1+unitary)) :
    actualComplexInverseCayley unitary*(1+unitary)=1-unitary := by
  letI := hunit.invertible
  simp [actualComplexInverseCayley,Matrix.mul_assoc]

theorem actual_inverse_cayley_left_denominator_identity
    (unitary : Matrix N N ℂ) (hunit : IsUnit (1+unitary)) :
    (1+unitary)*actualComplexInverseCayley unitary=1-unitary := by
  letI := hunit.invertible
  have hc : (1+unitary)*(1-unitary)=(1-unitary)*(1+unitary) := by
    noncomm_ring
  unfold actualComplexInverseCayley
  rw [← Matrix.mul_assoc,hc,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_inverse_cayley_is_source_inverse_formula
    (unitary : Matrix N N ℂ) (hunit : IsUnit (1+unitary)) :
    actualComplexInverseCayley unitary=(1+unitary)⁻¹*(1-unitary) := by
  letI := hunit.invertible
  rw [← actual_inverse_cayley_left_denominator_identity unitary hunit]
  simp [← Matrix.mul_assoc]

theorem actual_inverse_cayley_is_skew_hermitian
    (unitary : Matrix N N ℂ) (hunitary : unitaryᴴ*unitary=1)
    (hunit : IsUnit (1+unitary)) :
    (actualComplexInverseCayley unitary)ᴴ= -actualComplexInverseCayley unitary := by
  letI := hunit.invertible
  letI := ((Matrix.isUnit_conjTranspose (1+unitary)).mpr hunit).invertible
  have hr := actual_inverse_cayley_right_denominator_identity unitary hunit
  have ht : (1+unitary)ᴴ*(actualComplexInverseCayley unitary)ᴴ=(1-unitary)ᴴ := by
    rw [← Matrix.conjTranspose_mul,hr]
  have he : (1+unitary)ᴴ*
      ((actualComplexInverseCayley unitary)ᴴ+actualComplexInverseCayley unitary)*(1+unitary)=0 := by
    calc
      _ = ((1+unitary)ᴴ*(actualComplexInverseCayley unitary)ᴴ)*(1+unitary)+
          (1+unitary)ᴴ*(actualComplexInverseCayley unitary*(1+unitary)) := by
        noncomm_ring
      _ = (1-unitary)ᴴ*(1+unitary)+(1+unitary)ᴴ*(1-unitary) := by
        rw [ht,hr]
      _ = (1 : Matrix N N ℂ)+1-(unitaryᴴ*unitary+unitaryᴴ*unitary) := by
        rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_add,Matrix.conjTranspose_one]
        noncomm_ring
      _ = 0 := by rw [hunitary]; abel
  have hz := congrArg (fun matrix : Matrix N N ℂ =>
    ((1+unitary)ᴴ)⁻¹*matrix*(1+unitary)⁻¹) he
  simp only [Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible,Matrix.mul_one] at hz
  rw [← Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.one_mul] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem actual_inverse_cayley_recovers_unitary
    (unitary : Matrix N N ℂ) (hunitary : unitaryᴴ*unitary=1)
    (hunit : IsUnit (1+unitary)) :
    SafeLearning.CompleteModulesComplexCayley.actualComplexCayley (actualComplexInverseCayley unitary)=unitary := by
  have hskew := actual_inverse_cayley_is_skew_hermitian unitary hunitary hunit
  letI := (SafeLearning.CompleteModulesComplexCayley.actual_complex_skew_denominator_is_invertible
    (actualComplexInverseCayley unitary) hskew).invertible
  letI := hunit.invertible
  have hleft := actual_inverse_cayley_left_denominator_identity unitary hunit
  have hright := actual_inverse_cayley_right_denominator_identity unitary hunit
  have hrelation : unitary*(1+actualComplexInverseCayley unitary)=
      1-actualComplexInverseCayley unitary := by
    calc
      _ = (1+unitary)*actualComplexInverseCayley unitary+unitary-
          actualComplexInverseCayley unitary := by noncomm_ring
      _ = (1-unitary)+unitary-actualComplexInverseCayley unitary := by rw [hleft]
      _ = _ := by noncomm_ring
  unfold SafeLearning.CompleteModulesComplexCayley.actualComplexCayley
  rw [← hrelation,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_inverse_cayley_recovers_skew
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) :
    actualComplexInverseCayley (SafeLearning.CompleteModulesComplexCayley.actualComplexCayley skew)=skew := by
  let unitary := SafeLearning.CompleteModulesComplexCayley.actualComplexCayley skew
  have hunit := SafeLearning.CompleteModulesComplexCayley.actual_complex_cayley_plus_identity_is_invertible skew hskew
  have hsunit : IsUnit (1+unitary) := by simpa [unitary,add_comm] using hunit
  letI := hsunit.invertible
  letI := (SafeLearning.CompleteModulesComplexCayley.actual_complex_skew_denominator_is_invertible
    skew hskew).invertible
  have he : skew*(1+unitary)=1-unitary := by
    have hq : unitary*(1+skew)=1-skew := by
      simp [unitary,SafeLearning.CompleteModulesComplexCayley.actualComplexCayley,Matrix.mul_assoc]
    have hc : skew*unitary=unitary*skew := by
      apply Matrix.mul_left_injective_of_invertible (1+skew)
      have hx : skew*(1+skew)=(1+skew)*skew := by noncomm_ring
      calc
        _ = skew*(unitary*(1+skew)) := by simp only [Matrix.mul_assoc]
        _ = skew*(1-skew) := by rw [hq]
        _ = (1-skew)*skew := by noncomm_ring
        _ = (unitary*(1+skew))*skew := by rw [hq]
        _ = unitary*(skew*(1+skew)) := by rw [hx,Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    calc
      _ = skew+skew*unitary := by noncomm_ring
      _ = skew+unitary*skew := by rw [hc]
      _ = unitary*(1+skew)+skew-unitary := by noncomm_ring
      _ = (1-skew)+skew-unitary := by rw [hq]
      _ = _ := by noncomm_ring
  unfold actualComplexInverseCayley
  rw [← he,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_cayley_preimage_is_unique
    (unitary skew : Matrix N N ℂ) (hskew : skewᴴ= -skew)
    (htransform : SafeLearning.CompleteModulesComplexCayley.actualComplexCayley skew=unitary) :
    skew=actualComplexInverseCayley unitary := by
  rw [← htransform,actual_inverse_cayley_recovers_skew skew hskew]

theorem actual_unitary_denominator_invertible_iff_no_negative_one_eigenvector
    (unitary : Matrix N N ℂ) : IsUnit (1+unitary) ↔
    ∀ vector : N → ℂ, unitary*ᵥvector= -vector → vector=0 := by
  constructor
  · intro hunit vector heigen
    have hz : (1+unitary)*ᵥvector=0 := by simp [Matrix.add_mulVec,heigen]
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    exact hinj (by simpa using hz)
  · intro hnoeigen
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro left right hequal
    have hz : (1+unitary)*ᵥ(left-right)=0 := by
      simp [Matrix.mulVec_sub,hequal]
    have hsum : unitary*ᵥ(left-right)+(left-right)=0 := by
      simpa [Matrix.add_mulVec,add_comm] using hz
    have hdifference := hnoeigen (left-right) (eq_neg_of_add_eq_zero_left hsum)
    exact sub_eq_zero.mp hdifference

theorem actual_unitary_without_negative_one_has_unique_skew_preimage
    (unitary : Matrix N N ℂ) (hunitary : unitaryᴴ*unitary=1)
    (hnoeigen : ∀ vector : N → ℂ, unitary*ᵥvector= -vector → vector=0) :
    ∃! skew : Matrix N N ℂ, skewᴴ= -skew ∧
      SafeLearning.CompleteModulesComplexCayley.actualComplexCayley skew=unitary := by
  have hunit := (actual_unitary_denominator_invertible_iff_no_negative_one_eigenvector
    unitary).mpr hnoeigen
  refine ⟨actualComplexInverseCayley unitary,
    ⟨actual_inverse_cayley_is_skew_hermitian unitary hunitary hunit,
      actual_inverse_cayley_recovers_unitary unitary hunitary hunit⟩,?_⟩
  intro skew hpreimage
  exact actual_cayley_preimage_is_unique unitary skew hpreimage.1 hpreimage.2

end SafeLearning.CompleteModulesComplexCayleyInverse
