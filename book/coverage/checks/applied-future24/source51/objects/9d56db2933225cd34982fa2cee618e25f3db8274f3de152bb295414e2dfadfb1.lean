import SafeLearning.CompleteModulesCayley

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesCayleyInverse

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualInverseCayley (orthogonal : Matrix N N ℝ) : Matrix N N ℝ :=
  (1-orthogonal)*(1+orthogonal)⁻¹

theorem actual_inverse_cayley_right_denominator_identity
    (orthogonal : Matrix N N ℝ) (hunit : IsUnit (1+orthogonal)) :
    actualInverseCayley orthogonal*(1+orthogonal)=1-orthogonal := by
  letI := hunit.invertible
  simp [actualInverseCayley,Matrix.mul_assoc]

theorem actual_inverse_cayley_left_denominator_identity
    (orthogonal : Matrix N N ℝ) (hunit : IsUnit (1+orthogonal)) :
    (1+orthogonal)*actualInverseCayley orthogonal=1-orthogonal := by
  letI := hunit.invertible
  have hc : (1+orthogonal)*(1-orthogonal)=(1-orthogonal)*(1+orthogonal) := by
    noncomm_ring
  unfold actualInverseCayley
  rw [← Matrix.mul_assoc,hc,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_inverse_cayley_is_source_inverse_formula
    (orthogonal : Matrix N N ℝ) (hunit : IsUnit (1+orthogonal)) :
    actualInverseCayley orthogonal=(1+orthogonal)⁻¹*(1-orthogonal) := by
  letI := hunit.invertible
  rw [← actual_inverse_cayley_left_denominator_identity orthogonal hunit]
  simp [← Matrix.mul_assoc]

theorem actual_inverse_cayley_is_skew_symmetric
    (orthogonal : Matrix N N ℝ) (horthogonal : orthogonalᵀ*orthogonal=1)
    (hunit : IsUnit (1+orthogonal)) :
    (actualInverseCayley orthogonal)ᵀ= -actualInverseCayley orthogonal := by
  letI := hunit.invertible
  letI := ((Matrix.isUnit_transpose (1+orthogonal)).mpr hunit).invertible
  have hr := actual_inverse_cayley_right_denominator_identity orthogonal hunit
  have ht : (1+orthogonal)ᵀ*(actualInverseCayley orthogonal)ᵀ=(1-orthogonal)ᵀ := by
    rw [← Matrix.transpose_mul,hr]
  have he : (1+orthogonal)ᵀ*
      ((actualInverseCayley orthogonal)ᵀ+actualInverseCayley orthogonal)*(1+orthogonal)=0 := by
    calc
      _ = ((1+orthogonal)ᵀ*(actualInverseCayley orthogonal)ᵀ)*(1+orthogonal)+
          (1+orthogonal)ᵀ*(actualInverseCayley orthogonal*(1+orthogonal)) := by
        noncomm_ring
      _ = (1-orthogonal)ᵀ*(1+orthogonal)+(1+orthogonal)ᵀ*(1-orthogonal) := by
        rw [ht,hr]
      _ = (1 : Matrix N N ℝ)+1-(orthogonalᵀ*orthogonal+orthogonalᵀ*orthogonal) := by
        rw [Matrix.transpose_sub,Matrix.transpose_add,Matrix.transpose_one]
        noncomm_ring
      _ = 0 := by rw [horthogonal]; abel
  have hz := congrArg (fun matrix : Matrix N N ℝ =>
    ((1+orthogonal)ᵀ)⁻¹*matrix*(1+orthogonal)⁻¹) he
  simp only [Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible,Matrix.mul_one] at hz
  rw [← Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.one_mul] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem actual_inverse_cayley_recovers_orthogonal
    (orthogonal : Matrix N N ℝ) (horthogonal : orthogonalᵀ*orthogonal=1)
    (hunit : IsUnit (1+orthogonal)) :
    SafeLearning.CompleteModulesCayley.actualCayley (actualInverseCayley orthogonal)=orthogonal := by
  have hskew := actual_inverse_cayley_is_skew_symmetric orthogonal horthogonal hunit
  letI := (SafeLearning.CompleteModulesCayley.actual_skew_cayley_denominator_is_invertible
    (actualInverseCayley orthogonal) hskew).invertible
  letI := hunit.invertible
  have hleft := actual_inverse_cayley_left_denominator_identity orthogonal hunit
  have hright := actual_inverse_cayley_right_denominator_identity orthogonal hunit
  have hrelation : orthogonal*(1+actualInverseCayley orthogonal)=
      1-actualInverseCayley orthogonal := by
    calc
      _ = (1+orthogonal)*actualInverseCayley orthogonal+orthogonal-
          actualInverseCayley orthogonal := by noncomm_ring
      _ = (1-orthogonal)+orthogonal-actualInverseCayley orthogonal := by rw [hleft]
      _ = _ := by noncomm_ring
  unfold SafeLearning.CompleteModulesCayley.actualCayley
  rw [← hrelation,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_inverse_cayley_recovers_skew
    (skew : Matrix N N ℝ) (hskew : skewᵀ= -skew) :
    actualInverseCayley (SafeLearning.CompleteModulesCayley.actualCayley skew)=skew := by
  let orthogonal := SafeLearning.CompleteModulesCayley.actualCayley skew
  have hunit := SafeLearning.CompleteModulesCayley.actual_cayley_plus_identity_is_invertible skew hskew
  have hsunit : IsUnit (1+orthogonal) := by simpa [orthogonal,add_comm] using hunit
  letI := hsunit.invertible
  letI := (SafeLearning.CompleteModulesCayley.actual_skew_cayley_denominator_is_invertible
    skew hskew).invertible
  have he : skew*(1+orthogonal)=1-orthogonal := by
    have hq : orthogonal*(1+skew)=1-skew := by
      simp [orthogonal,SafeLearning.CompleteModulesCayley.actualCayley,Matrix.mul_assoc]
    have hc : skew*orthogonal=orthogonal*skew := by
      apply Matrix.mul_left_injective_of_invertible (1+skew)
      have hx : skew*(1+skew)=(1+skew)*skew := by noncomm_ring
      calc
        _ = skew*(orthogonal*(1+skew)) := by simp only [Matrix.mul_assoc]
        _ = skew*(1-skew) := by rw [hq]
        _ = (1-skew)*skew := by noncomm_ring
        _ = (orthogonal*(1+skew))*skew := by rw [hq]
        _ = orthogonal*(skew*(1+skew)) := by rw [hx,Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    calc
      _ = skew+skew*orthogonal := by noncomm_ring
      _ = skew+orthogonal*skew := by rw [hc]
      _ = orthogonal*(1+skew)+skew-orthogonal := by noncomm_ring
      _ = (1-skew)+skew-orthogonal := by rw [hq]
      _ = _ := by noncomm_ring
  unfold actualInverseCayley
  rw [← he,Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem actual_cayley_preimage_is_unique
    (orthogonal skew : Matrix N N ℝ) (hskew : skewᵀ= -skew)
    (htransform : SafeLearning.CompleteModulesCayley.actualCayley skew=orthogonal) :
    skew=actualInverseCayley orthogonal := by
  rw [← htransform,actual_inverse_cayley_recovers_skew skew hskew]

theorem actual_orthogonal_denominator_invertible_iff_no_negative_one_eigenvector
    (orthogonal : Matrix N N ℝ) : IsUnit (1+orthogonal) ↔
    ∀ vector : N → ℝ, orthogonal*ᵥvector= -vector → vector=0 := by
  constructor
  · intro hunit vector heigen
    have hz : (1+orthogonal)*ᵥvector=0 := by simp [Matrix.add_mulVec,heigen]
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    exact hinj (by simpa using hz)
  · intro hnoeigen
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro left right hequal
    have hz : (1+orthogonal)*ᵥ(left-right)=0 := by
      simp [Matrix.mulVec_sub,hequal]
    have hsum : orthogonal*ᵥ(left-right)+(left-right)=0 := by
      simpa [Matrix.add_mulVec,add_comm] using hz
    have hdifference := hnoeigen (left-right) (eq_neg_of_add_eq_zero_left hsum)
    exact sub_eq_zero.mp hdifference

theorem actual_orthogonal_without_negative_one_has_unique_skew_preimage
    (orthogonal : Matrix N N ℝ) (horthogonal : orthogonalᵀ*orthogonal=1)
    (hnoeigen : ∀ vector : N → ℝ, orthogonal*ᵥvector= -vector → vector=0) :
    ∃! skew : Matrix N N ℝ, skewᵀ= -skew ∧
      SafeLearning.CompleteModulesCayley.actualCayley skew=orthogonal := by
  have hunit := (actual_orthogonal_denominator_invertible_iff_no_negative_one_eigenvector
    orthogonal).mpr hnoeigen
  refine ⟨actualInverseCayley orthogonal,
    ⟨actual_inverse_cayley_is_skew_symmetric orthogonal horthogonal hunit,
      actual_inverse_cayley_recovers_orthogonal orthogonal horthogonal hunit⟩,?_⟩
  intro skew hpreimage
  exact actual_cayley_preimage_is_unique orthogonal skew hpreimage.1 hpreimage.2

end SafeLearning.CompleteModulesCayleyInverse
