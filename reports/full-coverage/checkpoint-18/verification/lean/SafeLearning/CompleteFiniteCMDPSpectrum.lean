import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace SafeLearning.CompleteFiniteCMDPSpectrum

variable {S : Type*} [Fintype S] [DecidableEq S]

def complexMatrix (K : Matrix S S ℝ) : Matrix S S ℂ := fun s t => (K s t : ℂ)

theorem actual_stochastic_complex_average_norm_bound
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (v : S → ℂ) : ‖complexMatrix K *ᵥ v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro s
  change ‖∑ t, (K s t : ℂ) * v t‖ ≤ ‖v‖
  calc
    _ ≤ ∑ t, ‖(K s t : ℂ) * v t‖ := norm_sum_le _ _
    _ = ∑ t, K s t * ‖v t‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 _ _)]
    _ ≤ ∑ t, K s t * ‖v‖ := Finset.sum_le_sum
      (fun t _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm v t) (hK0 s t))
    _ = ‖v‖ := by rw [← Finset.sum_mul, hK1, one_mul]

theorem actual_every_stochastic_complex_eigenvalue_has_norm_at_most_one
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (z : ℂ) (v : S → ℂ) (hv : v ≠ 0)
    (he : complexMatrix K *ᵥ v = z • v) : ‖z‖ ≤ 1 := by
  have hb := actual_stochastic_complex_average_norm_bound K hK0 hK1 v
  rw [he, norm_smul] at hb
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

theorem actual_stochastic_matrix_spectrum_norm_at_most_one
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (z : ℂ) (hz : z ∈ spectrum ℂ (complexMatrix K)) : ‖z‖ ≤ 1 := by
  have he : Module.End.HasEigenvalue (complexMatrix K).toLin' z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
      rwa [Matrix.spectrum_toLin'])
  obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  exact actual_every_stochastic_complex_eigenvalue_has_norm_at_most_one K hK0 hK1 z v
    hv.2 (by simpa using hv.apply_eq_smul)

theorem actual_stochastic_matrix_has_literal_one_eigenvector
    [Nonempty S] (K : Matrix S S ℝ) (hK1 : ∀ s, ∑ t, K s t = 1) :
    (fun _ : S => (1 : ℂ)) ≠ 0 ∧
      complexMatrix K *ᵥ (fun _ => (1 : ℂ)) = (fun _ => (1 : ℂ)) := by
  constructor
  · intro he
    have h := congrArg (fun v : S → ℂ => v (Classical.choice ‹Nonempty S›)) he
    norm_num at h
  · ext s
    change (∑ t, (K s t : ℂ) * 1) = 1
    simp only [mul_one]
    exact_mod_cast hK1 s

theorem actual_stochastic_matrix_one_mem_spectrum
    [Nonempty S] (K : Matrix S S ℝ) (hK1 : ∀ s, ∑ t, K s t = 1) :
    (1 : ℂ) ∈ spectrum ℂ (complexMatrix K) := by
  have h := actual_stochastic_matrix_has_literal_one_eigenvector K hK1
  have he : Module.End.HasEigenvector (complexMatrix K).toLin' 1 (fun _ => (1 : ℂ)) := by
    apply Module.End.hasEigenvector_iff.mpr
    exact ⟨by simpa using h.2, h.1⟩
  have hs := (Module.End.hasEigenvalue_of_hasEigenvector he).mem_spectrum
  rwa [Matrix.spectrum_toLin'] at hs

theorem actual_stochastic_matrix_standard_spectral_radius_one
    [Nonempty S] (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1) :
    spectralRadius ℂ (complexMatrix K) = 1 := by
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply ENNReal.coe_le_coe.mpr
    exact_mod_cast actual_stochastic_matrix_spectrum_norm_at_most_one K hK0 hK1 z hz
  · have h := actual_stochastic_matrix_one_mem_spectrum K hK1
    exact le_iSup_of_le (1 : ℂ) (le_iSup_of_le h (by simp))

end SafeLearning.CompleteFiniteCMDPSpectrum
