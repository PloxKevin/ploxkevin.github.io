import SafeLearning.CompleteFiniteCMDPSpectrum

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFiniteCMDPScaledSpectrum

open SafeLearning.CompleteFiniteCMDPSpectrum

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem actual_discount_scaled_stochastic_average_norm_bound
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (v : S → ℂ) :
    ‖((γ : ℂ) • complexMatrix K) *ᵥ v‖ ≤ γ * ‖v‖ := by
  rw [Matrix.smul_mulVec, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ0]
  exact mul_le_mul_of_nonneg_left (actual_stochastic_complex_average_norm_bound K hK0 hK1 v) hγ0

theorem actual_discount_scaled_stochastic_eigenvalue_norm_bound
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (z : ℂ) (v : S → ℂ) (hv : v ≠ 0)
    (he : ((γ : ℂ) • complexMatrix K) *ᵥ v = z • v) : ‖z‖ ≤ γ := by
  have hb := actual_discount_scaled_stochastic_average_norm_bound K hK0 hK1 γ hγ0 v
  rw [he,norm_smul] at hb
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

theorem actual_discount_scaled_stochastic_spectrum_norm_bound
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (z : ℂ)
    (hz : z ∈ spectrum ℂ ((γ : ℂ) • complexMatrix K)) : ‖z‖ ≤ γ := by
  have he : Module.End.HasEigenvalue (((γ : ℂ) • complexMatrix K).toLin') z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by rwa [Matrix.spectrum_toLin'])
  obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  exact actual_discount_scaled_stochastic_eigenvalue_norm_bound K hK0 hK1 γ hγ0 z v
    hv.2 (by simpa using hv.apply_eq_smul)

theorem actual_discount_scaled_stochastic_one_not_mem_spectrum
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (1 : ℂ) ∉ spectrum ℂ ((γ : ℂ) • complexMatrix K) := by
  intro h
  have hb := actual_discount_scaled_stochastic_spectrum_norm_bound K hK0 hK1 γ hγ0 1 h
  norm_num at hb
  linarith

theorem actual_complex_discounted_stochastic_matrix_is_unit
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit ((1 : Matrix S S ℂ) - (γ : ℂ) • complexMatrix K) := by
  classical
  by_contra h
  apply actual_discount_scaled_stochastic_one_not_mem_spectrum K hK0 hK1 γ hγ0 hγ1
  apply spectrum.mem_iff.mpr
  simpa only [map_one] using h

end SafeLearning.CompleteFiniteCMDPScaledSpectrum
