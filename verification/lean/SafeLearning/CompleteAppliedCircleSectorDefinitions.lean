import SafeLearning.CompleteAppliedCircleConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCircleSectorDefinitions
open CompleteAppliedCircleFeedback CompleteAppliedCircleConsequences

theorem actual_literal_product_sector_iff_zero_and_radial_sector
    (kappa : ℝ) (hk : 0 ≤ kappa) (phi : ℝ → ℝ) :
    (∀ z : ℝ, phi z * (phi z - kappa*z) ≤ 0) ↔
      phi 0 = 0 ∧ ∀ z : ℝ, 0 ≤ z*phi z ∧ z*phi z ≤ kappa*z^2 := by
  constructor
  · intro h
    have hz : phi 0 = 0 := by
      have h0 := h 0
      nlinarith [sq_nonneg (phi 0)]
    refine ⟨hz, ?_⟩
    intro z
    by_cases hk0 : kappa = 0
    · have hp : phi z = 0 := by
        have hh := h z
        rw [hk0] at hh
        nlinarith [sq_nonneg (phi z)]
      simp [hp, hk0]
    · have hkp : 0 < kappa := lt_of_le_of_ne hk (Ne.symm hk0)
      rcases mul_nonpos_iff.mp (h z) with ⟨hp, hsub⟩ | ⟨hp, hsub⟩
      · have hzp : 0 ≤ z := by nlinarith
        refine ⟨mul_nonneg hzp hp, ?_⟩
        have hh := mul_le_mul_of_nonneg_left (show phi z ≤ kappa*z by linarith) hzp
        nlinarith
      · have hzp : z ≤ 0 := by nlinarith
        refine ⟨mul_nonneg_of_nonpos_of_nonpos hzp hp, ?_⟩
        have hh := mul_le_mul_of_nonpos_left (show kappa*z ≤ phi z by linarith) hzp
        nlinarith
  · rintro ⟨hz, h⟩ z
    rcases lt_trichotomy z 0 with hzn | hzz | hzp
    · have hp : phi z ≤ 0 := by nlinarith [(h z).1]
      have hl : kappa*z ≤ phi z := by nlinarith [(h z).2]
      exact mul_nonpos_of_nonpos_of_nonneg hp (by linarith)
    · subst z
      simp [hz]
    · have hp : 0 ≤ phi z := by nlinarith [(h z).1]
      have hu : phi z ≤ kappa*z := by nlinarith [(h z).2]
      exact mul_nonpos_of_nonneg_of_nonpos hp (by linarith)

theorem actual_scaled_tanh_satisfies_the_literal_product_sector
    (kappa : ℝ) (hk : 0 ≤ kappa) :
    ∀ z : ℝ, sourceNonlinearity kappa z *
      (sourceNonlinearity kappa z - kappa*z) ≤ 0 := by
  apply (actual_literal_product_sector_iff_zero_and_radial_sector kappa hk _).mpr
  refine ⟨by simp [sourceNonlinearity], ?_⟩
  intro z
  exact (actual_scaled_tanh_has_the_stated_derivative_and_sector kappa hk z).2.2.2

theorem actual_every_literal_time_varying_sector_feedback_is_stable_and_decays
    (kappa : ℝ) (hk : 0 ≤ kappa) (hk3 : kappa < 3) (phi : ℕ → ℝ → ℝ)
    (hsector : ∀ n z, phi n z * (phi n z - kappa*z) ≤ 0) :
    (∀ initial : ℝ, Tendsto (sectorTrajectory phi initial) atTop (𝓝 0)) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ initial : ℝ, |initial| < delta → ∀ n,
          |sectorTrajectory phi initial n| < epsilon := by
  have h (n : ℕ) :=
    (actual_literal_product_sector_iff_zero_and_radial_sector kappa hk (phi n)).mp
      (hsector n)
  exact ⟨fun initial => actual_every_time_varying_sector_trajectory_tends_to_zero
    kappa hk hk3 phi (fun n => (h n).1) (fun n => (h n).2) initial,
    actual_sector_feedback_is_lyapunov_stable kappa hk hk3 phi
      (fun n => (h n).1) (fun n => (h n).2)⟩

end SafeLearning.CompleteAppliedCircleSectorDefinitions
