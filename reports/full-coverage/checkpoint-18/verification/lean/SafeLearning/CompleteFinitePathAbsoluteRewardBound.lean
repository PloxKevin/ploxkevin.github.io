import SafeLearning.CompleteFiniteTrajectoryReturns

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace SafeLearning.CompleteFinitePathAbsoluteRewardBound

open SafeLearning.CompleteFiniteTrajectoryReturns

variable {F Ω : Type*} [Fintype F] [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → F)

theorem actual_absolute_path_series_le_supplied_reward_bound
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : F → ℝ) (B : ℝ) (hB : ∀ z, |r z| ≤ B) (ω : Ω) :
    (∑' n : ℕ, γ ^ n * |r (Z n ω)|) ≤ B / (1 - γ) := by
  calc
    _ ≤ ∑' n : ℕ, γ ^ n * B :=
      (actual_path_reward_series_summable Z γ hγ0 hγ1 (fun z => |r z|) ω).tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_left (hB (Z n ω)) (pow_nonneg hγ0 n))
        ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B)
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]
      simp only [div_eq_mul_inv, mul_comm]

theorem actual_expected_absolute_path_series_le_supplied_reward_bound
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : F → ℝ) (B : ℝ) (hB : ∀ z, |r z| ≤ B) :
    (∫ ω, ∑' n : ℕ, γ ^ n * |r (Z n ω)| ∂μ) ≤ B / (1 - γ) := by
  have hint (n : ℕ) : Integrable (fun ω => γ ^ n * |r (Z n ω)|) μ :=
    actual_discounted_stage_integrable μ Z hZ γ (fun z => |r z|) n
  have hnorm := actual_discounted_integral_norm_summable μ Z hZ γ hγ0 hγ1
    (fun z => |r z|)
  have hsum := (hasSum_integral_of_summable_integral_norm hint hnorm).summable
  have hstage (n : ℕ) : (∫ ω, |r (Z n ω)| ∂μ) ≤ B := by
    calc
      _ ≤ ∫ _ : Ω, B ∂μ := integral_mono
        ((actual_stage_reward_integrable μ Z hZ r n).abs)
        (integrable_const B) (fun ω => hB (Z n ω))
      _ = _ := by simp
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  calc
    _ ≤ ∑' n : ℕ, γ ^ n * B := hsum.tsum_le_tsum (fun n => by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hstage n) (pow_nonneg hγ0 n))
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B)
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]
      simp only [div_eq_mul_inv, mul_comm]

end SafeLearning.CompleteFinitePathAbsoluteRewardBound
