import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace SafeLearning.CompleteFiniteTrajectoryReturns

variable {F Ω : Type*} [Fintype F] [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → F)

/-- The actual probability of a finite trajectory coordinate event. -/
def atomMass (n : ℕ) (z : F) : ℝ := μ.real {ω | Z n ω = z}

/-- Discounted occupancy defined directly from measurable trajectory events. -/
def pathOccupancy (γ : ℝ) (z : F) : ℝ :=
  (1 - γ) * ∑' n : ℕ, γ ^ n * atomMass μ Z n z

/-- Expected discounted return as an actual Bochner integral of the path series. -/
def pathReturn (γ : ℝ) (r : F → ℝ) : ℝ :=
  ∫ ω, ∑' n : ℕ, γ ^ n * r (Z n ω) ∂μ

theorem finite_reward_indicator_decomposition (r : F → ℝ) (n : ℕ) (ω : Ω) :
    r (Z n ω) = ∑ z, Set.indicator {ω | Z n ω = z} (fun _ => r z) ω := by
  classical
  simp [Set.indicator, eq_comm]

theorem actual_stage_reward_integrable
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z}) (r : F → ℝ) (n : ℕ) :
    Integrable (fun ω => r (Z n ω)) μ := by
  classical
  have h := integrable_finsetSum Finset.univ (fun z _ =>
    (integrable_const (μ := μ) (r z)).indicator (hZ n z))
  simpa only [← finite_reward_indicator_decomposition Z r n] using h

theorem actual_stage_reward_expectation
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z}) (r : F → ℝ) (n : ℕ) :
    (∫ ω, r (Z n ω) ∂μ) = ∑ z, atomMass μ Z n z * r z := by
  classical
  simp_rw [finite_reward_indicator_decomposition Z r n]
  rw [integral_finsetSum _ (fun z _ => (integrable_const (r z)).indicator (hZ n z))]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [atomMass, smul_eq_mul] using integral_indicator_const (r z) (hZ n z)

theorem finite_reward_absolute_bound (r : F → ℝ) (z : F) :
    |r z| ≤ ∑ y, |r y| :=
  Finset.single_le_sum (fun y _ => abs_nonneg (r y)) (Finset.mem_univ z)

theorem actual_path_reward_series_summable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : F → ℝ) (ω : Ω) : Summable (fun n : ℕ => γ ^ n * r (Z n ω)) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ z, |r z|))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 n)]
  exact mul_le_mul_of_nonneg_left (finite_reward_absolute_bound r (Z n ω))
    (pow_nonneg hγ0 n)

theorem actual_discounted_stage_integrable
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z}) (γ : ℝ) (r : F → ℝ) (n : ℕ) :
    Integrable (fun ω => γ ^ n * r (Z n ω)) μ :=
  (actual_stage_reward_integrable μ Z hZ r n).const_mul (γ ^ n)

theorem actual_discounted_integral_norm_summable
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : F → ℝ) :
    Summable (fun n : ℕ => ∫ ω, ‖γ ^ n * r (Z n ω)‖ ∂μ) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => ?_) ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ z, |r z|))
  have h := integral_mono_ae
    (actual_discounted_stage_integrable μ Z hZ γ r n).norm
    (integrable_const (γ ^ n * ∑ z, |r z|))
    (Filter.Eventually.of_forall fun ω => ?_)
  · simpa using h
  · change ‖γ ^ n * r (Z n ω)‖ ≤ γ ^ n * ∑ z, |r z|
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 n)]
    exact mul_le_mul_of_nonneg_left (finite_reward_absolute_bound r (Z n ω))
      (pow_nonneg hγ0 n)

theorem actual_path_integral_series_interchange
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : F → ℝ) :
    pathReturn μ Z γ r = ∑' n : ℕ, γ ^ n * ∫ ω, r (Z n ω) ∂μ := by
  unfold pathReturn
  rw [← integral_tsum_of_summable_integral_norm
    (actual_discounted_stage_integrable μ Z hZ γ r)
    (actual_discounted_integral_norm_summable μ Z hZ γ hγ0 hγ1 r)]
  simp_rw [integral_const_mul]

theorem actual_atom_discounted_series_summable
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (z : F) :
    Summable (fun n : ℕ => γ ^ n * atomMass μ Z n z) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ0 n) measureReal_nonneg)
    (fun n => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 n) measureReal_le_one

theorem actual_path_occupancy_return_identity
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : F → ℝ) :
    (∑ z, pathOccupancy μ Z γ z * r z) = (1 - γ) * pathReturn μ Z γ r := by
  classical
  rw [actual_path_integral_series_interchange μ Z hZ γ hγ0 hγ1 r]
  simp_rw [actual_stage_reward_expectation μ Z hZ r]
  simp only [pathOccupancy, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp_rw [← tsum_mul_right]
  simp only [Finset.mul_sum, mul_assoc]
  simpa only [mul_assoc] using (Summable.tsum_finsetSum (s := Finset.univ) (fun z _ =>
    (actual_atom_discounted_series_summable μ Z γ hγ0 hγ1 z).mul_right (r z))).symm

theorem actual_path_return_linear_functional
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : F → ℝ) :
    pathReturn μ Z γ r = (∑ z, pathOccupancy μ Z γ z * r z) / (1 - γ) := by
  rw [actual_path_occupancy_return_identity μ Z hZ γ hγ0 hγ1 r]
  field_simp [ne_of_gt (sub_pos.mpr hγ1)]

theorem actual_coordinate_event_probabilities_sum_one
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z}) (n : ℕ) :
    ∑ z, atomMass μ Z n z = 1 := by
  have h := actual_stage_reward_expectation μ Z hZ (fun _ => 1) n
  simpa using h.symm

theorem actual_path_occupancy_nonnegative
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (z : F) :
    0 ≤ pathOccupancy μ Z γ z := by
  exact mul_nonneg (sub_nonneg.mpr hγ1.le)
    (tsum_nonneg fun n => mul_nonneg (pow_nonneg hγ0 n) measureReal_nonneg)

theorem actual_path_occupancy_total_mass
    (hZ : ∀ n z, MeasurableSet {ω | Z n ω = z})
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑ z, pathOccupancy μ Z γ z = 1 := by
  have h := actual_path_occupancy_return_identity μ Z hZ γ hγ0 hγ1 (fun _ => 1)
  simp only [mul_one] at h
  rw [h, actual_path_integral_series_interchange μ Z hZ γ hγ0 hγ1]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [tsum_geometric_of_lt_one hγ0 hγ1]
  exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hγ1))

end SafeLearning.CompleteFiniteTrajectoryReturns
