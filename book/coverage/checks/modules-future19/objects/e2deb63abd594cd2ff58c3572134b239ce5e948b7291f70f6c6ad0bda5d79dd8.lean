import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesGPConfidenceBands

def band (mean multiplier variance : ℝ) : Set ℝ :=
  Set.Icc (mean-multiplier*Real.sqrt variance) (mean+multiplier*Real.sqrt variance)
def intervalWidth (mean multiplier variance : ℝ) : ℝ :=
  (mean+multiplier*Real.sqrt variance)-(mean-multiplier*Real.sqrt variance)
def cumulativeBands (initial : Set ℝ) (Q : ℕ → Set ℝ) : ℕ → Set ℝ
  | 0 => initial
  | n+1 => cumulativeBands initial Q n ∩ Q n

theorem actual_gaussian_confidence_band_has_width_twice_the_multiplier_times_standard_deviation
    (mean multiplier variance : ℝ) :
    intervalWidth mean multiplier variance=2*multiplier*Real.sqrt variance := by
  unfold intervalWidth
  ring

theorem actual_decreasing_posterior_variance_cannot_increase_confidence_width_at_fixed_multiplier
    (oldMean newMean multiplier oldVariance newVariance : ℝ)
    (hMultiplier : 0 ≤ multiplier) (hVariance : newVariance ≤ oldVariance) :
    intervalWidth newMean multiplier newVariance ≤ intervalWidth oldMean multiplier oldVariance := by
  simp only [actual_gaussian_confidence_band_has_width_twice_the_multiplier_times_standard_deviation]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVariance) (mul_nonneg (by norm_num) hMultiplier)

theorem actual_gaussian_confidence_band_is_a_genuine_nonempty_closed_interval
    (mean multiplier variance : ℝ) (hMultiplier : 0 ≤ multiplier) :
    mean ∈ band mean multiplier variance ∧ (band mean multiplier variance).Nonempty := by
  have hh : 0 ≤ multiplier*Real.sqrt variance := mul_nonneg hMultiplier (Real.sqrt_nonneg _)
  have hm : mean ∈ band mean multiplier variance := by
    constructor  <;> linarith
  exact ⟨hm,⟨mean,hm⟩⟩

theorem actual_safeopt_intersection_update_is_nested_at_every_step
    (initial : Set ℝ) (Q : ℕ → Set ℝ) (n : ℕ) :
    cumulativeBands initial Q (n+1) ⊆ cumulativeBands initial Q n := by
  exact Set.inter_subset_left

theorem actual_safeopt_intersections_never_widen_even_if_the_multiplier_or_mean_changes
    (initial : Set ℝ) (Q : ℕ → Set ℝ) {m n : ℕ} (hmn : m ≤ n) :
    cumulativeBands initial Q n ⊆ cumulativeBands initial Q m := by
  induction n,hmn using Nat.le_induction with
  | base => exact Set.Subset.refl _
  | succ n hmn ih =>
    exact (actual_safeopt_intersection_update_is_nested_at_every_step initial Q n).trans ih

theorem actual_simultaneous_truth_event_preserves_truth_in_every_intersection
    (initial : Set ℝ) (Q : ℕ → Set ℝ) (truth : ℝ)
    (hInitial : truth ∈ initial) (hQ : ∀ n,truth ∈ Q n) :
    ∀ n,truth ∈ cumulativeBands initial Q n := by
  intro n
  induction n with
  | zero => exact hInitial
  | succ n ih => exact ⟨ih,hQ n⟩

theorem actual_increasing_multiplier_can_widen_raw_bands_despite_unchanged_variance :
    band 0 1 1  ⊂  band 0 2 1 ∧
      intervalWidth 0 1 1 < intervalWidth 0 2 1 := by
  constructor
  · apply Set.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      norm_num [band] at hx ⊢
      constructor <;> linarith [hx.1,hx.2]
    · intro he
      have h : (2 : ℝ) ∈ band 0 2 1 := by norm_num [band]
      rw [←he] at h
      norm_num [band] at h
  · norm_num [intervalWidth]

end SafeLearning.CompleteModulesGPConfidenceBands
