import SafeLearning.CompleteCoreFilippovEulerConstruction31

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
namespace SafeLearning.CompleteCoreFilippovPolygonalConstruction32

def ramp (h : ℝ) (k : ℕ) (t : ℝ) : ℝ := max 0 (min h (t - (k : ℝ) * h))

theorem actual_clamp_identity (h u : ℝ) (hh : 0 ≤ h) :
    max 0 (min h u) = max 0 u - max 0 (u - h) := by
  by_cases hu : u ≤ 0
  · rw [max_eq_left (le_trans (min_le_right _ _) hu), max_eq_left hu,
      max_eq_left (by linarith : u - h ≤ 0)]
    ring
  · have hu0 : 0 ≤ u := by linarith
    by_cases huh : u ≤ h
    · rw [min_eq_right huh, max_eq_right hu0, max_eq_left (by linarith : u - h ≤ 0)]
      ring
    · rw [min_eq_left (by linarith : h ≤ u), max_eq_right hh, max_eq_right hu0,
        max_eq_right (by linarith : 0 ≤ u - h)]
      ring

theorem actual_ramp_difference (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (t : ℝ) :
    ramp h k t = max 0 (t - (k : ℝ) * h) - max 0 (t - ((k + 1 : ℕ) : ℝ) * h) := by
  rw [ramp, actual_clamp_identity h _ hh]
  congr 2
  push_cast
  ring

theorem actual_ramp_nonnegative (h : ℝ) (k : ℕ) (t : ℝ) : 0 ≤ ramp h k t :=
  le_max_left _ _

theorem actual_ramp_zero (h : ℝ) (hh : 0 ≤ h) (k : ℕ) : ramp h k 0 = 0 := by
  unfold ramp
  apply max_eq_left
  exact le_trans (min_le_right _ _) (sub_nonpos.mpr (mul_nonneg (Nat.cast_nonneg k) hh))

theorem actual_ramp_monotone (h : ℝ) (k : ℕ) {s t : ℝ} (hst : s ≤ t) :
    ramp h k s ≤ ramp h k t :=
  max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right hst _))

theorem actual_ramp_sum (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range n, ramp h k t) = max 0 t - max 0 (t - (n : ℝ) * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, actual_ramp_difference h hh n t]
    ring

theorem actual_ramp_sum_bound (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range n, ramp h k t) ≤ t := by
  rw [actual_ramp_sum h hh, max_eq_right ht]
  have hp := le_max_left 0 (t - (n : ℝ) * h)
  linarith

theorem actual_ramp_continuous (h : ℝ) (k : ℕ) : Continuous (ramp h k) := by
  unfold ramp
  fun_prop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [ProperSpace E]
open SafeLearning.CompleteCoreFilippovVelocityCompactness30

/-- A continuous polygonal path whose slopes use actual chosen essential velocities. -/
def polygonal (μ : Measure E) [μ.IsOpenPosMeasure] (F : E → E) (M : ℝ)
    (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (x₀ : E) (n : ℕ) (t : ℝ) : E :=
  x₀ + ∑ k ∈ Finset.range n,
    ramp h k t • chosenVelocity μ F M hF (eulerNodes μ F M hF h x₀ k)

theorem actual_polygonal_initial (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (hh : 0 ≤ h)
    (x₀ : E) (n : ℕ) : polygonal μ F M hF h x₀ n 0 = x₀ := by
  simp [polygonal, actual_ramp_zero h hh]

theorem actual_polygonal_continuous (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ)
    (x₀ : E) (n : ℕ) : Continuous (polygonal μ F M hF h x₀ n) := by
  unfold polygonal
  have hr : ∀ k : ℕ, Continuous (ramp h k) := actual_ramp_continuous h
  fun_prop

theorem actual_polygonal_radius_bound (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (hh : 0 ≤ h)
    (x₀ : E) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖polygonal μ F M hF h x₀ n t - x₀‖ ≤ t * M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (F (0 : E))) (hF 0)
  simp only [polygonal, add_sub_cancel_left]
  calc
    ‖∑ k ∈ Finset.range n, ramp h k t • chosenVelocity μ F M hF
        (eulerNodes μ F M hF h x₀ k)‖
        ≤ ∑ k ∈ Finset.range n, ‖ramp h k t • chosenVelocity μ F M hF
          (eulerNodes μ F M hF h x₀ k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ramp h k t * M := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (actual_ramp_nonnegative h k t)]
      exact mul_le_mul_of_nonneg_left (chosenVelocity_norm_bound μ F M hF _) (actual_ramp_nonnegative h k t)
    _ = (∑ k ∈ Finset.range n, ramp h k t) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ t * M := mul_le_mul_of_nonneg_right (actual_ramp_sum_bound h hh n t ht) hM

theorem actual_ramp_sum_as_cap (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range n, ramp h k t) = min ((n : ℝ) * h) t := by
  rw [actual_ramp_sum h hh, max_eq_right ht]
  by_cases htn : t ≤ (n : ℝ) * h
  · rw [max_eq_left (sub_nonpos.mpr htn), min_eq_right htn]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ t - (n : ℝ) * h),
      min_eq_left (by linarith : (n : ℝ) * h ≤ t)]
    ring

theorem actual_ramp_sum_increment_bound (h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∑ k ∈ Finset.range n, ramp h k t) - (∑ k ∈ Finset.range n, ramp h k s) ≤ t - s := by
  rw [actual_ramp_sum_as_cap h hh n t (le_trans hs hst), actual_ramp_sum_as_cap h hh n s hs]
  by_cases hsn : s ≤ (n : ℝ) * h
  · rw [min_eq_right hsn]
    exact sub_le_sub_right (min_le_right _ _) s
  · have hns : (n : ℝ) * h ≤ s := by linarith
    rw [min_eq_left hns, min_eq_left (le_trans hns hst)]
    linarith

theorem actual_polygonal_uniform_increment_bound (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (hh : 0 ≤ h)
    (x₀ : E) (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖polygonal μ F M hF h x₀ n t - polygonal μ F M hF h x₀ n s‖ ≤ (t - s) * M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg (F (0 : E))) (hF 0)
  have hid : polygonal μ F M hF h x₀ n t - polygonal μ F M hF h x₀ n s =
      ∑ k ∈ Finset.range n, (ramp h k t - ramp h k s) •
        chosenVelocity μ F M hF (eulerNodes μ F M hF h x₀ k) := by
    simp [polygonal, sub_smul, Finset.sum_sub_distrib]
  rw [hid]
  calc
    ‖∑ k ∈ Finset.range n, (ramp h k t - ramp h k s) • chosenVelocity μ F M hF
        (eulerNodes μ F M hF h x₀ k)‖
        ≤ ∑ k ∈ Finset.range n, ‖(ramp h k t - ramp h k s) • chosenVelocity μ F M hF
          (eulerNodes μ F M hF h x₀ k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (ramp h k t - ramp h k s) * M := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 ≤ ramp h k t - ramp h k s := sub_nonneg.mpr (actual_ramp_monotone h k hst)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_left (chosenVelocity_norm_bound μ F M hF _) hk0
    _ = ((∑ k ∈ Finset.range n, ramp h k t) - (∑ k ∈ Finset.range n, ramp h k s)) * M := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    _ ≤ (t - s) * M := mul_le_mul_of_nonneg_right (actual_ramp_sum_increment_bound h hh n s t hs hst) hM

end SafeLearning.CompleteCoreFilippovPolygonalConstruction32
