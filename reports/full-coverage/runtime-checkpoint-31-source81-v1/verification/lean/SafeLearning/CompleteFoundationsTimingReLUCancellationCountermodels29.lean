import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic

namespace SafeLearning.FoundationTimingReLUCancellation28

/-- A differentiable timing can stop everywhere while satisfying nonnegative speed. -/
theorem constant_timing_derivative_nonnegative (t : ℝ) :
    0 ≤ deriv (fun (_ : ℝ) => (0 : ℝ)) t := by
  simp

/-- Merely imposing nonnegative speed does not preserve the entire path image. -/
theorem constant_timing_misses_full_identity_path :
    ((fun (_ : ℝ) => (0 : ℝ)) '' Set.Icc (0 : ℝ) 1) ≠
      ((fun (s : ℝ) => s) '' Set.Icc (0 : ℝ) 1) := by
  intro h
  have h1 : (1 : ℝ) ∈ (fun (_ : ℝ) => (0 : ℝ)) '' Set.Icc (0 : ℝ) 1 := by
    rw [h]
    exact ⟨1, by constructor <;> norm_num, rfl⟩
  rcases h1 with ⟨t, ht, he⟩
  norm_num at he

/-- Two identical ReLU neurons with output weights 1 and -1 give a smooth constant. -/
theorem actual_relu_switch_cancellation_differentiable (x : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => max t 0 - max t 0) x := by
  simpa using (differentiableAt_const (c := (0 : ℝ)))

/-- Covering the entire parameter interval is the separate condition for full image equality. -/
theorem entire_timing_coverage_preserves_path_image
    {E : Type*} (q : ℝ → E) (s : ℝ → ℝ) (T : Set ℝ)
    (hinto : Set.MapsTo s T (Set.Icc (0 : ℝ) 1))
    (hcover : Set.SurjOn s T (Set.Icc (0 : ℝ) 1)) :
    (q ∘ s) '' T = q '' Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨s t, hinto ht, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    rcases hcover hz with ⟨t, ht, hst⟩
    exact ⟨t, ht, by simp [Function.comp_apply, hst]⟩

end SafeLearning.FoundationTimingReLUCancellation28
