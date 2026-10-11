import Mathlib

namespace SafeLearning.CompleteFoundationsIsometricEmbeddings26

theorem actual_isometric_embedding_iff_norm_distance
    {D E : Type*} [PseudoMetricSpace D] [NormedAddCommGroup E] (f : D → E) :
    Isometry f ↔ ∀ x y, ‖f x - f y‖ = dist x y := by
  simpa only [dist_eq_norm] using (isometry_iff_dist_eq (f := f))

theorem actual_unit_direction_affine_line_preserves_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ u : E) (hu : ‖u‖ = 1) (s t : ℝ) :
    dist (x₀ + s • u) (x₀ + t • u) = dist s t := by
  have hsub : (x₀ + s • u) - (x₀ + t • u) = (s - t) • u := by module
  rw [dist_eq_norm, hsub, norm_smul, hu, mul_one, dist_eq_norm]

theorem actual_unit_direction_affine_line_isometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ u : E) (hu : ‖u‖ = 1) :
    Isometry (fun t : ℝ => x₀ + t • u) := by
  apply Isometry.of_dist_eq
  exact actual_unit_direction_affine_line_preserves_distance x₀ u hu

theorem actual_distance_kernel_invariant_under_isometry
    {D E K : Type*} [PseudoMetricSpace D] [PseudoMetricSpace E]
    (f : D → E) (hf : Isometry f) (κ : ℝ → K) (x y : D) :
    κ (dist (f x) (f y)) = κ (dist x y) := by
  rw [hf.dist_eq]

theorem actual_norm_distance_kernel_invariant_under_embedding
    {D E K : Type*} [PseudoMetricSpace D] [NormedAddCommGroup E]
    (f : D → E) (hf : Isometry f) (κ : ℝ → K) (x y : D) :
    κ (‖f x - f y‖) = κ (dist x y) := by
  rw [← dist_eq_norm, hf.dist_eq]

theorem actual_square_embedding_is_nonisometric_and_nonadditive :
    ¬ Isometry (fun t : ℝ => t ^ 2) ∧
      ((1 + 1 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) := by
  constructor
  · intro h
    have hp := h.dist_eq (0 : ℝ) 2
    norm_num [Real.dist_eq] at hp
  · norm_num

theorem actual_square_embedding_changes_threshold_proximity :
    dist (0 : ℝ) 2 ≤ 3 ∧ ¬ (dist ((0 : ℝ) ^ 2) ((2 : ℝ) ^ 2) ≤ 3) := by
  norm_num [Real.dist_eq]

end SafeLearning.CompleteFoundationsIsometricEmbeddings26
