import SafeLearning.CompleteFoundationsNormDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SafeLearning.CompleteFoundationsNormExercises

open Set
open scoped BigOperators RealInnerProductSpace
open CompleteFoundationsNormDuality

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem actual_infinity_norm_at_most_euclidean_norm (x : n → ℝ) : ‖x‖ ≤ l2Norm x := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (euclidean x))).mpr
  intro i
  exact PiLp.norm_apply_le (euclidean x) i

theorem actual_euclidean_norm_at_most_one_norm (x : n → ℝ) : l2Norm x ≤ l1Norm x := by
  have he : euclidean x = ∑ i : n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ n) := by
    ext j
    simp [euclidean, PiLp.single_apply]
  calc
    l2Norm x = ‖∑ i : n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ n)‖ := by
      rw [l2Norm, he]
    _ ≤ ∑ i : n, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℝ n)‖ := norm_sum_le _ _
    _ = ∑ i : n, |x i| := by simp [Real.norm_eq_abs]
    _ = l1Norm x := (actual_l1_norm_is_sum_absolute_values x).symm

theorem actual_one_norm_at_most_dimension_factor_euclidean_norm (x : n → ℝ) :
    l1Norm x ≤ Real.sqrt (Fintype.card n) * l2Norm x := by
  have habs : ‖euclidean (fun i => |x i|)‖ = l2Norm x := by
    simp [euclidean, l2Norm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have hone : ‖euclidean (fun _ : n => (1 : ℝ))‖ = Real.sqrt (Fintype.card n) := by
    simpa only [l2Norm, mul_one] using
      (actual_constant_vector_attains_dimension_conversion (n := n) 1 (by norm_num))
  have hip : ⟪euclidean (fun i => |x i|), euclidean (fun _ : n => (1 : ℝ))⟫ = l1Norm x := by
    rw [actual_euclidean_pairing_is_dot, actual_l1_norm_is_sum_absolute_values]
    simp [dotProduct]
  have hh := abs_real_inner_le_norm (euclidean (fun i => |x i|))
    (euclidean (fun _ : n => (1 : ℝ)))
  rw [hip, abs_of_nonneg (show 0 ≤ l1Norm x from norm_nonneg _), habs, hone] at hh
  simpa only [mul_comm] using hh

def sourceWeight : Fin 3 → ℝ := ![1, -2, 2]

theorem actual_source_three_norms :
    l1Norm sourceWeight = 5 ∧ l2Norm sourceWeight = 3 ∧ ‖sourceWeight‖ = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [actual_l1_norm_is_sum_absolute_values, sourceWeight, Fin.sum_univ_succ]
  · have hs : l2Norm sourceWeight ^ 2 = 9 := by
      norm_num [actual_l2_norm_squared, sourceWeight, Fin.sum_univ_succ]
    have hn : 0 ≤ l2Norm sourceWeight := norm_nonneg _
    nlinarith
  · apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      fin_cases i <;> norm_num [sourceWeight]
    · simpa [sourceWeight] using norm_le_pi_norm sourceWeight (1 : Fin 3)

theorem actual_source_norm_comparisons_and_rounding :
    (2 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 5 ∧ (5 : ℝ) ≤ Real.sqrt 3 * 3 ∧
    |Real.sqrt 3 * 3 - 5.20| < 0.005 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  refine ⟨by norm_num, by norm_num, by nlinarith, ?_⟩
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem actual_source_infinity_ball_maximum :
    IsGreatest ((fun x : Fin 3 → ℝ => sourceWeight ⬝ᵥ x) '' {x | ‖x‖ ≤ 1 / 10}) (1 / 2) := by
  simpa only [actual_source_three_norms.1, show (1 / 10 : ℝ) * 5 = 1 / 2 by norm_num]
    using actual_infinity_ball_support_maximum sourceWeight (1 / 10) (by norm_num)

theorem actual_source_infinity_maximizing_point :
    ‖(![1 / 10, -1 / 10, 1 / 10] : Fin 3 → ℝ)‖ ≤ 1 / 10 ∧
    sourceWeight ⬝ᵥ ![1 / 10, -1 / 10, 1 / 10] = 1 / 2 := by
  have he : (fun i => (1 / 10 : ℝ) * Real.sign (sourceWeight i)) =
      (![1 / 10, -1 / 10, 1 / 10] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> norm_num [sourceWeight, Real.sign]
  have hh := actual_sign_vector_attains_infinity_ball sourceWeight (1 / 10) (by norm_num)
  rw [he, actual_source_three_norms.1] at hh
  norm_num at hh ⊢
  exact hh

theorem actual_source_euclidean_ball_maximum :
    IsGreatest ((fun x : Fin 3 → ℝ => sourceWeight ⬝ᵥ x) '' {x | l2Norm x ≤ 1 / 10}) (3 / 10) := by
  simpa only [actual_source_three_norms.2.1, show (1 / 10 : ℝ) * 3 = 3 / 10 by norm_num]
    using actual_euclidean_ball_support_maximum sourceWeight (1 / 10) (by norm_num)

theorem actual_source_euclidean_maximizing_point :
    l2Norm ((1 / 10 / 3 : ℝ) • sourceWeight) = 1 / 10 ∧
    sourceWeight ⬝ᵥ ((1 / 10 / 3 : ℝ) • sourceWeight) = 3 / 10 := by
  constructor
  · have he : euclidean ((1 / 10 / 3 : ℝ) • sourceWeight) =
        (1 / 10 / 3 : ℝ) • euclidean sourceWeight := by rfl
    rw [l2Norm, he, norm_smul]
    change ‖(1 / 10 / 3 : ℝ)‖ * l2Norm sourceWeight = _
    rw [actual_source_three_norms.2.1]
    norm_num
  · norm_num [sourceWeight, dotProduct, Fin.sum_univ_succ]

theorem actual_source_one_ball_maximum :
    IsGreatest ((fun x : Fin 3 → ℝ => sourceWeight ⬝ᵥ x) '' {x | l1Norm x ≤ 1 / 10}) (1 / 5) := by
  simpa only [actual_source_three_norms.2.2, show (1 / 10 : ℝ) * 2 = 1 / 5 by norm_num]
    using actual_one_ball_support_maximum_without_supplied_coordinate
      sourceWeight (1 / 10) (by norm_num)

theorem actual_source_both_one_norm_maximizing_points :
    l1Norm (![0, -1 / 10, 0] : Fin 3 → ℝ) = 1 / 10 ∧
    sourceWeight ⬝ᵥ ![0, -1 / 10, 0] = 1 / 5 ∧
    l1Norm (![0, 0, 1 / 10] : Fin 3 → ℝ) = 1 / 10 ∧
    sourceWeight ⬝ᵥ ![0, 0, 1 / 10] = 1 / 5 := by
  norm_num [actual_l1_norm_is_sum_absolute_values, sourceWeight, dotProduct, Fin.sum_univ_succ]

theorem actual_pixel_dimension_square_root : Real.sqrt (784 : ℝ) = 28 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 784)
  have hp := Real.sqrt_nonneg (784 : ℝ)
  nlinarith

theorem actual_source_pixel_ball_inclusion (ε : ℝ) (hε : 0 ≤ ε) :
    {x : Fin 784 → ℝ | ‖x‖ ≤ ε} ⊆ {x | l2Norm x ≤ 28 * ε} := by
  intro x hx
  have hh := actual_infinity_ball_in_euclidean_ball x ε hε hx
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hh
  exact hh

theorem actual_source_classifier_radius_conversion {Label : Type*}
    (classifier : (Fin 784 → ℝ) → Label) (center : Fin 784 → ℝ) (radius ε : ℝ)
    (hε : 0 ≤ ε) (hconvert : 28 * ε ≤ radius)
    (hcertificate : ∀ x, l2Norm (x - center) ≤ radius → classifier x = classifier center) :
    ∀ x, ‖x - center‖ ≤ ε → classifier x = classifier center := by
  intro x hx
  exact hcertificate x ((actual_source_pixel_ball_inclusion ε hε hx).trans hconvert)

theorem actual_pixel_conversion_is_attained (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(fun _ : Fin 784 => ε)‖ = ε ∧ l2Norm (fun _ : Fin 784 => ε) = 28 * ε := by
  constructor
  · apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hε).mpr
      intro i
      simp only [Real.norm_eq_abs, abs_of_nonneg hε, le_refl]
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hε] using
        norm_le_pi_norm (fun _ : Fin 784 => ε) (0 : Fin 784)
  · have hh := actual_constant_vector_attains_dimension_conversion (n := Fin 784) ε hε
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hh
    exact hh

theorem actual_source_pixel_radius_values_and_rounding :
    (28 : ℝ) * (1 / 28) = 1 ∧ (28 : ℝ) * (1 / 10) = 2.8 ∧
    |(1 / 28 : ℝ) - 0.036| < 0.0005 := by norm_num

end SafeLearning.CompleteFoundationsNormExercises
