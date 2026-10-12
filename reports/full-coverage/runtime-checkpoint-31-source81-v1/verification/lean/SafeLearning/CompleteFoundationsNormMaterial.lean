import SafeLearning.CompleteFoundationsNormExercises

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteFoundationsNormMaterial
open Set
open scoped BigOperators RealInnerProductSpace
open CompleteFoundationsNormDuality CompleteFoundationsNormExercises

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem actual_one_norm_at_most_dimension_infinity_norm (x : n → ℝ) :
    l1Norm x ≤ Fintype.card n * ‖x‖ := by
  rw [actual_l1_norm_is_sum_absolute_values]
  calc
    ∑ i, |x i| ≤ ∑ _i : n, ‖x‖ := Finset.sum_le_sum fun i _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = Fintype.card n * ‖x‖ := by simp

theorem actual_all_source_norm_comparisons (x : n → ℝ) :
    ‖x‖ ≤ l2Norm x ∧ l2Norm x ≤ l1Norm x ∧
    l1Norm x ≤ Real.sqrt (Fintype.card n) * l2Norm x ∧
    l2Norm x ≤ Real.sqrt (Fintype.card n) * ‖x‖ ∧
    l1Norm x ≤ Fintype.card n * ‖x‖ := by
  exact ⟨actual_infinity_norm_at_most_euclidean_norm x,
    actual_euclidean_norm_at_most_one_norm x,
    actual_one_norm_at_most_dimension_factor_euclidean_norm x,
    actual_infinity_ball_in_euclidean_ball x ‖x‖ (norm_nonneg _) le_rfl,
    actual_one_norm_at_most_dimension_infinity_norm x⟩

theorem actual_unit_coordinate_has_three_norms_one (j : n) :
    ‖(Pi.single j (1:ℝ) : n → ℝ)‖ = 1 ∧
    l2Norm (Pi.single j (1:ℝ)) = 1 ∧ l1Norm (Pi.single j (1:ℝ)) = 1 := by
  have h1 : l1Norm (Pi.single j (1:ℝ)) = 1 := by
    rw [actual_l1_norm_is_sum_absolute_values,Finset.sum_eq_single j]
    · simp
    · intro i hi hij; simp [Pi.single_apply,hij]
    · simp
  have h2 : l2Norm (Pi.single j (1:ℝ)) = 1 := by
    have hs := actual_l2_norm_squared (Pi.single j (1:ℝ))
    simp [Pi.single_apply] at hs
    have hn : 0 ≤ l2Norm (Pi.single j (1:ℝ)) := norm_nonneg _
    rcases hs with hs | hs <;> linarith
  have hi : ‖(Pi.single j (1:ℝ) : n → ℝ)‖ = 1 := by
    apply le_antisymm
    · exact (actual_infinity_norm_at_most_euclidean_norm _).trans h2.le
    · have h := norm_le_pi_norm (Pi.single j (1:ℝ) : n → ℝ) j
      simpa using h
  exact ⟨hi,h2,h1⟩

theorem actual_ones_vector_sharp_right_factors [Nonempty n] :
    ‖(fun _ : n => (1:ℝ))‖ = 1 ∧
    l2Norm (fun _ : n => (1:ℝ)) = Real.sqrt (Fintype.card n) ∧
    l1Norm (fun _ : n => (1:ℝ)) = Fintype.card n := by
  refine ⟨by simp,?_,by simp [actual_l1_norm_is_sum_absolute_values]⟩
  simp [l2Norm,euclidean,EuclideanSpace.norm_eq]

def stack (x : n → ℝ) (u : m → ℝ) : n ⊕ m → ℝ := Sum.elim x u

theorem actual_stacked_euclidean_norm_squared (x : n → ℝ) (u : m → ℝ) :
    l2Norm (stack x u) ^ 2 = l2Norm x ^ 2 + l2Norm u ^ 2 := by
  simp [actual_l2_norm_squared,stack,Fintype.sum_sum_type]

theorem actual_stacked_one_norm (x : n → ℝ) (u : m → ℝ) :
    l1Norm (stack x u) = l1Norm x + l1Norm u := by
  simp [actual_l1_norm_is_sum_absolute_values,stack,Fintype.sum_sum_type]

theorem actual_stacked_infinity_norm (x : n → ℝ) (u : m → ℝ) :
    ‖stack x u‖ = max ‖x‖ ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg x))).mpr
    intro i
    cases i with
    | inl j => exact (norm_le_pi_norm x j).trans (le_max_left _ _)
    | inr j => exact (norm_le_pi_norm u j).trans (le_max_right _ _)
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact norm_le_pi_norm (stack x u) (Sum.inl i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact norm_le_pi_norm (stack x u) (Sum.inr i)

section GeneralInnerProducts
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_triangle_squared_from_cauchy_schwarz (x y : E) :
    ‖x+y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x,y⟫ + ‖y‖ ^ 2 ∧
    ‖x+y‖ ^ 2 ≤ (‖x‖+‖y‖)^2 ∧ ‖x+y‖ ≤ ‖x‖+‖y‖ := by
  have hcs := (le_abs_self ⟪x,y⟫).trans (abs_real_inner_le_norm x y)
  have he := norm_add_sq_real x y
  exact ⟨he,by nlinarith,by nlinarith [norm_nonneg (x+y),norm_nonneg x,norm_nonneg y]⟩

theorem actual_unit_ball_nonzero_radial_maximizer (c : E) (hc : c ≠ 0) :
    ‖(1/‖c‖ : ℝ) • c‖ = 1 ∧ ⟪c,(1/‖c‖ : ℝ) • c⟫ = ‖c‖ := by
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (by norm_num) hn)]
    field_simp
  · rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp

theorem actual_shifted_ball_support_is_greatest (c center : E) (radius : ℝ)
    (hr : 0 ≤ radius) :
    IsGreatest ((fun u => ⟪c,u⟫) '' {u | ‖u-center‖ ≤ radius})
      (⟪c,center⟫+radius*‖c‖) := by
  obtain ⟨point,hp,he⟩ := CompleteFoundationsGeometry.linear_ball_attainment c center radius hr
  refine ⟨⟨point,hp,he⟩,?_⟩
  rintro _ ⟨other,ho,rfl⟩
  exact CompleteFoundationsGeometry.linear_ball_upper_bound c center other radius ho

theorem actual_zero_objective_every_feasible_point_maximizes (center point : E)
    (radius : ℝ) (hp : ‖point-center‖ ≤ radius) :
    IsGreatest ((fun u : E => ⟪(0:E),u⟫) '' {u | ‖u-center‖ ≤ radius}) 0 ∧
    ⟪(0:E),point⟫ = 0 := by
  refine ⟨⟨⟨point,hp,by simp⟩,?_⟩,by simp⟩
  rintro _ ⟨other,ho,rfl⟩
  simp
end GeneralInnerProducts

section GeneralNorms
variable {E : Type*} [NormedAddCommGroup E]

theorem actual_reverse_triangle_from_triangle (x y : E) :
    ‖x‖ ≤ ‖x-y‖+‖y‖ ∧ ‖y‖ ≤ ‖x-y‖+‖x‖ ∧
      |‖x‖-‖y‖| ≤ ‖x-y‖ := by
  have hx : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
  have hy : ‖y‖ ≤ ‖x-y‖+‖x‖ := by
    simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (y-x) x
  exact ⟨hx,hy,abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem actual_every_norm_is_one_lipschitz : LipschitzWith 1 (norm : E → ℝ) :=
  lipschitzWith_one_norm

theorem actual_punctured_unit_ball_excludes_zero :
    (0:E) ∉ {u : E | 0 < ‖u‖ ∧ ‖u‖ ≤ 1} := by simp

theorem actual_radial_denominator_nonzero_iff (u : E) :
    ‖u‖ ≠ 0 ↔ u ≠ 0 := norm_ne_zero_iff
end GeneralNorms

end SafeLearning.CompleteFoundationsNormMaterial
