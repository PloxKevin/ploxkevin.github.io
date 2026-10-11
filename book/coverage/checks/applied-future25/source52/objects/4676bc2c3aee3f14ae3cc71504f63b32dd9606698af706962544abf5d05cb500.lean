import SafeLearning.CompleteFoundationsGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SafeLearning.CompleteFoundationsNormDuality

open Set
open scoped BigOperators RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

def l1Norm (x : n → ℝ) : ℝ := ‖(WithLp.toLp 1 x : PiLp 1 (fun _ : n => ℝ))‖
def euclidean (x : n → ℝ) : EuclideanSpace ℝ n := WithLp.toLp 2 x
def l2Norm (x : n → ℝ) : ℝ := ‖euclidean x‖

theorem actual_l1_norm_is_sum_absolute_values (x : n → ℝ) :
    l1Norm x = ∑ i, |x i| := by
  simp [l1Norm, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

theorem actual_l2_norm_squared (x : n → ℝ) :
    l2Norm x ^ 2 = ∑ i, (x i) ^ 2 := by
  simp only [l2Norm, euclidean, EuclideanSpace.norm_eq,
    Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

theorem actual_euclidean_pairing_is_dot (w x : n → ℝ) :
    ⟪euclidean w, euclidean x⟫ = w ⬝ᵥ x := by
  simp only [euclidean, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, dotProduct, mul_comm]

theorem actual_sign_absolute_bound_and_dot (a : ℝ) :
    |Real.sign a| ≤ 1 ∧ a * Real.sign a = |a| := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha]
    norm_num
  · norm_num
  · rw [Real.sign_of_pos ha, abs_of_pos ha]
    norm_num

theorem actual_infinity_ball_holder (w x : n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ ε) : |w ⬝ᵥ x| ≤ ε * l1Norm w := by
  have hi := (pi_norm_le_iff_of_nonneg hε).mp hx
  rw [dotProduct, actual_l1_norm_is_sum_absolute_values, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hi i) (abs_nonneg _)

theorem actual_sign_vector_attains_infinity_ball (w : n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(fun i => ε * Real.sign (w i) : n → ℝ)‖ ≤ ε ∧
    w ⬝ᵥ (fun i => ε * Real.sign (w i)) = ε * l1Norm w := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul_of_nonneg_left (actual_sign_absolute_bound_and_dot (w i)).1 hε
  · rw [dotProduct, actual_l1_norm_is_sum_absolute_values, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      w i * (ε * Real.sign (w i)) = ε * (w i * Real.sign (w i)) := by ring
      _ = ε * |w i| := by rw [(actual_sign_absolute_bound_and_dot (w i)).2]

theorem actual_infinity_ball_support_maximum (w : n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest ((fun x : n → ℝ => w ⬝ᵥ x) '' {x | ‖x‖ ≤ ε}) (ε * l1Norm w) := by
  refine ⟨⟨fun i => ε * Real.sign (w i),
    (actual_sign_vector_attains_infinity_ball w ε hε).1,
    (actual_sign_vector_attains_infinity_ball w ε hε).2⟩, ?_⟩
  rintro value ⟨x, hx, rfl⟩
  exact (le_abs_self _).trans (actual_infinity_ball_holder w x ε hε hx)

theorem actual_one_ball_holder (w x : n → ℝ) :
    |w ⬝ᵥ x| ≤ ‖w‖ * l1Norm x := by
  rw [dotProduct, actual_l1_norm_is_sum_absolute_values, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i)
    (abs_nonneg _)

theorem actual_largest_coordinate_attains_one_ball (w : n → ℝ) (j : n)
    (hj : |w j| = ‖w‖) (ε : ℝ) (hε : 0 ≤ ε) :
    l1Norm (Pi.single j (ε * Real.sign (w j))) ≤ ε ∧
    w ⬝ᵥ Pi.single j (ε * Real.sign (w j)) = ε * ‖w‖ := by
  constructor
  · rw [actual_l1_norm_is_sum_absolute_values, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, abs_mul, abs_of_nonneg hε]
      simpa using mul_le_mul_of_nonneg_left (actual_sign_absolute_bound_and_dot (w j)).1 hε
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, abs_zero]
    · simp
  · rw [dotProduct_single]
    calc
      w j * (ε * Real.sign (w j)) = ε * (w j * Real.sign (w j)) := by ring
      _ = ε * ‖w‖ := by rw [(actual_sign_absolute_bound_and_dot (w j)).2, hj]

theorem actual_one_ball_support_maximum (w : n → ℝ) (j : n) (hj : |w j| = ‖w‖)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest ((fun x : n → ℝ => w ⬝ᵥ x) '' {x | l1Norm x ≤ ε}) (ε * ‖w‖) := by
  refine ⟨⟨Pi.single j (ε * Real.sign (w j)),
    (actual_largest_coordinate_attains_one_ball w j hj ε hε).1,
    (actual_largest_coordinate_attains_one_ball w j hj ε hε).2⟩, ?_⟩
  rintro value ⟨x, hx, rfl⟩
  have hu := (le_abs_self _).trans (actual_one_ball_holder w x)
  have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg w)
  simpa only [mul_comm] using hu.trans hm

theorem actual_euclidean_ball_support_maximum (w : n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest ((fun x : n → ℝ => w ⬝ᵥ x) '' {x | l2Norm x ≤ ε}) (ε * l2Norm w) := by
  obtain ⟨u, hu, he⟩ := CompleteFoundationsGeometry.linear_ball_attainment (euclidean w) 0 ε hε
  refine ⟨⟨(u : n → ℝ), ?_, ?_⟩, ?_⟩
  · simpa [l2Norm, euclidean] using hu
  · have hp : ⟪euclidean w, u⟫ = w ⬝ᵥ (u : n → ℝ) :=
      actual_euclidean_pairing_is_dot w (u : n → ℝ)
    simpa only [inner_zero_right, zero_add, hp, l2Norm] using he
  · rintro value ⟨x, hx, rfl⟩
    have hh := (le_abs_self ⟪euclidean w, euclidean x⟫).trans
      (abs_real_inner_le_norm (euclidean w) (euclidean x))
    rw [actual_euclidean_pairing_is_dot] at hh
    exact hh.trans (by simpa only [l2Norm, mul_comm] using
      mul_le_mul_of_nonneg_left hx (norm_nonneg (euclidean w)))

theorem actual_infinity_ball_in_euclidean_ball (x : n → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hx : ‖x‖ ≤ ε) : l2Norm x ≤ Real.sqrt (Fintype.card n) * ε := by
  have hi := (pi_norm_le_iff_of_nonneg hε).mp hx
  have hsq : l2Norm x ^ 2 ≤ (Fintype.card n : ℝ) * ε ^ 2 := by
    rw [actual_l2_norm_squared]
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ _i : n, ε ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hb := hi i
        rw [Real.norm_eq_abs] at hb
        nlinarith [sq_abs (x i), abs_nonneg (x i)]
      _ = (Fintype.card n : ℝ) * ε ^ 2 := by simp
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card n : ℝ))
  have hp : 0 ≤ Real.sqrt (Fintype.card n) * ε := mul_nonneg (Real.sqrt_nonneg _) hε
  have hn : 0 ≤ l2Norm x := norm_nonneg _
  nlinarith

theorem actual_largest_absolute_coordinate_exists [Nonempty n] (w : n → ℝ) :
    ∃ j : n, |w j| = ‖w‖ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |w i|)
    Finset.univ_nonempty
  refine ⟨j, le_antisymm ?_ ?_⟩
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (w j))).mpr
    intro i
    simpa only [Real.norm_eq_abs] using hj i (Finset.mem_univ i)

theorem actual_one_ball_support_maximum_without_supplied_coordinate [Nonempty n]
    (w : n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest ((fun x : n → ℝ => w ⬝ᵥ x) '' {x | l1Norm x ≤ ε}) (ε * ‖w‖) := by
  obtain ⟨j, hj⟩ := actual_largest_absolute_coordinate_exists w
  exact actual_one_ball_support_maximum w j hj ε hε

theorem actual_constant_vector_attains_dimension_conversion (ε : ℝ) (hε : 0 ≤ ε) :
    l2Norm (fun _ : n => ε) = Real.sqrt (Fintype.card n) * ε := by
  have hs := actual_l2_norm_squared (fun _ : n => ε)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hr := Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card n : ℝ))
  have hp : 0 ≤ Real.sqrt (Fintype.card n) * ε := mul_nonneg (Real.sqrt_nonneg _) hε
  have hn : 0 ≤ l2Norm (fun _ : n => ε) := norm_nonneg _
  nlinarith

end SafeLearning.CompleteFoundationsNormDuality
