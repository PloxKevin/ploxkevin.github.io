import Mathlib
import SafeLearning.CompleteFoundationsRatesCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace SafeLearning.CompleteFoundationsLogCubeCrossover31

def cubeRootRatio (t : ℝ) : ℝ := (Real.log t)^3 / Real.sqrt t

/-- The two actual asymptotic statements are transferred from complete existing proofs. -/
theorem actual_log_cube_is_little_o_of_square_root :
    (fun t : ℝ => (Real.log t)^3) =o[atTop] Real.sqrt :=
  SafeLearning.CompleteFoundationsRatesCosts.actual_log_cube_vs_sqrt

theorem actual_square_root_over_two_thirds_power_tends_to_zero :
    Tendsto (fun t : ℝ => Real.sqrt t / Real.rpow t (2/3)) atTop (𝓝 0) :=
  SafeLearning.CompleteFoundationsRatesCosts.actual_sqrt_vs_two_thirds_ratio

theorem actual_cube_square_root_ratio_derivative
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt cubeRootRatio
      ((Real.log t)^2 * (6-Real.log t) / (2*t*Real.sqrt t)) t := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have he := Real.sq_sqrt ht.le
  convert (((hasDerivAt_id t).log ht.ne').pow 3).div
    (Real.hasDerivAt_sqrt ht.ne') hs using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, show (3 - 1 : ℕ) = 2 from rfl]
    field_simp
    rw [he]
    ring

theorem actual_ratio_increases_up_to_exp_six :
    MonotoneOn cubeRootRatio (Icc 4 (Real.exp 6)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun t => (Real.log t)^2 * (6-Real.log t)/(2*t*Real.sqrt t))
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t
      (by linarith [(interior_subset ht).1])).hasDerivWithinAt
  · intro t ht
    have hmem := interior_subset ht
    have hp : 0 < t := by linarith [hmem.1]
    have hl : Real.log t ≤ 6 := by
      simpa using Real.log_le_log hp hmem.2
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hl)) (by positivity)

theorem actual_ratio_decreases_after_exp_six :
    AntitoneOn cubeRootRatio (Ici (Real.exp 6)) := by
  have hp (t : ℝ) (ht : t ∈ Ici (Real.exp 6)) : 0 < t :=
    lt_of_lt_of_le (Real.exp_pos _) ht
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (f' := fun t => (Real.log t)^2 * (6-Real.log t)/(2*t*Real.sqrt t))
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t (hp t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t (hp t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    have hmem := interior_subset ht
    have htpos := hp t hmem
    have hl : 6 ≤ Real.log t := by
      simpa using Real.log_le_log (Real.exp_pos 6) hmem
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hl)) (by positivity)

theorem actual_two_endpoint_logarithms_and_bounds :
    Real.log (4:ℝ) = 2*Real.log 2 ∧
    Real.log (24000000:ℝ) = 9*Real.log 2+Real.log 3+6*Real.log 5 ∧
    (1386/1000:ℝ) < Real.log 4 ∧
    (169935/10000:ℝ) < Real.log 24000000 ∧
    Real.log (24000000:ℝ) < 17 := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have h24 : Real.log (24000000:ℝ) = 9*Real.log 2+Real.log 3+6*Real.log 5 := by
    rw [show (24000000:ℝ)=2^9*3*5^6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  refine ⟨h4,h24,?_,?_,?_⟩
  · rw [h4]
    linarith [Real.log_two_gt_d9]
  · rw [h24]
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]
  · rw [h24]
    linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]

theorem actual_cube_root_ratio_exceeds_one_at_both_endpoints :
    1 < cubeRootRatio 4 ∧ 1 < cubeRootRatio 24000000 := by
  have h := actual_two_endpoint_logarithms_and_bounds
  constructor
  · rw [cubeRootRatio,lt_div_iff₀ (by positivity)]
    have hs : Real.sqrt (4:ℝ)=2 := by norm_num
    rw [hs]
    have hc := pow_lt_pow_left₀ h.2.2.1 (by norm_num : (0:ℝ) ≤ 1386/1000) (by norm_num : (3:ℕ) ≠ 0)
    norm_num at hc
    linarith
  · rw [cubeRootRatio,lt_div_iff₀ (by positivity)]
    have hs : Real.sqrt (24000000:ℝ) < 4899 := by
      apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
      norm_num
    have hl := h.2.2.2.1
    nlinarith [sq_nonneg (Real.log (24000000:ℝ)-169935/10000),
      mul_nonneg (by linarith : 0 ≤ Real.log (24000000:ℝ)-169935/10000)
        (sq_nonneg (Real.log (24000000:ℝ)))]

/-- This is an actual every-real-point finite interval comparison; little-o is not used
as a premise to conclude any of its finite-budget inequalities. -/
theorem actual_every_point_from_four_to_twenty_four_million_has_log_cube_above_root
    (t : ℝ) (ht : t ∈ Icc 4 24000000) : (Real.log t)^3 > Real.sqrt t := by
  have h4 : 4 ≤ Real.exp 6 := by
    have hlog : Real.log (4:ℝ) ≤ 6 := by
      rw [actual_two_endpoint_logarithms_and_bounds.1]
      linarith [Real.log_two_lt_d9]
    exact (Real.exp_log (by norm_num : (0:ℝ)<4)).symm.le.trans (Real.exp_le_exp.mpr hlog)
  have h24 : Real.exp 6 ≤ 24000000 := by
    have hlog : 6 ≤ Real.log (24000000:ℝ) := by
      linarith [actual_two_endpoint_logarithms_and_bounds.2.2.2.1]
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by norm_num : (0:ℝ)<24000000))
  have hr : 1 < cubeRootRatio t := by
    by_cases hsplit : t ≤ Real.exp 6
    · exact actual_cube_root_ratio_exceeds_one_at_both_endpoints.1.trans_le
        (actual_ratio_increases_up_to_exp_six ⟨le_rfl,h4⟩ ⟨ht.1,hsplit⟩ ht.1)
    · exact actual_cube_root_ratio_exceeds_one_at_both_endpoints.2.trans_le
        (actual_ratio_decreases_after_exp_six (le_of_not_ge hsplit) h24 ht.2)
  have hp : 0 < t := by linarith [ht.1]
  simpa [cubeRootRatio] using (lt_div_iff₀ (Real.sqrt_pos.mpr hp)).mp hr

end SafeLearning.CompleteFoundationsLogCubeCrossover31

namespace SafeLearning.CompleteFoundationsLogCubeCrossover31

theorem actual_square_root_is_little_o_of_two_thirds_power :
    Real.sqrt =o[atTop] (fun t : ℝ => Real.rpow t (2/3)) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
    actual_square_root_over_two_thirds_power_tends_to_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  intro h
  exact False.elim ((ne_of_gt (Real.rpow_pos_of_pos ht (2/3))) h)

end SafeLearning.CompleteFoundationsLogCubeCrossover31


namespace SafeLearning.CompleteFoundationsLogCubeCrossover31

/-- An exact rational upper endpoint brackets the advertised approximate crossover. -/
theorem actual_ratio_is_below_one_at_twenty_four_and_a_half_million :
    cubeRootRatio 24500000 < 1 := by
  have h25 : Real.log (25000000:ℝ) = 6*Real.log 2 + 8*Real.log 5 := by
    rw [show (25000000:ℝ)=2^6*5^8 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hl : Real.log (24500000:ℝ) < 17035/1000 := by
    have hm : Real.log (24500000:ℝ) ≤ Real.log (25000000:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [h25] at hm
    linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]
  have hc := pow_lt_pow_left₀ hl
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 24500000)) (by norm_num : (3:ℕ) ≠ 0)
  have hs : (4949:ℝ) < Real.sqrt 24500000 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  rw [cubeRootRatio, div_lt_iff₀ (by positivity)]
  norm_num at hc
  nlinarith

/-- Beyond the lower numerical endpoint the ratio is strictly decreasing. -/
theorem actual_ratio_is_strictly_decreasing_after_twenty_four_million :
    StrictAntiOn cubeRootRatio (Ici 24000000) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici _)
    (f' := fun t => (Real.log t)^2 * (6-Real.log t)/(2*t*Real.sqrt t))
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t (by have hh : (24000000:ℝ) ≤ t := ht; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    exact (actual_cube_square_root_ratio_derivative t
      (by have hh : (24000000:ℝ) ≤ t := interior_subset ht; linarith)).hasDerivWithinAt
  · intro t ht
    have hmem := interior_subset ht
    have htlow : (24000000:ℝ) ≤ t := hmem
    have hp : 0 < t := by linarith
    have hl : 6 < Real.log t := by
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<24000000) hmem
      linarith [actual_two_endpoint_logarithms_and_bounds.2.2.2.1]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_pos (by linarith)) (by linarith)) (by positivity)

/-- The true upper crossover lies between 24 and 24.5 million, and is unique there. -/
theorem actual_unique_upper_crossover_in_an_exact_half_million_bracket :
    ∃! t : ℝ, t ∈ Icc 24000000 24500000 ∧ cubeRootRatio t = 1 := by
  have hc : ContinuousOn cubeRootRatio (Icc 24000000 24500000) := by
    intro t ht
    exact (actual_cube_square_root_ratio_derivative t (by linarith [ht.1])).continuousAt.continuousWithinAt
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (24000000:ℝ)≤24500000) hc
    ⟨actual_ratio_is_below_one_at_twenty_four_and_a_half_million.le,
      actual_cube_root_ratio_exceeds_one_at_both_endpoints.2.le⟩
  refine ⟨t, ⟨ht, he⟩, ?_⟩
  intro s hs
  apply actual_ratio_is_strictly_decreasing_after_twenty_four_million.injOn hs.1.1 ht.1
  exact hs.2.trans he.symm

end SafeLearning.CompleteFoundationsLogCubeCrossover31


namespace SafeLearning.CompleteFoundationsLogCubeCrossover31

/-- The same asymptotic assertion permits any prescribed value at a fixed budget.
This is the exact finite-point limitation of a little-o statement. -/
theorem actual_little_o_assertion_allows_any_value_at_any_fixed_budget
    (t₀ value : ℝ) :
    (fun t : ℝ => if t = t₀ then value else (Real.log t)^3) =o[atTop] Real.sqrt ∧
      (if t₀ = t₀ then value else (Real.log t₀)^3) = value := by
  refine ⟨?_, by simp⟩
  apply actual_log_cube_is_little_o_of_square_root.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop t₀] with t ht
  simp [ne_of_gt ht]

end SafeLearning.CompleteFoundationsLogCubeCrossover31
