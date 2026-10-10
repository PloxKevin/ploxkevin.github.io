import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SafeLearning.CompleteSafetyBellman

def margin : Fin 3 → ℝ := ![2, 1, -1]
def future (V : Fin 3 → ℝ) : Fin 3 → ℝ := ![max (V 0) (V 1), max (V 0) (V 2), V 2]
def undiscounted (V : Fin 3 → ℝ) (s : Fin 3) : ℝ := min (margin s) (future V s)
def discounted (V : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  (1 / 2) * margin s + (1 / 2) * min (margin s) (future V s)

theorem undiscounted_fixed_family (c : ℝ) (hc : c ∈ Icc (-1) 2) :
    undiscounted ![c, min 1 c, -1] = ![c, min 1 c, -1] := by
  ext s
  fin_cases s
  · simp [undiscounted, margin, future, min_eq_right hc.2]
  · simp [undiscounted, margin, future, max_eq_left hc.1]
  · norm_num [undiscounted, margin, future]

theorem undiscounted_nonunique :
    ∃ V W : Fin 3 → ℝ, undiscounted V = V ∧ undiscounted W = W ∧ V ≠ W := by
  refine ⟨![0, min 1 0, -1], ![2, min 1 2, -1],
    undiscounted_fixed_family 0 (by norm_num), undiscounted_fixed_family 2 (by norm_num), ?_⟩
  intro he
  have h := congrFun he 0
  norm_num at h

theorem undiscounted_lower_failure_fixed : undiscounted ![0, 0, -5] = ![0, 0, -5] := by
  ext s
  fin_cases s <;> norm_num [undiscounted, margin, future]

theorem undiscounted_zero_start :
    undiscounted (0 : Fin 3 → ℝ) = ![0, 0, -1] ∧
      undiscounted ![0, 0, -1] = ![0, 0, -1] := by
  constructor
  · ext s
    fin_cases s <;> norm_num [undiscounted, margin, future]
  · simpa using undiscounted_fixed_family 0 (by norm_num)

theorem future_difference_bound (V W : Fin 3 → ℝ) (s : Fin 3) :
    |future V s - future W s| ≤ dist V W := by
  have hp (i : Fin 3) : |V i - W i| ≤ dist V W := by
    simpa only [Real.dist_eq] using dist_le_pi_dist V W i
  fin_cases s
  · exact (abs_max_sub_max_le_max (V 0) (V 1) (W 0) (W 1)).trans
      (max_le (hp 0) (hp 1))
  · exact (abs_max_sub_max_le_max (V 0) (V 2) (W 0) (W 2)).trans
      (max_le (hp 0) (hp 2))
  · exact hp 2

theorem clipped_difference_bound (V W : Fin 3 → ℝ) (s : Fin 3) :
    |min (margin s) (future V s) - min (margin s) (future W s)| ≤ dist V W := by
  exact (abs_min_sub_min_le_max (margin s) (future V s) (margin s) (future W s)).trans
    (max_le (by simpa using (dist_nonneg : 0 ≤ dist V W)) (future_difference_bound V W s))

theorem actual_half_contraction : ContractingWith (1 / 2) discounted := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro V W
  apply (dist_pi_le_iff (by positivity : 0 ≤ (1 / 2 : ℝ) * dist V W)).mpr
  intro s
  have he : discounted V s - discounted W s = (1 / 2) *
      (min (margin s) (future V s) - min (margin s) (future W s)) := by
    unfold discounted
    ring
  rw [Real.dist_eq, he, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat]
  exact mul_le_mul_of_nonneg_left (clipped_difference_bound V W s) (by norm_num)

def fixed : Fin 3 → ℝ := ![2, 1, -1]

theorem actual_fixed_point : discounted fixed = fixed := by
  ext s
  fin_cases s <;> norm_num [discounted, fixed, margin, future]

theorem fixed_point_unique (V : Fin 3 → ℝ) (hV : discounted V = V) : V = fixed :=
  actual_half_contraction.fixedPoint_unique' hV actual_fixed_point

theorem all_value_iteration_converges (V : Fin 3 → ℝ) :
    Tendsto (fun n : ℕ => discounted^[n] V) atTop (nhds fixed) := by
  obtain ⟨W, hw, hc, _⟩ := actual_half_contraction.exists_fixedPoint V (edist_ne_top _ _)
  rw [fixed_point_unique W hw] at hc
  exact hc

def iteration (n : ℕ) : Fin 3 → ℝ := discounted^[n] 0

theorem iteration_successor (n : ℕ) : iteration (n + 1) = discounted (iteration n) :=
  Function.iterate_succ_apply' discounted n 0

theorem first_four_sweeps :
    iteration 1 = ![1, 1 / 2, -1] ∧ iteration 2 = ![3 / 2, 1, -1] ∧
      iteration 3 = ![7 / 4, 1, -1] ∧ iteration 4 = ![15 / 8, 1, -1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext s <;> fin_cases s <;>
    norm_num [iteration, Function.iterate_succ_apply', discounted, margin, future]

theorem all_later_sweeps (n : ℕ) :
    iteration (n + 2) = ![2 - (1 / 2 : ℝ) ^ (n + 1), 1, -1] := by
  induction n with
  | zero => convert first_four_sweeps.2.1 using 1 <;> norm_num
  | succ n ih =>
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_nonneg (by norm_num) _
    have hp1 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have ha1 : 1 ≤ 2 - (1 / 2 : ℝ) ^ (n + 1) := by linarith
    have ha2 : 2 - (1 / 2 : ℝ) ^ (n + 1) ≤ 2 := by linarith
    have haF : (-1 : ℝ) ≤ 2 - (1 / 2 : ℝ) ^ (n + 1) := by linarith
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, iteration_successor, ih]
    ext s
    fin_cases s
    · change (1 / 2 : ℝ) * 2 + (1 / 2) * min 2 (max (2 - (1 / 2 : ℝ) ^ (n + 1)) 1) =
        2 - (1 / 2 : ℝ) ^ (n + 1 + 1)
      rw [max_eq_left ha1, min_eq_right ha2, pow_succ]
      ring
    · change (1 / 2 : ℝ) * 1 + (1 / 2) * min 1
        (max (2 - (1 / 2 : ℝ) ^ (n + 1)) (-1)) = 1
      rw [max_eq_left haF, min_eq_left ha1]
      ring
    · norm_num [discounted, future, margin]

theorem exact_error_halving (n : ℕ) :
    2 - iteration (n + 2) 0 = (1 / 2 : ℝ) ^ (n + 1) ∧
      2 - iteration (n + 3) 0 = (1 / 2) * (2 - iteration (n + 2) 0) := by
  rw [all_later_sweeps n, show n + 3 = (n + 1) + 2 by omega, all_later_sweeps (n + 1)]
  simp [pow_succ] <;> ring

theorem safe_set (s : Fin 3) : 0 ≤ fixed s ↔ s = 0 ∨ s = 1 := by
  fin_cases s <;> norm_num [fixed]

def safeTransition : Fin 3 → Fin 3 := ![0, 0, 2]

theorem actual_safe_policy (s : Fin 3) (hs : 0 ≤ fixed s) :
    0 ≤ fixed (safeTransition s) := by
  fin_cases s <;> norm_num [fixed, safeTransition] at *

theorem constant_margin_value : fixed 0 = margin 0 := by norm_num [fixed, margin]

end SafeLearning.CompleteSafetyBellman
