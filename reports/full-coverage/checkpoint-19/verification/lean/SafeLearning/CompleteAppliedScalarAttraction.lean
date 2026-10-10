import SafeLearning.CompleteAppliedScalarODEBridges

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedScalarAttraction
open Set Filter
open scoped Topology
open SafeLearning.CompleteAppliedScalarODE

def locallyAttractive (rate : ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧ ∀ initial : ℝ, |initial| < delta →
    Tendsto (solution rate initial) atTop (𝓝 0)

theorem actual_local_attraction_iff_negative_rate (rate : ℝ) :
    locallyAttractive rate ↔ rate < 0 := by
  constructor
  · rintro ⟨delta, hd, h⟩
    have hp : 0 < delta / 2 := by linarith
    have hn : delta / 2 ≠ 0 := ne_of_gt hp
    have ht := h (delta / 2) (by rw [abs_of_pos hp]; linarith)
    have he : Tendsto (fun t : ℝ => Real.exp (rate * t)) atTop (𝓝 0) := by
      have hi := ht.const_mul ((delta / 2)⁻¹)
      simpa only [solution, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_zero]
        using hi
    rw [Real.tendsto_exp_comp_nhds_zero] at he
    exact (tendsto_const_mul_atBot_iff_neg tendsto_id).mp he
  · intro hr
    exact ⟨1, by norm_num, fun initial _ =>
      (actual_linear_all_initial_attraction_iff rate).mpr hr initial⟩

theorem actual_zero_rate_has_arbitrarily_small_nonattracted_states
    (delta : ℝ) (hd : 0 < delta) :
    ∃ initial : ℝ, 0 < initial ∧ |initial| < delta ∧
      (∀ t : ℝ, solution 0 initial t = initial) ∧
      ¬Tendsto (solution 0 initial) atTop (𝓝 0) := by
  refine ⟨delta / 2, by linarith, ?_, ?_, ?_⟩
  · rw [abs_of_pos (by linarith : 0 < delta / 2)]
    linarith
  · intro t
    simp [solution]
  · intro ht
    have hc : Tendsto (solution 0 (delta / 2)) atTop (𝓝 (delta / 2)) := by
      have he : solution 0 (delta / 2) = (fun _ : ℝ => delta / 2) := by
        funext t
        simp [solution]
      rw [he]
      exact tendsto_const_nhds
    have he := tendsto_nhds_unique hc ht
    linarith

theorem actual_feedback_local_asymptotic_stability_iff (k : ℝ) :
    (lyapunovStable (2 - k) ∧ locallyAttractive (2 - k)) ↔ 2 < k := by
  rw [actual_stability_iff_nonpositive_rate, actual_local_attraction_iff_negative_rate]
  constructor <;> intro h <;> (try constructor) <;> linarith

theorem actual_zero_rate_is_stable_but_not_locally_attractive :
    lyapunovStable 0 ∧ ¬locallyAttractive 0 := by
  rw [actual_stability_iff_nonpositive_rate, actual_local_attraction_iff_negative_rate]
  norm_num

theorem actual_strictly_faster_certificate_example :
    (4 * Real.exp (-4 * (0 : ℝ))) = 4 ∧
      (∀ t : ℝ, HasDerivAt (fun s => 4 * Real.exp (-4 * s))
        (-4 * (4 * Real.exp (-4 * t))) t ∧
        -4 * (4 * Real.exp (-4 * t)) ≤ -3 * (4 * Real.exp (-4 * t))) ∧
      ∀ t : ℝ, 0 < t → 4 * Real.exp (-4 * t) < 4 * Real.exp (-3 * t) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro t
    constructor
    · change HasDerivAt (solution (-4) 4) (-4 * solution (-4) 4 t) t
      exact actual_linear_solution_ODE (-4) 4 t
    · have hp := Real.exp_pos (-4 * t)
      linarith
  · intro t ht
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (by linarith)) (by norm_num)

end SafeLearning.CompleteAppliedScalarAttraction
