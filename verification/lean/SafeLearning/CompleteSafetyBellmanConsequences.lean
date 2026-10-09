import SafeLearning.CompleteSafetyBellman

set_option autoImplicit false
noncomputable section
open scoped NNReal

namespace SafeLearning.CompleteSafetyBellmanConsequences

open CompleteSafetyBellman

theorem smaller_c_rejects_displayed_family (c : ℝ) (hc : c < -1) :
    undiscounted ![c, min 1 c, -1] 1 ≠ min 1 c := by
  have hc1 : c ≤ 1 := by linarith
  have hcF : c ≤ (-1 : ℝ) := hc.le
  simp [undiscounted, margin, future, min_eq_right hc1, max_eq_right hcF]
  linarith

theorem no_strict_contraction_for_undiscounted :
    ¬ ∃ K : ℝ≥0, ContractingWith K undiscounted := by
  rintro ⟨K, hK⟩
  obtain ⟨V, W, hV, hW, hne⟩ := undiscounted_nonunique
  exact hne (hK.fixedPoint_unique' hV hW)

def generalDiscounted (gamma : ℝ) (V : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  (1 - gamma) * margin s + gamma * min (margin s) (future V s)

theorem actual_general_interpolation (gamma : ℝ) (V : Fin 3 → ℝ) (s : Fin 3)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    min (margin s) (future V s) ≤ generalDiscounted gamma V s ∧
      generalDiscounted gamma V s ≤ margin s := by
  have hclip := min_le_left (margin s) (future V s)
  have h1 := mul_nonneg hg0 (sub_nonneg.mpr hclip)
  have h2 := mul_nonneg (sub_nonneg.mpr hg1) (sub_nonneg.mpr hclip)
  unfold generalDiscounted
  constructor <;> nlinarith

theorem source_half_is_general_half : generalDiscounted (1 / 2) = discounted := by
  funext V s
  unfold generalDiscounted discounted
  ring

theorem actual_safe_policy_all_time (s : Fin 3) (hs : 0 ≤ fixed s) (n : ℕ) :
    0 ≤ fixed (safeTransition^[n] s) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact actual_safe_policy _ ih

end SafeLearning.CompleteSafetyBellmanConsequences
