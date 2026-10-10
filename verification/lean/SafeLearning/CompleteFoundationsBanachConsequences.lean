import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsBanachConsequences

variable {E : Type*} [NormedAddCommGroup E]

theorem actual_closed_sets_contain_the_limits_of_their_sequences
    (X : Set E) (hclosed : IsClosed X) (x : ℕ → E) (p : E)
    (hlim : Tendsto x atTop (𝓝 p)) (hmem : ∀ n, x n ∈ X) : p ∈ X :=
  hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

theorem actual_subset_uniqueness_norm_proof_route
    (X : Set E) (g : X → X) (L : NNReal) (hL : L < 1)
    (hbound : ∀ x y : X, ‖(g x : E) - (g y : E)‖ ≤ (L : ℝ) * ‖(x : E) - (y : E)‖)
    (p q : X) (hp : g p = p) (hq : g q = q) :
    ‖(p : E) - (q : E)‖ = ‖(g p : E) - (g q : E)‖ ∧
      ‖(g p : E) - (g q : E)‖ ≤ (L : ℝ) * ‖(p : E) - (q : E)‖ ∧
      (1 - (L : ℝ)) * ‖(p : E) - (q : E)‖ ≤ 0 ∧ p = q := by
  have hb := hbound p q
  have hpq : ‖(p : E) - (q : E)‖ ≤ (L : ℝ) * ‖(p : E) - (q : E)‖ := by
    simpa only [hp, hq] using hb
  have hL' : (L : ℝ) < 1 := hL
  have he : (p : E) = (q : E) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((p : E) - (q : E))]
  exact ⟨by rw [hp, hq], hb, by nlinarith, Subtype.ext he⟩

theorem actual_subset_one_step_fixed_point_error_and_repetition
    (X : Set E) (g : X → X) (L : NNReal)
    (hbound : ∀ x y : X, ‖(g x : E) - (g y : E)‖ ≤ (L : ℝ) * ‖(x : E) - (y : E)‖)
    (p x : X) (hp : g p = p) :
    (∀ n : ℕ, ‖((g^[n+1] x : X) : E) - (p : E)‖ ≤
      (L : ℝ) * ‖((g^[n] x : X) : E) - (p : E)‖) ∧
      (∀ n : ℕ, ‖((g^[n] x : X) : E) - (p : E)‖ ≤
        (L : ℝ)^n * ‖(x : E) - (p : E)‖) := by
  have hs : ∀ n : ℕ, ‖((g^[n+1] x : X) : E) - (p : E)‖ ≤
      (L : ℝ) * ‖((g^[n] x : X) : E) - (p : E)‖ := by
    intro n
    simpa only [Function.iterate_succ_apply', hp] using hbound (g^[n] x) p
  refine ⟨hs, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ (L : ℝ) * ‖((g^[n] x : X) : E) - (p : E)‖ := hs n
      _ ≤ (L : ℝ) * ((L : ℝ)^n * ‖(x : E) - (p : E)‖) :=
        mul_le_mul_of_nonneg_left ih L.2
      _ = _ := by rw [pow_succ]; ring

end SafeLearning.CompleteFoundationsBanachConsequences
