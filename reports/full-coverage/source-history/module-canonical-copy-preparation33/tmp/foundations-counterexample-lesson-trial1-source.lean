import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsCounterexampleLesson

theorem actual_one_counterexample_disproves_the_universal_statement
    {X : Type*} (P : X → Prop) (x : X) (hx : ¬ P x) : ¬ ∀ y : X, P y := by
  intro h
  exact hx (h x)

theorem actual_alternating_sign_sequence_is_bounded :
    ∀ t : ℕ, |(-1 : ℝ) ^ t| = 1 := by
  intro t
  rw [abs_pow]
  norm_num

theorem actual_continuous_function_on_a_bounded_domain_need_not_attain_a_maximum :
    ContinuousOn (fun x : ℝ => x) (Ioo (0 : ℝ) 1) ∧
      Bornology.IsBounded (Ioo (0 : ℝ) 1) ∧
      ¬ ∃ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, y ≤ x := by
  refine ⟨continuous_id.continuousOn, isBounded_Ioo _ _, ?_⟩
  rintro ⟨x, hx, hmax⟩
  have hm : (x + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have h := hmax ((x + 1) / 2) hm
  linarith [hx.2]

theorem actual_two_inclusions_suffice_for_set_equality
    {X : Type*} (A B : Set X) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B :=
  Subset.antisymm hAB hBA

theorem actual_every_query_in_a_certified_set_satisfies_the_threshold
    {X : Type*} (sets : ℕ → Set X) (query : ℕ → X) (f : X → ℝ) (threshold : ℝ)
    (hquery : ∀ t : ℕ, query t ∈ sets t)
    (hcertificate : ∀ t : ℕ, ∀ x ∈ sets t, threshold ≤ f x) :
    ∀ t : ℕ, threshold ≤ f (query t) := by
  intro t
  exact hcertificate t (query t) (hquery t)

end SafeLearning.CompleteFoundationsCounterexampleLesson
