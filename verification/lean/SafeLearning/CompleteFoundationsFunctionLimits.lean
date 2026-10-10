import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsFunctionLimits

theorem actual_punctured_real_function_limit_is_the_literal_epsilon_delta_definition
    (f : ℝ → ℝ) (a limit : ℝ) :
    Tendsto f (𝓝[≠] a) (𝓝 limit) ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ x : ℝ, 0 < |x - a| → |x - a| < delta → |f x - limit| < epsilon := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Real.dist_eq, mem_compl_iff, mem_singleton_iff, abs_pos, sub_ne_zero]

theorem actual_punctured_real_limit_is_equivalent_to_every_genuine_avoiding_sequence
    (f : ℝ → ℝ) (a limit : ℝ) :
    Tendsto f (𝓝[≠] a) (𝓝 limit) ↔
      ∀ sequence : ℕ → ℝ, Tendsto sequence atTop (𝓝 a) →
        (∀ n, sequence n ≠ a) → Tendsto (fun n => f (sequence n)) atTop (𝓝 limit) := by
  constructor
  · intro hf sequence hs hn
    have hne : Tendsto sequence atTop (𝓝[≠] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hs, Eventually.of_forall ?_⟩
      intro n
      simpa only [mem_compl_iff, mem_singleton_iff] using hn n
    exact hf.comp hne
  · intro hall
    apply tendsto_iff_seq_tendsto.mpr
    intro sequence hs
    have hev : ∀ᶠ n : ℕ in atTop, sequence n ≠ a := by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        eventually_mem_of_tendsto_nhdsWithin hs
    let repaired : ℕ → ℝ := fun n => if sequence n = a then a + 1 else sequence n
    have hrepair : ∀ n, repaired n ≠ a := by
      intro n
      dsimp [repaired]
      split_ifs with h
      · linarith
      · exact h
    have heq : ∀ᶠ n : ℕ in atTop, repaired n = sequence n := by
      filter_upwards [hev] with n hn
      simp [repaired, hn]
    have hrt : Tendsto repaired atTop (𝓝 a) :=
      (tendsto_nhds_of_tendsto_nhdsWithin hs).congr' (heq.mono fun _ h => h.symm)
    exact (hall repaired hrt hrepair).congr' (heq.mono fun _ h => congrArg f h)

theorem actual_right_hand_real_limit_is_the_literal_right_domain_epsilon_definition
    (f : ℝ → ℝ) (a limit : ℝ) :
    Tendsto f (𝓝[>] a) (𝓝 limit) ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ x : ℝ, a < x → |x - a| < delta → |f x - limit| < epsilon := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [mem_Ioi, Real.dist_eq]

theorem actual_left_hand_real_limit_is_the_literal_left_domain_epsilon_definition
    (f : ℝ → ℝ) (a limit : ℝ) :
    Tendsto f (𝓝[<] a) (𝓝 limit) ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ x : ℝ, x < a → |x - a| < delta → |f x - limit| < epsilon := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [mem_Iio, Real.dist_eq]

theorem actual_real_continuity_is_equivalent_to_the_punctured_limit_at_its_actual_value
    (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔ Tendsto f (𝓝[≠] a) (𝓝 (f a)) :=
  continuousAt_iff_punctured_nhds

end SafeLearning.CompleteFoundationsFunctionLimits
