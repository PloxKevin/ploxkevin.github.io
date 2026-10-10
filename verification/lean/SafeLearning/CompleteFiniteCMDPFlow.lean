import SafeLearning.CompleteFiniteCMDPOccupancy

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPFlow

open SafeLearning.CompleteFiniteCMDPOccupancy

variable {S A : Type*} [Fintype S] [Fintype A]

def stateMarginal (ρ : S → A → ℝ) (s : S) : ℝ := ∑ a, ρ s a

/-- The nonnegative discounted Bellman-flow polyhedron of the actual model. -/
def FlowFeasible (M : Model S A) (γ : ℝ) (ρ : S → A → ℝ) : Prop :=
  (∀ s a, 0 ≤ ρ s a) ∧ ∀ t, stateMarginal ρ t =
    (1 - γ) * M.initial t + γ * ∑ s, ∑ a, ρ s a * M.transition s a t

theorem actual_occupancy_satisfies_flow (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    FlowFeasible M γ (occupancy M π γ) :=
  ⟨actual_occupancy_nonneg M π γ hγ0 hγ1,
    actual_discounted_bellman_flow M π γ hγ0 hγ1⟩

theorem actual_all_feasible_flows_have_total_mass_one (M : Model S A)
    (γ : ℝ) (hγ1 : γ < 1) (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ) :
    ∑ s, ∑ a, ρ s a = 1 := by
  have he := congrArg (fun f : S → ℝ => ∑ t, f t) (funext hρ.2)
  simp only [stateMarginal, Finset.sum_add_distrib, ← Finset.mul_sum] at he
  have rearrange : (∑ t, ∑ s, ∑ a, ρ s a * M.transition s a t) =
      ∑ s, ∑ a, ρ s a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, M.transition_sum, mul_one]
  rw [M.initial_sum, mul_one, rearrange] at he
  nlinarith

theorem actual_feasible_coordinate_bound (M : Model S A)
    (γ : ℝ) (hγ1 : γ < 1) (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ)
    (s : S) (a : A) : 0 ≤ ρ s a ∧ ρ s a ≤ 1 := by
  refine ⟨hρ.1 s a, ?_⟩
  have h₁ := Finset.single_le_sum (s := Finset.univ)
    (fun b _ => hρ.1 s b) (Finset.mem_univ a)
  have h₂ := Finset.single_le_sum (s := Finset.univ) (f := fun t => ∑ b, ρ t b)
    (fun t _ => Finset.sum_nonneg (s := Finset.univ) (fun b _ => hρ.1 t b))
    (Finset.mem_univ s)
  exact h₁.trans (h₂.trans_eq (actual_all_feasible_flows_have_total_mass_one M γ hγ1 ρ hρ))

theorem actual_nonnegative_flow_polyhedron_is_convex (M : Model S A) (γ : ℝ) :
    Convex ℝ {ρ | FlowFeasible M γ ρ} := by
  intro ρ hρ σ hσ u v hu hv huv
  constructor
  · intro s a
    exact add_nonneg (mul_nonneg hu (hρ.1 s a)) (mul_nonneg hv (hσ.1 s a))
  · intro t
    change (∑ a, (u * ρ t a + v * σ t a)) =
      (1 - γ) * M.initial t + γ * ∑ s, ∑ a,
        (u * ρ s a + v * σ s a) * M.transition s a t
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    change u * stateMarginal ρ t + v * stateMarginal σ t = _
    rw [hρ.2 t, hσ.2 t]
    have rearrange : (∑ s, ∑ a,
        (u * ρ s a + v * σ s a) * M.transition s a t) =
        u * (∑ s, ∑ a, ρ s a * M.transition s a t) +
        v * (∑ s, ∑ a, σ s a * M.transition s a t) := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [rearrange]
    nlinarith [congrArg (fun x : ℝ => x * ((1 - γ) * M.initial t)) huv]

end SafeLearning.CompleteFiniteCMDPFlow
