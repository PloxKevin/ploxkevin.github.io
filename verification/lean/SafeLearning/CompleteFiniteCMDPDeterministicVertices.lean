import SafeLearning.CompleteFiniteCMDPRecovery

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPDeterministicVertices

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery

variable {S A : Type*} [Fintype S] [Fintype A]

def pureAction (d : S → A) (s : S) (a : A) : ℝ := by
  classical
  exact if a = d s then 1 else 0

theorem actual_pure_action_nonnegative (d : S → A) (s : S) (a : A) :
    0 ≤ pureAction d s a := by
  classical
  simp only [pureAction]
  split_ifs <;> norm_num

theorem actual_pure_action_normalized (d : S → A) (s : S) :
    ∑ a, pureAction d s a = 1 := by
  classical
  simp [pureAction]

def purePolicy (d : S → A) : Policy S A where
  action _ := pureAction d
  action_nonneg _ := actual_pure_action_nonnegative d
  action_sum _ := actual_pure_action_normalized d

theorem actual_pure_policy_occupancy_has_only_selected_actions
    (M : Model S A) (d : S → A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (s : S) (a : A) (ha : a ≠ d s) :
    occupancy M (purePolicy d) γ s a = 0 := by
  rw [actual_stationary_occupancy_factorization M (purePolicy d)
    (fun _ _ _ => rfl) γ hγ0 hγ1]
  simp [purePolicy, pureAction, ha]

/-- A feasible flow supported by a fixed deterministic action at each state is
the actual discounted occupancy of that policy, including unreachable states. -/
theorem actual_flow_supported_on_selected_actions_is_pure_policy_occupancy
    (M : Model S A) (d : S → A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ)
    (hsupport : ∀ s a, a ≠ d s → ρ s a = 0) :
    occupancy M (purePolicy d) γ = ρ := by
  classical
  have hrow (s : S) : stateMarginal ρ s = ρ s (d s) := by
    exact Finset.sum_eq_single (d s)
      (fun a _ ha => hsupport s a ha) (by simp)
  have hprod : ∀ s a, stateMarginal ρ s * pureAction d s a = ρ s a := by
    intro s a
    by_cases ha : a = d s
    · subst a
      simpa [pureAction] using hrow s
    · simp [pureAction, ha, hsupport s a ha]
  have hoccprod : ∀ s a,
      stateMarginal (occupancy M (purePolicy d) γ) s * pureAction d s a =
        occupancy M (purePolicy d) γ s a := by
    intro s a
    exact (actual_stationary_occupancy_factorization M (purePolicy d)
      (fun _ _ _ => rfl) γ hγ0 hγ1 s a).symm
  have hK := actual_stationary_kernel_probability_law M (pureAction d)
    (actual_pure_action_nonnegative d) (actual_pure_action_normalized d)
  have hmarg : stateMarginal (occupancy M (purePolicy d) γ) = stateMarginal ρ :=
    actual_stochastic_discounted_fixed_point_unique _ hK.1 hK.2 γ hγ0 hγ1
      M.initial _ _
      (actual_flow_factorization_gives_kernel_fixed_point M γ
        (occupancy M (purePolicy d) γ) (pureAction d)
        (actual_occupancy_satisfies_flow M (purePolicy d) γ hγ0 hγ1) hoccprod)
      (actual_flow_factorization_gives_kernel_fixed_point M γ ρ (pureAction d) hρ hprod)
  funext s a
  calc
    _ = stateMarginal (occupancy M (purePolicy d) γ) s * pureAction d s a :=
      (hoccprod s a).symm
    _ = stateMarginal ρ s * pureAction d s a :=
      congrArg (fun x : S → ℝ => x s * pureAction d s a) hmarg
    _ = ρ s a := hprod s a

/-- Every deterministic stationary occupancy is an actual Mathlib extreme point.
The converse classification of all extreme points is a separate claim. -/
theorem actual_pure_policy_occupancy_is_extreme_point
    (M : Model S A) (d : S → A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    occupancy M (purePolicy d) γ ∈
      Set.extremePoints ℝ {ρ | FlowFeasible M γ ρ} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨actual_occupancy_satisfies_flow M (purePolicy d) γ hγ0 hγ1, ?_⟩
  intro ρ hρ σ hσ hsegment
  rcases hsegment with ⟨u, v, hu, hv, huv, he⟩
  have hsupport : ∀ s a, a ≠ d s → ρ s a = 0 := by
    intro s a ha
    have hcoord := congrArg (fun x : S → A → ℝ => x s a) he
    change u * ρ s a + v * σ s a = occupancy M (purePolicy d) γ s a at hcoord
    rw [actual_pure_policy_occupancy_has_only_selected_actions M d γ hγ0 hγ1 s a ha]
      at hcoord
    have hzero : u * ρ s a = 0 := by
      nlinarith [mul_nonneg hu.le (hρ.1 s a), mul_nonneg hv.le (hσ.1 s a)]
    exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hu)
  exact (actual_flow_supported_on_selected_actions_is_pure_policy_occupancy
    M d γ hγ0 hγ1 ρ hρ hsupport).symm

end SafeLearning.CompleteFiniteCMDPDeterministicVertices
