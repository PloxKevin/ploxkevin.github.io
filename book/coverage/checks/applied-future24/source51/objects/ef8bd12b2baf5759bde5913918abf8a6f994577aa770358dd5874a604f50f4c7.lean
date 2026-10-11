import SafeLearning.CompleteFiniteCMDPRecovery

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPLinearProgram

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery

universe u v w
variable {S : Type u} {A : Type v} {I : Type w} [Fintype S] [Fintype A] [Fintype I]

def rewardFunctional (r : S → A → ℝ) : (S → A → ℝ) →ₗ[ℝ] ℝ where
  toFun ρ := ∑ s, ∑ a, ρ s a * r s a
  map_add' ρ σ := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' u ρ := by simp [mul_assoc, Finset.mul_sum]

theorem actual_reward_functional_continuous (r : S → A → ℝ) :
    Continuous (rewardFunctional r) := by
  change Continuous (fun ρ : S → A → ℝ => ∑ s, ∑ a, ρ s a * r s a)
  fun_prop

theorem actual_flow_polyhedron_closed (M : Model S A) (γ : ℝ) :
    IsClosed {ρ | FlowFeasible M γ ρ} := by
  have he : {ρ | FlowFeasible M γ ρ} =
      (⋂ s, ⋂ a, {ρ : S → A → ℝ | 0 ≤ ρ s a}) ∩
      (⋂ t, {ρ : S → A → ℝ | (∑ a, ρ t a) =
        (1 - γ) * M.initial t + γ * ∑ s, ∑ a, ρ s a * M.transition s a t}) := by
    ext ρ
    simp [FlowFeasible, stateMarginal]
  rw [he]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro a
    apply isClosed_le continuous_const
    fun_prop
  · apply isClosed_iInter
    intro t
    apply isClosed_eq <;> fun_prop

theorem actual_flow_polyhedron_in_unit_box (M : Model S A) (γ : ℝ) (hγ1 : γ < 1) :
    {ρ | FlowFeasible M γ ρ} ⊆ Set.Icc (0 : S → A → ℝ) 1 := by
  intro ρ hρ
  constructor
  · intro s a
    exact (actual_feasible_coordinate_bound M γ hγ1 ρ hρ s a).1
  · intro s a
    exact (actual_feasible_coordinate_bound M γ hγ1 ρ hρ s a).2

theorem actual_flow_polyhedron_compact (M : Model S A) (γ : ℝ) (hγ1 : γ < 1) :
    IsCompact {ρ | FlowFeasible M γ ρ} :=
  isCompact_Icc.of_isClosed_subset (actual_flow_polyhedron_closed M γ)
    (actual_flow_polyhedron_in_unit_box M γ hγ1)

theorem actual_flow_polyhedron_bounded (M : Model S A) (γ : ℝ) (hγ1 : γ < 1) :
    Bornology.IsBounded {ρ | FlowFeasible M γ ρ} :=
  (actual_flow_polyhedron_compact M γ hγ1).isBounded

def CostFeasible (M : Model S A) (γ : ℝ) (cost : I → S → A → ℝ)
    (budget : I → ℝ) (ρ : S → A → ℝ) : Prop :=
  FlowFeasible M γ ρ ∧ ∀ i, rewardFunctional (cost i) ρ ≤ (1 - γ) * budget i

theorem actual_cost_feasible_closed (M : Model S A) (γ : ℝ)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    IsClosed {ρ | CostFeasible M γ cost budget ρ} := by
  have he : {ρ | CostFeasible M γ cost budget ρ} =
      {ρ | FlowFeasible M γ ρ} ∩
      (⋂ i, {ρ | rewardFunctional (cost i) ρ ≤ (1 - γ) * budget i}) := by
    ext ρ
    simp [CostFeasible]
  rw [he]
  exact (actual_flow_polyhedron_closed M γ).inter
    (isClosed_iInter (fun i => isClosed_le (actual_reward_functional_continuous (cost i))
      continuous_const))

theorem actual_cost_feasible_compact (M : Model S A) (γ : ℝ) (hγ1 : γ < 1)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    IsCompact {ρ | CostFeasible M γ cost budget ρ} :=
  (actual_flow_polyhedron_compact M γ hγ1).of_isClosed_subset
    (actual_cost_feasible_closed M γ cost budget) (fun _ h => h.1)

theorem actual_cost_feasible_convex (M : Model S A) (γ : ℝ)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    Convex ℝ {ρ | CostFeasible M γ cost budget ρ} := by
  intro ρ hρ σ hσ u v hu hv huv
  refine ⟨actual_nonnegative_flow_polyhedron_is_convex M γ hρ.1 hσ.1 hu hv huv, ?_⟩
  intro i
  rw [map_add, map_smul, map_smul]
  change u * rewardFunctional (cost i) ρ + v * rewardFunctional (cost i) σ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left (hρ.2 i) hu,
    mul_le_mul_of_nonneg_left (hσ.2 i) hv,
    congrArg (fun x : ℝ => x * ((1 - γ) * budget i)) huv]

theorem actual_policy_cost_feasible_iff (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    (∀ i, expectedReturn M π γ (cost i) ≤ budget i) ↔
      CostFeasible M γ cost budget (occupancy M π γ) := by
  have hp : 0 < 1 - γ := sub_pos.mpr hγ1
  constructor
  · intro h
    refine ⟨actual_occupancy_satisfies_flow M π γ hγ0 hγ1, ?_⟩
    intro i
    have hi := h i
    rw [actual_reward_return_identity M π γ hγ0 hγ1] at hi
    simpa only [rewardFunctional, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using
      (div_le_iff₀ hp).mp hi
  · intro h i
    rw [actual_reward_return_identity M π γ hγ0 hγ1]
    apply (div_le_iff₀ hp).mpr
    simpa only [rewardFunctional, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using h.2 i

def returnPairMap (γ : ℝ) (reward cost : S → A → ℝ) :
    (S → A → ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (((1 - γ)⁻¹) • rewardFunctional reward).prod (((1 - γ)⁻¹) • rewardFunctional cost)

def achievablePairs (M : Model S A) (γ : ℝ) (reward cost : S → A → ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ π : Policy S A, z = (expectedReturn M π γ reward, expectedReturn M π γ cost)}

theorem actual_achievable_pairs_equal_flow_linear_image (M : Model S A) (a₀ : A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (reward cost : S → A → ℝ) :
    achievablePairs M γ reward cost = returnPairMap γ reward cost '' {ρ | FlowFeasible M γ ρ} := by
  have hpair (π : Policy S A) :
      returnPairMap γ reward cost (occupancy M π γ) =
        (expectedReturn M π γ reward, expectedReturn M π γ cost) := by
    apply Prod.ext <;>
      simp [returnPairMap, rewardFunctional,
        actual_reward_return_identity M π γ hγ0 hγ1, div_eq_mul_inv, mul_comm]
  ext z
  constructor
  · rintro ⟨π, rfl⟩
    exact ⟨occupancy M π γ, actual_occupancy_satisfies_flow M π γ hγ0 hγ1, hpair π⟩
  · rintro ⟨ρ, hρ, rfl⟩
    let π := recoveredPolicy a₀ ρ hρ.1
    refine ⟨π, ?_⟩
    rw [← hpair π]
    exact congrArg (returnPairMap γ reward cost)
      (actual_every_feasible_flow_is_realized_by_recovered_stationary_policy
        M a₀ γ hγ0 hγ1 ρ hρ).symm

theorem actual_achievable_pairs_convex (M : Model S A) (a₀ : A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (reward cost : S → A → ℝ) :
    Convex ℝ (achievablePairs M γ reward cost) := by
  rw [actual_achievable_pairs_equal_flow_linear_image M a₀ γ hγ0 hγ1]
  exact (actual_nonnegative_flow_polyhedron_is_convex M γ).linear_image
    (returnPairMap γ reward cost)

def flowFunctional (M : Model S A) (γ : ℝ) (t : S) : (S → A → ℝ) →ₗ[ℝ] ℝ where
  toFun ρ := stateMarginal ρ t - γ * ∑ s, ∑ a, ρ s a * M.transition s a t
  map_add' ρ σ := by simp [stateMarginal, add_mul, Finset.sum_add_distrib]; ring
  map_smul' u ρ := by
    change (∑ a, u * ρ t a) - γ * (∑ s, ∑ a, (u * ρ s a) * M.transition s a t) =
      u * ((∑ a, ρ t a) - γ * (∑ s, ∑ a, ρ s a * M.transition s a t))
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

def negativeCoordinate (s : S) (a : A) : (S → A → ℝ) →ₗ[ℝ] ℝ where
  toFun ρ := -ρ s a
  map_add' ρ σ := by change -(ρ s a + σ s a) = -ρ s a + -σ s a; ring
  map_smul' u ρ := by simp

/-- Nonnegativity rows, each flow equation as two rows, and all budget rows. -/
abbrev LPIndex := (S × A) ⊕ (S ⊕ (S ⊕ I))

def lpRow (M : Model S A) (γ : ℝ) (cost : I → S → A → ℝ) :
    LPIndex (S := S) (A := A) (I := I) → ((S → A → ℝ) →ₗ[ℝ] ℝ)
  | .inl (s,a) => negativeCoordinate s a
  | .inr (.inl t) => flowFunctional M γ t
  | .inr (.inr (.inl t)) => -flowFunctional M γ t
  | .inr (.inr (.inr i)) => rewardFunctional (cost i)

def lpRhs (M : Model S A) (γ : ℝ) (budget : I → ℝ) :
    LPIndex (S := S) (A := A) (I := I) → ℝ
  | .inl _ => 0
  | .inr (.inl t) => (1 - γ) * M.initial t
  | .inr (.inr (.inl t)) => -((1 - γ) * M.initial t)
  | .inr (.inr (.inr i)) => (1 - γ) * budget i

theorem actual_cost_feasible_finite_linear_halfspaces (M : Model S A) (γ : ℝ)
    (cost : I → S → A → ℝ) (budget : I → ℝ) (ρ : S → A → ℝ) :
    CostFeasible M γ cost budget ρ ↔
      ∀ j, lpRow M γ cost j ρ ≤ lpRhs M γ budget j := by
  constructor
  · rintro ⟨⟨hρ,hflow⟩,hcost⟩ j
    rcases j with ⟨s,a⟩ | (t | (t | i))
    · simpa [lpRow,lpRhs,negativeCoordinate] using neg_nonpos.mpr (hρ s a)
    · change stateMarginal ρ t - γ * (∑ s, ∑ a, ρ s a * M.transition s a t) ≤
        (1 - γ) * M.initial t
      linarith [hflow t]
    · change -(stateMarginal ρ t - γ * (∑ s, ∑ a, ρ s a * M.transition s a t)) ≤
        -((1 - γ) * M.initial t)
      linarith [hflow t]
    · exact hcost i
  · intro h
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro s a
      have hi := h (.inl (s,a))
      change -ρ s a ≤ 0 at hi
      linarith
    · intro t
      have hupper := h (.inr (.inl t))
      have hlower := h (.inr (.inr (.inl t)))
      change stateMarginal ρ t - γ * (∑ s, ∑ a, ρ s a * M.transition s a t) ≤
        (1 - γ) * M.initial t at hupper
      change -(stateMarginal ρ t - γ * (∑ s, ∑ a, ρ s a * M.transition s a t)) ≤
        -((1 - γ) * M.initial t) at hlower
      linarith
    · intro i
      exact h (.inr (.inr (.inr i)))

/-- A finite bounded linear-halfspace representation, the printed definition of polytope. -/
theorem actual_cost_feasible_bounded_finite_halfspace_representation
    (M : Model S A) (γ : ℝ) (hγ1 : γ < 1)
    (cost : I → S → A → ℝ) (budget : I → ℝ) :
    (∃ (J : Type (max u v w)) (_ : Fintype J) (row : J → ((S → A → ℝ) →ₗ[ℝ] ℝ))
        (rhs : J → ℝ), {ρ | CostFeasible M γ cost budget ρ} =
        {ρ | ∀ j, row j ρ ≤ rhs j}) ∧
      Bornology.IsBounded {ρ | CostFeasible M γ cost budget ρ} := by
  constructor
  · refine ⟨LPIndex (S := S) (A := A) (I := I), inferInstance,
      lpRow M γ cost, lpRhs M γ budget, ?_⟩
    ext ρ
    exact actual_cost_feasible_finite_linear_halfspaces M γ cost budget ρ
  · exact (actual_cost_feasible_compact M γ hγ1 cost budget).isBounded

theorem actual_feasible_lp_has_an_optimal_recovered_policy
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : S → A → ℝ) (cost : I → S → A → ℝ) (budget : I → ℝ)
    (hne : ∃ π : Policy S A, ∀ i, expectedReturn M π γ (cost i) ≤ budget i) :
    ∃ (ρ : S → A → ℝ) (π : Policy S A),
      CostFeasible M γ cost budget ρ ∧ occupancy M π γ = ρ ∧
      (∀ i, expectedReturn M π γ (cost i) ≤ budget i) ∧
      (∀ σ, CostFeasible M γ cost budget σ → rewardFunctional reward σ ≤ rewardFunctional reward ρ) ∧
      (∀ ψ : Policy S A, (∀ i, expectedReturn M ψ γ (cost i) ≤ budget i) →
        expectedReturn M ψ γ reward ≤ expectedReturn M π γ reward) := by
  obtain ⟨ψ₀, hψ₀⟩ := hne
  have hset : {ρ | CostFeasible M γ cost budget ρ}.Nonempty :=
    ⟨occupancy M ψ₀ γ, (actual_policy_cost_feasible_iff M ψ₀ γ hγ0 hγ1 cost budget).mp hψ₀⟩
  obtain ⟨ρ,hρ,hmax⟩ := (actual_cost_feasible_compact M γ hγ1 cost budget).exists_isMaxOn
    hset (actual_reward_functional_continuous reward).continuousOn
  let π := recoveredPolicy a₀ ρ hρ.1.1
  have he : occupancy M π γ = ρ :=
    actual_every_feasible_flow_is_realized_by_recovered_stationary_policy M a₀ γ hγ0 hγ1 ρ hρ.1
  have hπ : ∀ i, expectedReturn M π γ (cost i) ≤ budget i := by
    apply (actual_policy_cost_feasible_iff M π γ hγ0 hγ1 cost budget).mpr
    rwa [he]
  refine ⟨ρ,π,hρ,he,hπ,hmax,?_⟩
  intro ψ hψ
  have h := hmax ((actual_policy_cost_feasible_iff M ψ γ hγ0 hγ1 cost budget).mp hψ)
  rw [actual_reward_return_identity M ψ γ hγ0 hγ1 reward,
    actual_reward_return_identity M π γ hγ0 hγ1 reward, he]
  exact div_le_div_of_nonneg_right h (sub_pos.mpr hγ1).le

end SafeLearning.CompleteFiniteCMDPLinearProgram
