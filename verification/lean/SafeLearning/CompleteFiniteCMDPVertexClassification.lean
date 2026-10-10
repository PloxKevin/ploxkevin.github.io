import SafeLearning.CompleteFiniteCMDPActiveFlow

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPVertexClassification

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery SafeLearning.CompleteFiniteCMDPDeterministicVertices
  SafeLearning.CompleteFiniteNonnegativeAffineExtrema SafeLearning.CompleteFiniteCMDPActiveFlow

variable {S A : Type*} [Fintype S] [Fintype A]

def activeRestrictionLinearMap (ρ : S → A → ℝ) :
    (S → ℝ) →ₗ[ℝ] (PositiveSupport (stateMarginal ρ) → ℝ) where
  toFun x s := x s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def activeSupportFlowLinearMap (M : Model S A) (γ : ℝ) (ρ : S → A → ℝ) :
    (PositiveSupport (fun p : S × A => ρ p.1 p.2) → ℝ) →ₗ[ℝ]
      (PositiveSupport (stateMarginal ρ) → ℝ) :=
  (activeRestrictionLinearMap ρ).comp
    ((flowLinearMap M γ).comp (supportExtensionLinearMap (fun p : S × A => ρ p.1 p.2)))

theorem actual_extreme_flow_active_support_map_is_injective
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y}) :
    Function.Injective (activeSupportFlowLinearMap M γ ρ) := by
  classical
  let x : (S × A) → ℝ := fun p => ρ p.1 p.2
  let E := supportExtensionLinearMap x
  let L := flowLinearMap M γ
  have hfull := actual_extreme_point_positive_support_linear_map_is_injective
    L (fun t => (1 - γ) * M.initial t) x
    (actual_flow_extreme_point_is_flat_affine_extreme_point M γ ρ hext)
  intro v w h
  apply hfull
  have hk : L (E (v - w)) = 0 := by
    funext t
    by_cases ht : 0 < stateMarginal ρ t
    · have hc := congrArg (fun z : PositiveSupport (stateMarginal ρ) → ℝ => z ⟨t, ht⟩) h
      change L (E v) t = L (E w) t at hc
      change L (E (v - w)) t = 0
      rw [map_sub, map_sub, Pi.sub_apply]
      exact sub_eq_zero.mpr hc
    · have hz : stateMarginal ρ t = 0 := le_antisymm (le_of_not_gt ht)
        (actual_nonnegative_row_marginal ρ hext.1.1 t)
      exact actual_supported_direction_flow_is_zero_on_inactive_rows M γ hγ0 hγ1
        ρ hext.1 (E (v - w))
        (fun p hp => by simp [E, x, supportExtensionLinearMap, supportExtension, hp]) t hz
  have he : (L.comp E) v - (L.comp E) w = 0 := by
    simpa only [map_sub, LinearMap.comp_apply] using hk
  exact sub_eq_zero.mp he

theorem actual_extreme_flow_positive_coordinates_cardinality_le_active_states
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y}) :
    Fintype.card (PositiveSupport (fun p : S × A => ρ p.1 p.2)) ≤
      Fintype.card (PositiveSupport (stateMarginal ρ)) := by
  classical
  have h := LinearMap.finrank_le_finrank_of_injective
    (actual_extreme_flow_active_support_map_is_injective M γ hγ0 hγ1 ρ hext)
  simpa only [Module.finrank_fintype_fun_eq_card] using h

def positiveStateProjection (ρ : S → A → ℝ) (hρ : ∀ s a, 0 ≤ ρ s a) :
    PositiveSupport (fun p : S × A => ρ p.1 p.2) → PositiveSupport (stateMarginal ρ) :=
  fun p => ⟨p.val.1, lt_of_lt_of_le p.property
    (Finset.single_le_sum (s := Finset.univ) (fun a _ => hρ p.val.1 a)
      (Finset.mem_univ p.val.2))⟩

theorem actual_positive_row_has_positive_action (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) (s : S) (hs : 0 < stateMarginal ρ s) :
    ∃ a, 0 < ρ s a := by
  obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg (fun a _ => hρ s a)).mp hs
  exact ⟨a, ha⟩

theorem actual_positive_state_projection_is_surjective (ρ : S → A → ℝ)
    (hρ : ∀ s a, 0 ≤ ρ s a) : Function.Surjective (positiveStateProjection ρ hρ) := by
  intro s
  obtain ⟨a, ha⟩ := actual_positive_row_has_positive_action ρ hρ s.val s.property
  refine ⟨⟨(s.val, a), ha⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem actual_extreme_flow_has_at_most_one_positive_action_per_state
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y})
    (s : S) (a b : A) (ha : 0 < ρ s a) (hb : 0 < ρ s b) : a = b := by
  classical
  have hsurj := actual_positive_state_projection_is_surjective ρ hext.1.1
  have hcard := actual_extreme_flow_positive_coordinates_cardinality_le_active_states
    M γ hγ0 hγ1 ρ hext
  have heq := le_antisymm hcard (Fintype.card_le_of_surjective _ hsurj)
  have hinj := ((Fintype.bijective_iff_surjective_and_card
    (positiveStateProjection ρ hext.1.1)).mpr ⟨hsurj, heq⟩).1
  have hs : positiveStateProjection ρ hext.1.1 ⟨(s, a), ha⟩ =
      positiveStateProjection ρ hext.1.1 ⟨(s, b), hb⟩ := by
    apply Subtype.ext
    rfl
  exact congrArg (fun p : PositiveSupport (fun p : S × A => ρ p.1 p.2) => p.val.2)
    (hinj hs)

theorem actual_feasible_flow_action_type_is_nonempty
    (M : Model S A) (γ : ℝ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hρ : FlowFeasible M γ ρ) : Nonempty A := by
  cases isEmpty_or_nonempty A with
  | inl h =>
    letI := h
    have hm := actual_all_feasible_flows_have_total_mass_one M γ hγ1 ρ hρ
    simp at hm
  | inr h => exact h

theorem actual_every_extreme_flow_has_a_deterministic_supported_policy
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y}) :
    ∃ d : S → A, ∀ s a, a ≠ d s → ρ s a = 0 := by
  classical
  letI := actual_feasible_flow_action_type_is_nonempty M γ hγ1 ρ hext.1
  let d (s : S) : A := if hs : 0 < stateMarginal ρ s then
      Classical.choose (actual_positive_row_has_positive_action ρ hext.1.1 s hs)
    else Classical.arbitrary A
  refine ⟨d, ?_⟩
  intro s a ha
  by_cases hs : 0 < stateMarginal ρ s
  · have hd : 0 < ρ s (d s) := by
      simp only [d, dif_pos hs]
      exact Classical.choose_spec (actual_positive_row_has_positive_action ρ hext.1.1 s hs)
    have hn : ¬ 0 < ρ s a := fun hpos => ha
      (actual_extreme_flow_has_at_most_one_positive_action_per_state
        M γ hγ0 hγ1 ρ hext s a (d s) hpos hd)
    exact le_antisymm (le_of_not_gt hn) (hext.1.1 s a)
  · have hz : stateMarginal ρ s = 0 := le_antisymm (le_of_not_gt hs)
      (actual_nonnegative_row_marginal ρ hext.1.1 s)
    exact actual_zero_nonnegative_row_has_zero_coordinates ρ hext.1.1 s hz a

theorem actual_all_flow_vertices_are_deterministic_stationary_occupancies
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y}) :
    ∃ d : S → A, ρ = occupancy M (purePolicy d) γ := by
  obtain ⟨d, hd⟩ := actual_every_extreme_flow_has_a_deterministic_supported_policy
    M γ hγ0 hγ1 ρ hext
  exact ⟨d, (actual_flow_supported_on_selected_actions_is_pure_policy_occupancy
    M d γ hγ0 hγ1 ρ hext.1 hd).symm⟩

theorem actual_flow_extreme_point_iff_deterministic_stationary_occupancy
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → A → ℝ) :
    ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y} ↔
      ∃ d : S → A, ρ = occupancy M (purePolicy d) γ := by
  constructor
  · exact actual_all_flow_vertices_are_deterministic_stationary_occupancies M γ hγ0 hγ1 ρ
  · rintro ⟨d, rfl⟩
    exact actual_pure_policy_occupancy_is_extreme_point M d γ hγ0 hγ1

end SafeLearning.CompleteFiniteCMDPVertexClassification
