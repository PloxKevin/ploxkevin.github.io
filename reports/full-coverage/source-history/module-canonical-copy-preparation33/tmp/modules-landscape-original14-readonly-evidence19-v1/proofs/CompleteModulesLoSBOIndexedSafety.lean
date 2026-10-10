import SafeLearning.CompleteModulesSafeExploration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesLoSBOIndexedSafety

def actualSourceRounds {X : Type*} (seed : Set X) (query : ℕ → X)
    (observation : ℕ → ℝ) (upperNoise : X → ℕ → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) : ℕ → Set X
  | 0 => seed
  | 1 => seed
  | n+2 => actualSourceRounds seed query observation upperNoise cost threshold (n+1) ∪
      {candidate | threshold ≤ observation (n+1)-upperNoise (query (n+1)) (n+1)-cost (query (n+1)) candidate}

theorem actual_one_based_initial_round_and_source_time_dependent_update
    {X : Type*} (seed : Set X) (query : ℕ → X) (observation : ℕ → ℝ)
    (upperNoise : X → ℕ → ℝ) (cost : X → X → ℝ) (threshold : ℝ) :
    actualSourceRounds seed query observation upperNoise cost threshold 0=seed ∧
      actualSourceRounds seed query observation upperNoise cost threshold 1=seed ∧
      ∀ t ≥ 2, actualSourceRounds seed query observation upperNoise cost threshold t=
        actualSourceRounds seed query observation upperNoise cost threshold (t-1) ∪
          {candidate | threshold ≤ observation (t-1)-upperNoise (query (t-1)) (t-1)-cost (query (t-1)) candidate} := by
  refine ⟨rfl,rfl,?_⟩
  intro t ht
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ht
  simp [Nat.add_comm,actualSourceRounds]

theorem actual_source_every_round_and_any_admissible_query_are_safe_using_only_upper_noise
    {X : Type*} (f : X → ℝ) (seed : Set X) (query : ℕ → X)
    (observation noise : ℕ → ℝ) (upperNoise : X → ℕ → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hobs : ∀ t ≥ 1, observation t=f (query t)+noise t)
    (hnoise : ∀ t ≥ 1, noise t ≤ upperNoise (query t) t)
    (hregularity : ∀ a x, f a-cost a x ≤ f x)
    (hquery : ∀ t ≥ 1, query t ∈ actualSourceRounds seed query observation upperNoise cost threshold t) :
    (∀ t x, x ∈ actualSourceRounds seed query observation upperNoise cost threshold t → threshold ≤ f x) ∧
      ∀ t ≥ 1, threshold ≤ f (query t) := by
  have hs : ∀ t x, x ∈ actualSourceRounds seed query observation upperNoise cost threshold t → threshold ≤ f x := by
    intro t
    induction t with
    | zero => exact hseed
    | succ t ih =>
      cases t with
      | zero => exact hseed
      | succ n =>
        intro x hx
        change x ∈ actualSourceRounds seed query observation upperNoise cost threshold (n+1) ∪ _ at hx
        rcases hx with hx | hx
        · exact ih x hx
        · have ho := hobs (n+1) (by omega)
          have hn := hnoise (n+1) (by omega)
          have hr := hregularity (query (n+1)) x
          change threshold ≤ observation (n+1)-upperNoise (query (n+1)) (n+1)-cost (query (n+1)) x at hx
          linarith
  exact ⟨hs,fun t ht => hs t (query t) (hquery t ht)⟩

theorem actual_lipschitz_source_time_dependent_rule_is_safe
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (seed : Set X) (query : ℕ → X)
    (observation noise : ℕ → ℝ) (upperNoise : X → ℕ → ℝ) (L threshold : ℝ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hobs : ∀ t ≥ 1, observation t=f (query t)+noise t)
    (hnoise : ∀ t ≥ 1, noise t ≤ upperNoise (query t) t)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hquery : ∀ t ≥ 1, query t ∈ actualSourceRounds seed query observation upperNoise
      (fun a x => L*dist a x) threshold t) :
    (∀ t x, x ∈ actualSourceRounds seed query observation upperNoise (fun a x => L*dist a x) threshold t → threshold ≤ f x) ∧
      ∀ t ≥ 1, threshold ≤ f (query t) := by
  apply actual_source_every_round_and_any_admissible_query_are_safe_using_only_upper_noise
    f seed query observation noise upperNoise (fun a x => L*dist a x) threshold hseed hobs hnoise
  · intro a x
    have h := (abs_le.mp (hf a x)).2
    linarith
  · exact hquery

theorem actual_negative_noise_only_shrinks_the_certificate_and_lower_error_controls_an_upper_bound
    (actual noise upperError lowerError threshold : ℝ) (cost : ℝ)
    (hn : noise ≤ 0) (hl : -lowerError ≤ noise) :
    (threshold ≤ (actual+noise)-upperError-cost → threshold ≤ actual-upperError-cost) ∧
      actual ≤ (actual+noise)+lowerError := by
  constructor
  · intro hc
    linarith
  · linarith

def actualHolderModulus (C exponent radius : ℝ) : ℝ := C*radius^exponent

theorem actual_positive_holder_modulus_has_the_literal_continuity_monotonicity_and_zero
    (C exponent : ℝ) (hC : 0 < C) (he : 0 < exponent) :
    ContinuousOn (actualHolderModulus C exponent) (Ici 0) ∧
      StrictMonoOn (actualHolderModulus C exponent) (Ici 0) ∧
      actualHolderModulus C exponent 0=0 ∧
      (∀ radius ∈ Ici (0:ℝ), 0 ≤ actualHolderModulus C exponent radius) := by
  refine ⟨((Real.continuous_rpow_const he.le).const_mul C).continuousOn,?_,?_,?_⟩
  · intro a ha b hb hab
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha hab he) hC
  · simp [actualHolderModulus,Real.zero_rpow he.ne']
  · intro radius hr
    exact mul_nonneg hC.le (Real.rpow_nonneg hr exponent)

theorem actual_negative_slack_certifies_nothing_for_every_positive_holder_exponent
    (C exponent slack radius : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ radius) (hs : slack < 0) :
    ¬actualHolderModulus C exponent radius ≤ slack := by
  have hn := mul_nonneg hC (Real.rpow_nonneg hr exponent)
  dsimp [actualHolderModulus]
  linarith

end SafeLearning.CompleteModulesLoSBOIndexedSafety
