import SafeLearning.CompleteModulesLoSBOIndexedSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsLoSBOAssumptionIndependence
open SafeLearning.CompleteModulesLoSBOIndexedSafety

theorem actual_hard_noise_lipschitz_seed_and_admissible_queries_suffice
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (seed : Set X)
    (query : ℕ → X) (observation noise : ℕ → ℝ) (E L threshold : ℝ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hobs : ∀ t ≥ 1, observation t = f (query t) + noise t)
    (hnoise : ∀ t ≥ 1, |noise t| ≤ E)
    (hf : ∀ a x, |f a - f x| ≤ L * dist a x)
    (hquery : ∀ t ≥ 1, query t ∈ actualSourceRounds seed query observation
      (fun _ _ => E) (fun a x => L * dist a x) threshold t) :
    (∀ t x, x ∈ actualSourceRounds seed query observation (fun _ _ => E)
      (fun a x => L * dist a x) threshold t → threshold ≤ f x) ∧
      ∀ t ≥ 1, threshold ≤ f (query t) := by
  exact actual_lipschitz_source_time_dependent_rule_is_safe f seed query observation noise
    (fun _ _ => E) L threshold hseed hobs
    (fun t ht => (abs_le.mp (hnoise t ht)).2) hf hquery

-- Model data and confidence scales may change the selected queries and readings.
-- Every such selection satisfying the literal admissibility and physical bounds is safe.
theorem actual_losbo_safety_for_every_confidence_scale_and_arbitrary_model_data
    {X ModelData : Type*} [PseudoMetricSpace X] (f : X → ℝ) (seed : Set X)
    (query : (ℕ → ℝ) → ModelData → ℕ → X)
    (observation noise : (ℕ → ℝ) → ModelData → ℕ → ℝ) (E L threshold : ℝ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hobs : ∀ β model, ∀ t ≥ 1,
      observation β model t = f (query β model t) + noise β model t)
    (hnoise : ∀ β model, ∀ t ≥ 1, |noise β model t| ≤ E)
    (hf : ∀ a x, |f a - f x| ≤ L * dist a x)
    (hquery : ∀ β model, ∀ t ≥ 1, query β model t ∈
      actualSourceRounds seed (query β model) (observation β model) (fun _ _ => E)
        (fun a x => L * dist a x) threshold t) :
    ∀ β model,
      (∀ t x, x ∈ actualSourceRounds seed (query β model) (observation β model)
        (fun _ _ => E) (fun a x => L * dist a x) threshold t → threshold ≤ f x) ∧
      ∀ t ≥ 1, threshold ≤ f (query β model t) := by
  intro β model
  exact actual_hard_noise_lipschitz_seed_and_admissible_queries_suffice f seed
    (query β model) (observation β model) (noise β model) E L threshold hseed
    (hobs β model) (hnoise β model) hf (hquery β model)

end SafeLearning.CompleteFoundationsLoSBOAssumptionIndependence
