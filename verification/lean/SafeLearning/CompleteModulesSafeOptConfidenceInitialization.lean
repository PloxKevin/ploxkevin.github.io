import SafeLearning.CompleteModulesSafeOptConfidenceIntersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptConfidenceInitialization
open SafeLearning.CompleteModulesSafeOptConfidenceIntersections

theorem actual_seed_halfline_intersected_with_the_first_band_has_the_literal_floor
    (threshold lower upper : ℝ) :
    Ici threshold ∩ Icc lower upper=Icc (max threshold lower) upper := by
  ext value
  simp only [mem_inter_iff,mem_Ici,mem_Icc,max_le_iff]
  tauto

theorem actual_source_seed_initial_confidence_interval_has_the_derived_maximum_lower_endpoint
    {X : Type*} (seed : Set X) (threshold : ℝ) (raw : ℕ → X → Set ℝ)
    (x : X) (hx : x ∈ seed) (lower upper : ℝ) (hband : raw 1 x=Icc lower upper) :
    actualConfidence seed threshold raw 1 x=Icc (max threshold lower) upper ∧
      threshold ≤ max threshold lower := by
  classical
  refine ⟨?_,le_max_left _ _⟩
  have he : actualConfidence seed threshold raw 1 x=Ici threshold ∩ raw 1 x := by
    ext value
    simp [actualConfidence,hx,Nat.lt_one_iff]
  rw [he,hband,actual_seed_halfline_intersected_with_the_first_band_has_the_literal_floor]

theorem actual_seed_truth_in_the_band_makes_the_floor_a_genuine_least_confidence_value
    {X : Type*} (seed : Set X) (threshold : ℝ) (raw : ℕ → X → Set ℝ)
    (x : X) (hx : x ∈ seed) (lower upper value : ℝ) (hband : raw 1 x=Icc lower upper)
    (hseed : threshold≤value) (hvalue : value ∈ raw 1 x) :
    IsLeast (actualConfidence seed threshold raw 1 x) (max threshold lower) := by
  rw [(actual_source_seed_initial_confidence_interval_has_the_derived_maximum_lower_endpoint seed threshold raw x hx lower upper hband).1]
  rw [hband] at hvalue
  have hfit : max threshold lower≤upper := max_le (hseed.trans hvalue.2) (hvalue.1.trans hvalue.2)
  exact ⟨⟨le_rfl,hfit⟩,fun _ h => h.1⟩

end SafeLearning.CompleteModulesSafeOptConfidenceInitialization
