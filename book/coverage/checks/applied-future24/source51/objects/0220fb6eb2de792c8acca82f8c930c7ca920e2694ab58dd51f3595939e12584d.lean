import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace SafeLearning.CompleteAppliedNormLipschitzDefinitions

theorem actual_global_domain_lipschitz_definition_is_the_literal_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (domain : Set E) (f : E→F) (constant : ℝ≥0) :
    LipschitzOnWith constant f domain ↔
      ∀x∈domain,∀y∈domain,‖f x-f y‖≤(constant:ℝ)*‖x-y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul,dist_eq_norm]

theorem actual_local_domain_lipschitz_definition_is_a_genuine_norm_neighborhood_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (domain : Set E) (f : E→F) :
    LocallyLipschitzOn domain f ↔
      ∀point∈domain,∃constant:ℝ≥0,∃neighborhood∈𝓝[domain] point,
        ∀x∈neighborhood,∀y∈neighborhood,‖f x-f y‖≤(constant:ℝ)*‖x-y‖ := by
  simp only [LocallyLipschitzOn,lipschitzOnWith_iff_dist_le_mul,dist_eq_norm]

end SafeLearning.CompleteAppliedNormLipschitzDefinitions
