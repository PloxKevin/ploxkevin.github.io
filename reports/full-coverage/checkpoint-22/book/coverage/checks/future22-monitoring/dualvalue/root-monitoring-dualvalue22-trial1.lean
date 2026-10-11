import SafeLearning.CompleteMonitoringGeometry21
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringDualValue22
open SafeLearning.CompleteMonitoringGeometry21

def values (l1 l2 : ℝ) : Set ℝ := {x | ∃ v, AchievablePolytope v ∧ x=lagrangian l1 l2 v}
def dualValue (l1 l2 : ℝ) : ℝ := sSup (values l1 l2)

private theorem actual_values_bounded_above (l1 l2 : ℝ) : BddAbove (values l1 l2) := by
  refine ⟨1+|l1|+|l2|-(l1+l2)/3,?_⟩
  rintro x ⟨v,⟨h0,h1,h2,hs,hh⟩,rfl⟩
  have hv1 : v.v1 ≤ 1 := by linarith
  have hv2 : v.v2 ≤ 1 := by linarith
  have hp1 : l1*v.v1 ≤ |l1| := le_trans (mul_le_mul_of_nonneg_right (le_abs_self l1) h1) (mul_le_of_le_one_right (abs_nonneg l1) hv1)
  have hp2 : l2*v.v2 ≤ |l2| := le_trans (mul_le_mul_of_nonneg_right (le_abs_self l2) h2) (mul_le_of_le_one_right (abs_nonneg l2) hv2)
  dsimp [lagrangian]
  linarith

theorem actual_dual_value_is_a_genuine_finite_supremum (l1 l2 : ℝ) :
    (values l1 l2).Nonempty ∧ BddAbove (values l1 l2) ∧
    ∀ v, AchievablePolytope v → lagrangian l1 l2 v ≤ dualValue l1 l2 := by
  have hop := actual_four_vertices_and_primal_optimum_in_the_polytope
  refine ⟨⟨lagrangian l1 l2 vertex1,vertex1,hop.1,rfl⟩,actual_values_bounded_above l1 l2,?_⟩
  intro v hv
  exact le_csSup (actual_values_bounded_above l1 l2) ⟨v,hv,rfl⟩

theorem actual_unit_dual_prices_have_value_one_third : dualValue 1 1=1/3 := by
  have he : values 1 1={(1/3:ℝ)} := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      simpa only [Set.mem_singleton_iff] using actual_lagrangian_is_constant_at_the_dual_prices v hv
    · intro hx
      have hop := actual_four_vertices_and_primal_optimum_in_the_polytope
      refine ⟨optimum,hop.2.2.2.2.1,?_⟩
      simpa only [Set.mem_singleton_iff,actual_optimum_lagrangian_value_for_any_prices] using hx
  simp [dualValue,he]

theorem actual_every_dual_price_pair_has_value_at_least_one_third (l1 l2 : ℝ) :
    1/3 ≤ dualValue l1 l2 := by
  have hop := actual_four_vertices_and_primal_optimum_in_the_polytope
  have h := (actual_dual_value_is_a_genuine_finite_supremum l1 l2).2.2 optimum hop.2.2.2.2.1
  simpa only [actual_optimum_lagrangian_value_for_any_prices] using h

theorem actual_unit_prices_are_the_unique_dual_optimum (l1 l2 : ℝ) :
    dualValue l1 l2=1/3 ↔ l1=1 ∧ l2=1 := by
  constructor
  · intro h
    have hop := actual_four_vertices_and_primal_optimum_in_the_polytope
    apply actual_primal_optimum_maximizes_only_at_exact_dual_prices
    refine ⟨hop.2.2.2.2.1,?_⟩
    intro v hv
    have hb := (actual_dual_value_is_a_genuine_finite_supremum l1 l2).2.2 v hv
    rw [h,actual_optimum_lagrangian_value_for_any_prices]
    exact hb
  · rintro ⟨rfl,rfl⟩
    exact actual_unit_dual_prices_have_value_one_third
end SafeLearning.CompleteMonitoringDualValue22
