import SafeLearning.CompleteAppliedTinyNetwork

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open SafeLearning.CompleteAppliedTinyNetwork
namespace SafeLearning.CompleteAppliedTinyNetworkPositive

theorem actual_positive_output_iff_both_strict_boundary_halfspaces (x : E) :
    0<network x ↔ 2<x 0+x 1 ∧ 2< -x 0+3*x 1 := by
  rw [(actual_network_is_the_literal_two_two_one_ReLU_composition x).2]
  by_cases h1 : 0≤x 0+x 1-1
  · rw [max_eq_left h1]
    by_cases h2 : 0≤x 0-x 1
    · rw [max_eq_left h2]
      constructor
      · intro h;constructor <;> linarith
      · rintro ⟨_,h⟩;linarith
    · rw [max_eq_right (le_of_not_ge h2)]
      constructor
      · intro h;constructor <;> linarith
      · rintro ⟨h,_⟩;linarith
  · rw [max_eq_right (le_of_not_ge h1)]
    have hmax : 0 ≤ max (x 0-x 1) 0 := le_max_right _ _
    constructor
    · intro h;exfalso;linarith
    · rintro ⟨h,_⟩;exfalso;linarith

theorem actual_positive_output_iff_above_the_kinked_boundary (x : E) :
    0<network x ↔ max (2-x 0) ((x 0+2)/3)<x 1 := by
  rw [actual_positive_output_iff_both_strict_boundary_halfspaces,max_lt_iff]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem actual_boundary_graph_is_exactly_the_max_of_its_two_lines (x : E) :
    network x=0 ↔ x 1=max (2-x 0) ((x 0+2)/3) := by
  rw [actual_zero_boundary_has_exactly_the_two_literal_branches]
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · rw [max_eq_left (by linarith)]
      linarith
    · rw [max_eq_right (by linarith)]
      linarith
  · intro h
    by_cases hx : (2-x 0)≤(x 0+2)/3
    · rw [max_eq_right hx] at h
      right;constructor <;> linarith
    · rw [max_eq_left (le_of_not_ge hx)] at h
      left;constructor <;> linarith

end SafeLearning.CompleteAppliedTinyNetworkPositive
