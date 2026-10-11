import SafeLearning.CompleteModulesSafeOptPracticeNumbers
import SafeLearning.CompleteModulesSafeOptPracticeTheorems

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptPracticeConsequences
open SafeLearning.CompleteModulesSafeOptPracticeNumbers SafeLearning.CompleteModulesSafeOptPracticeTheorems

def actualPotentialMaximizers : Set (Fin 3) := {i | i ∈ expanderSafe ∧ (1:ℝ) ≤ expanderUpper i}

theorem actual_source_expander_example_maximizer_set_eligible_union_and_unique_query :
    actualPotentialMaximizers=({0,1}:Set (Fin 3)) ∧
      actualExpanders ∪ actualPotentialMaximizers=expanderSafe ∧
      IsGreatest ((fun i => expanderUpper i-expanderLower i) '' (actualExpanders ∪ actualPotentialMaximizers)) (4/5:ℝ) ∧
      ∀ i ∈ actualExpanders ∪ actualPotentialMaximizers, expanderUpper i-expanderLower i=4/5 ↔ i=1 := by
  have hm : actualPotentialMaximizers=({0,1}:Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [actualPotentialMaximizers,expanderSafe,expanderUpper]
  have he : actualExpanders ∪ actualPotentialMaximizers=expanderSafe := by
    rw [hm,actual_source_expander_test_is_exactly_the_witness_point_one]
    ext i
    fin_cases i <;> simp [expanderSafe]
  refine ⟨hm,he,?_,?_⟩
  · rw [he]
    constructor
    · exact ⟨1,by simp [expanderSafe],by norm_num [expanderUpper,expanderLower]⟩
    · rintro value ⟨i,hi,rfl⟩
      exact actual_source_expander_problem_maximizers_widths_query_and_no_current_certificate_for_two.2.2.2.1 i hi
  · rw [he]
    exact actual_source_expander_width_query_is_uniquely_one

def outsideValue (i : Fin 2) : ℝ := ![51/50,2] i
def outsideLower (i : Fin 2) : ℝ := ![51/50,2] i
def outsideUpper (i : Fin 2) : ℝ := ![11/10,2] i

theorem actual_source_valid_comparison_intervals_can_leave_a_better_safe_point_outside :
    (∀ i : Fin 2, outsideLower i ≤ outsideValue i ∧ outsideValue i ≤ outsideUpper i ∧ 0 ≤ outsideValue i) ∧
      IsGreatest (outsideUpper '' ({0}:Set (Fin 2))) (11/10:ℝ) ∧
      IsGreatest (outsideLower '' ({0}:Set (Fin 2))) (51/50:ℝ) ∧
      (1:Fin 2) ∉ ({0}:Set (Fin 2)) ∧ outsideValue 0 < outsideValue 1 := by
  refine ⟨?_,?_,?_,by simp,by norm_num [outsideValue]⟩
  · intro i
    fin_cases i <;> norm_num [outsideLower,outsideValue,outsideUpper]
  · constructor
    · exact ⟨0,rfl,by norm_num [outsideUpper]⟩
    · rintro value ⟨i,hi,rfl⟩
      have he : i=0 := hi
      rw [he]
      norm_num [outsideUpper]
  · constructor
    · exact ⟨0,rfl,by norm_num [outsideLower]⟩
    · rintro value ⟨i,hi,rfl⟩
      have he : i=0 := hi
      rw [he]
      norm_num [outsideLower]

theorem actual_nonnegative_grid_lower_bounds_only_give_the_source_negative_point_one_margin
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (hf : LipschitzWith (2:NNReal) f)
    (design grid : Set X) (hgrid : ∀ z ∈ grid, 0 ≤ f z)
    (hcover : ∀ x ∈ design, ∃ z ∈ grid, dist z x ≤ (1/20:ℝ)) :
    ∀ x ∈ design, (-1/10:ℝ) ≤ f x := by
  intro x hx
  obtain ⟨z,hz,hd⟩ := hcover x hx
  have h := actual_metric_lipschitz_lower_confidence_transfer f 2 hf z x 0 (hgrid z hz)
  norm_num only [NNReal.coe_ofNat,zero_sub] at h
  linarith

end SafeLearning.CompleteModulesSafeOptPracticeConsequences
