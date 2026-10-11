import SafeLearning.CompleteModulesLoSBOIndexedSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLoSBOGridUpdates
open SafeLearning.CompleteModulesLoSBOIndexedSafety SafeLearning.CompleteModulesSafeExploration

def sourceCoordinate (i : Fin 11) : ℝ := (i.val:ℝ)/10
def sourceQuery (n : ℕ) : Fin 11 := if n=2 then 9 else if n=3 then 1 else 5
def sourceObservation (n : ℕ) : ℝ := if n=1 then 7/5 else if n=2 then 4/5 else 1/4
def sourceCost (L : ℝ) (i j : Fin 11) : ℝ := L*|sourceCoordinate i-sourceCoordinate j|
def sourceRounds : ℕ → Set (Fin 11) := actualSourceRounds {5} sourceQuery sourceObservation
  (fun _ _ => 1/5) (sourceCost 3) 0
def sourceFirstExpanded : Set (Fin 11) := {i | 1 ≤ i.val ∧ i.val ≤ 9}
def sourceSecondExpanded : Set (Fin 11) := {i | 1 ≤ i.val}
def sourceSecondConstraint : Set (Fin 11) :=
  {5} ∪ {i | 0 ≤ (7/20:ℝ)-1/10-sourceCost 1 5 i}
def sourceMultiFirst : Set (Fin 11) := sourceFirstExpanded ∩ sourceSecondConstraint

theorem actual_source_coordinate_grid_has_no_duplicate_inputs : Function.Injective sourceCoordinate := by
  intro i j he
  unfold sourceCoordinate at he
  have hv : (i.val:ℝ)=(j.val:ℝ) := by linarith
  exact Fin.ext (Nat.cast_inj.mp hv)

theorem actual_source_three_observation_radii_are_the_printed_values :
    ((7/5:ℝ)-1/5)/3=2/5 ∧ ((4/5:ℝ)-1/5)/3=1/5 ∧
      ((1/4:ℝ)-1/5)/3=1/60 ∧ |(1/60:ℝ)-17/1000|<1/2000 ∧
      (1/60:ℝ)<1/10 ∧ ((7/20:ℝ)-1/10)/1=1/4 ∧
      ((7/5:ℝ)-1/5)/2=3/5 := by norm_num

theorem actual_source_one_based_safe_sets_are_exactly_the_displayed_grid_points :
    sourceRounds 0=({5}:Set (Fin 11)) ∧ sourceRounds 1=({5}:Set (Fin 11)) ∧
      sourceRounds 2=sourceFirstExpanded ∧ sourceRounds 3=sourceSecondExpanded ∧
      sourceRounds 4=sourceRounds 3 := by
  refine ⟨rfl,rfl,?_,?_,?_⟩
  all_goals ext i
  all_goals fin_cases i <;>
    norm_num [sourceRounds,actualSourceRounds,sourceQuery,sourceObservation,sourceCost,
      sourceCoordinate,sourceFirstExpanded,sourceSecondExpanded]

theorem actual_source_all_three_planned_queries_are_admissible_for_the_first_constraint :
    sourceQuery 1 ∈ sourceRounds 1 ∧ sourceQuery 2 ∈ sourceRounds 2 ∧
      sourceQuery 3 ∈ sourceRounds 3 := by
  norm_num [sourceRounds,actualSourceRounds,sourceQuery,sourceObservation,sourceCost,sourceCoordinate]

theorem actual_source_second_constraint_intersection_excludes_the_planned_point_nine_query :
    sourceSecondConstraint={i | 3 ≤ i.val ∧ i.val ≤ 7} ∧
      sourceMultiFirst={i | 3 ≤ i.val ∧ i.val ≤ 7} ∧
      (9:Fin 11) ∉ sourceMultiFirst ∧ (3:Fin 11) ∈ sourceMultiFirst ∧
      (7:Fin 11) ∈ sourceMultiFirst := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · ext i
    fin_cases i <;> norm_num [sourceSecondConstraint,sourceCost,sourceCoordinate]
  · ext i
    fin_cases i <;> norm_num [sourceMultiFirst,sourceFirstExpanded,sourceSecondConstraint,sourceCost,sourceCoordinate]
  · norm_num [sourceMultiFirst,sourceFirstExpanded,sourceSecondConstraint,sourceCost,sourceCoordinate]
  · norm_num [sourceMultiFirst,sourceFirstExpanded,sourceSecondConstraint,sourceCost,sourceCoordinate]
  · norm_num [sourceMultiFirst,sourceFirstExpanded,sourceSecondConstraint,sourceCost,sourceCoordinate]

def compatibleUnsafeFunction (x : ℝ) : ℝ := (7/5)-3*|x-(1/2)|
def underestimatedFirstSet : Set (Fin 11) :=
  {5} ∪ {i | 0 ≤ (7/5:ℝ)-1/5-sourceCost 2 5 i}

theorem actual_underestimated_lipschitz_update_admits_every_grid_input :
    underestimatedFirstSet=univ := by
  ext i
  fin_cases i <;> norm_num [underestimatedFirstSet,sourceCost,sourceCoordinate]

theorem actual_source_unsafe_boundary_is_a_genuine_lipschitz_three_data_compatible_function :
    (∀ x y, |compatibleUnsafeFunction x-compatibleUnsafeFunction y| ≤ 3*|x-y|) ∧
      compatibleUnsafeFunction (1/2)=7/5 ∧ compatibleUnsafeFunction 0=-(1/10:ℝ) ∧
      |(7/5:ℝ)-compatibleUnsafeFunction (1/2)|≤1/5 ∧
      compatibleUnsafeFunction (1/2) ∈ Icc (6/5:ℝ) (8/5) ∧
      |compatibleUnsafeFunction (1/2)-compatibleUnsafeFunction 0|=3/2 ∧
      compatibleUnsafeFunction 0<0 ∧ (0:Fin 11) ∈ underestimatedFirstSet := by
  refine ⟨?_,by norm_num [compatibleUnsafeFunction],by norm_num [compatibleUnsafeFunction],
    by norm_num [compatibleUnsafeFunction],by norm_num [compatibleUnsafeFunction],
    by norm_num [compatibleUnsafeFunction],by norm_num [compatibleUnsafeFunction],?_⟩
  · intro x y
    simpa [compatibleUnsafeFunction] using downward_cone_is_lipschitz
      (7/5) 0 3 (1/2) (by norm_num) x y
  · rw [actual_underestimated_lipschitz_update_admits_every_grid_input]
    trivial

theorem actual_any_measurement_below_threshold_plus_allowance_certifies_no_new_grid_point
    (measurement allowance threshold L : ℝ) (hL : 0 ≤ L)
    (hm : measurement < threshold+allowance) (anchor : Fin 11) :
    {candidate | threshold ≤ measurement-allowance-sourceCost L anchor candidate}=∅ := by
  ext candidate
  simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
  intro hc
  have hn : 0 ≤ sourceCost L anchor candidate := mul_nonneg hL (abs_nonneg _)
  linarith

end SafeLearning.CompleteModulesLoSBOGridUpdates
