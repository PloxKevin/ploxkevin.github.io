import SafeLearning.CompleteModulesGoSafeToyIslands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyGridGeometry
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility
open SafeLearning.CompleteModulesGoSafeToyIslands

theorem actual_arccos_island_boundary_increases_strictly_with_the_gain :
    StrictMonoOn actualBoundary (Icc (3:ℝ) 8) := by
  intro gain₁ hg₁ gain₂ hg₂ hlt
  have hpos₁ : 0 < 2*gain₁ := by linarith [hg₁.1]
  have hpos₂ : 0 < 2*gain₂ := by linarith [hg₂.1]
  have hrec : 1/(2*gain₂)<1/(2*gain₁) :=
    div_lt_div_of_pos_left (by norm_num) hpos₁ (by linarith)
  have hc₁ := actual_source_cosine_threshold_is_strictly_between_zero_and_one_half gain₁ hg₁
  have hc₂ := actual_source_cosine_threshold_is_strictly_between_zero_and_one_half gain₂ hg₂
  have ht : actualThreshold gain₂<actualThreshold gain₁ := by
    unfold actualThreshold
    linarith
  have hac := Real.arccos_lt_arccos (by linarith : -1 ≤ actualThreshold gain₂) ht
    (by linarith : actualThreshold gain₁ ≤ 1)
  unfold actualBoundary
  exact div_lt_div_of_pos_right hac (by positivity)

theorem actual_two_closed_islands_have_a_strict_gap
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    Disjoint (Icc (actualBoundary gain) (1/2-actualBoundary gain))
      (Icc (1/2+actualBoundary gain) (1-actualBoundary gain)) := by
  have hb := actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth gain hg
  apply Set.disjoint_left.mpr
  intro a h₁ h₂
  simp only [mem_Icc] at h₁ h₂
  linarith [h₁.2,h₂.1,hb.1]

def actualGridParameters : Finset (Fin 25 × Fin 25) := Finset.univ

def actualFirstIslandParameters : Finset (Fin 25 × Fin 25) := by
  classical
  exact actualGridParameters.filter (fun p => p.1.val ≤ 12 ∧
    0 ≤ actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((p.1.val:ℝ)/24))

def actualSecondIslandParameters : Finset (Fin 25 × Fin 25) := by
  classical
  exact actualGridParameters.filter (fun p => 12 < p.1.val ∧
    0 ≤ actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((p.1.val:ℝ)/24))

def actualSafeGridParameters : Finset (Fin 25 × Fin 25) := by
  classical
  exact actualGridParameters.filter (fun p =>
    0 ≤ actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((p.1.val:ℝ)/24))

theorem actual_grid_gain_is_in_the_source_domain (j : Fin 25) :
    actualGain ((j.val:ℝ)/24) ∈ Icc (3:ℝ) 8 := by
  have hj : ((j.val:ℝ)/24) ∈ Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · have h : (j.val:ℝ) ≤ 24 := by exact_mod_cast (by omega : j.val ≤ 24)
      linarith
  exact (actual_source_parameter_ranges 0 ((j.val:ℝ)/24) hj).1

theorem actual_first_island_grid_is_exactly_seven_columns_times_all_twenty_five_gains :
    actualFirstIslandParameters=
      (Finset.univ.filter (fun i : Fin 25 => 3 ≤ i.val ∧ i.val ≤ 9)).product Finset.univ := by
  classical
  apply Finset.ext
  intro p
  simp only [actualFirstIslandParameters,actualGridParameters,Finset.product_eq_sprod,Finset.mem_product,
    Finset.mem_filter,Finset.mem_univ,true_and,and_true]
  rw [actual_safe_grid_columns_are_exactly_three_through_nine_and_fifteen_through_twenty_one _
    (actual_grid_gain_is_in_the_source_domain p.2)]
  omega

theorem actual_second_island_grid_is_exactly_seven_columns_times_all_twenty_five_gains :
    actualSecondIslandParameters=
      (Finset.univ.filter (fun i : Fin 25 => 15 ≤ i.val ∧ i.val ≤ 21)).product Finset.univ := by
  classical
  apply Finset.ext
  intro p
  simp only [actualSecondIslandParameters,actualGridParameters,Finset.product_eq_sprod,Finset.mem_product,
    Finset.mem_filter,Finset.mem_univ,true_and,and_true]
  rw [actual_safe_grid_columns_are_exactly_three_through_nine_and_fifteen_through_twenty_one _
    (actual_grid_gain_is_in_the_source_domain p.2)]
  omega

theorem actual_each_island_contains_one_hundred_seventy_five_grid_parameters :
    actualFirstIslandParameters.card=175 ∧ actualSecondIslandParameters.card=175 := by
  classical
  rw [actual_first_island_grid_is_exactly_seven_columns_times_all_twenty_five_gains,
    actual_second_island_grid_is_exactly_seven_columns_times_all_twenty_five_gains]
  have hfirst : (Finset.univ.filter (fun i : Fin 25 => 3 ≤ i.val ∧ i.val ≤ 9)).card=7 := by decide
  have hsecond : (Finset.univ.filter (fun i : Fin 25 => 15 ≤ i.val ∧ i.val ≤ 21)).card=7 := by decide
  simp [Finset.card_product,hfirst,hsecond]

theorem actual_full_safe_grid_is_the_disjoint_union_of_the_two_islands :
    actualSafeGridParameters=actualFirstIslandParameters ∪ actualSecondIslandParameters ∧
      Disjoint actualFirstIslandParameters actualSecondIslandParameters := by
  classical
  constructor
  · apply Finset.ext
    intro p
    simp only [actualSafeGridParameters,actualFirstIslandParameters,actualSecondIslandParameters,
      actualGridParameters,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    by_cases hindex : p.1.val ≤ 12
    · simp [hindex,not_lt.mpr hindex]
    · simp [hindex,lt_of_not_ge hindex]
  · apply Finset.disjoint_left.mpr
    intro p hfirst hsecond
    simp only [actualFirstIslandParameters,actualSecondIslandParameters,Finset.mem_filter] at hfirst hsecond
    omega

theorem actual_safe_grid_has_three_hundred_fifty_of_the_six_hundred_twenty_five_parameters :
    actualGridParameters.card=625 ∧ actualSafeGridParameters.card=350 := by
  classical
  have h := actual_full_safe_grid_is_the_disjoint_union_of_the_two_islands
  have hc := actual_each_island_contains_one_hundred_seventy_five_grid_parameters
  constructor
  · simp [actualGridParameters]
  · rw [h.1,Finset.card_union_of_disjoint h.2,hc.1,hc.2]

end SafeLearning.CompleteModulesGoSafeToyGridGeometry
