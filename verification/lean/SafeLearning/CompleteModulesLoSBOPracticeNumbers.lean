import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLoSBOPracticeNumbers

def actualCone (center observation allowance slope threshold : ℝ) : Set ℝ :=
  {x | threshold ≤ observation-allowance-slope*|x-center|}

theorem actual_positive_slope_cone_is_the_closed_interval
    (center observation allowance slope threshold : ℝ) (hs : 0 < slope) :
    actualCone center observation allowance slope threshold =
      Icc (center-(observation-allowance-threshold)/slope)
        (center+(observation-allowance-threshold)/slope) := by
  ext x
  change threshold ≤ observation-allowance-slope*|x-center| ↔ _
  have hd := (le_div_iff₀ hs : |x-center| ≤ (observation-allowance-threshold)/slope ↔
    |x-center| * slope ≤ observation-allowance-threshold)
  rw [Set.mem_Icc]
  constructor
  · intro h
    have ha : |x-center| ≤ (observation-allowance-threshold)/slope := hd.mpr (by nlinarith)
    have hab := abs_le.mp ha
    constructor <;> linarith [hab.1,hab.2]
  · intro h
    have ha : |x-center| ≤ (observation-allowance-threshold)/slope := abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
    have hp := hd.mp ha
    nlinarith

theorem actual_source_first_cone_interval_radius_and_two_boundary_tests :
    ((7/10:ℝ)-1/10-1/5)/2=1/5 ∧
      actualCone (2/5) (7/10) (1/10) 2 (1/5) ∩ Icc 0 1=Icc (1/5) (3/5) ∧
      (7/10:ℝ)-1/10-2*|3/5-2/5|=1/5 ∧
      (7/10:ℝ)-1/10-2*|13/20-2/5|=1/10 ∧
      (3/5:ℝ) ∈ actualCone (2/5) (7/10) (1/10) 2 (1/5) ∧
      (13/20:ℝ) ∉ actualCone (2/5) (7/10) (1/10) 2 (1/5) := by
  refine ⟨by norm_num,?_,by norm_num,by norm_num,by norm_num [actualCone],by norm_num [actualCone]⟩
  rw [actual_positive_slope_cone_is_the_closed_interval _ _ _ _ _ (by norm_num)]
  ext x
  norm_num [Set.mem_Icc]
  intro hlo hhi
  constructor <;> linarith

def actualAcquisition (i : Fin 3) : ℝ := ![4/5,11/10,3] i
def actualCertified : Set (Fin 3) := {0,1}

theorem actual_source_best_certified_acquisition_is_uniquely_b_and_c_is_ineligible :
    IsGreatest (actualAcquisition '' actualCertified) (11/10:ℝ) ∧
      (∀ i ∈ actualCertified, actualAcquisition i=11/10 ↔ i=1) ∧
      (2:Fin 3) ∉ actualCertified ∧ actualAcquisition 1 < actualAcquisition 2 := by
  refine ⟨?_,?_,by norm_num [actualCertified],by norm_num [actualAcquisition]⟩
  · constructor
    · exact ⟨1,by simp [actualCertified],by norm_num [actualAcquisition]⟩
    · rintro value ⟨i,hi,rfl⟩
      fin_cases i
      all_goals norm_num [actualCertified] at hi
      all_goals norm_num [actualAcquisition]
  · intro i hi
    fin_cases i
    all_goals norm_num [actualCertified] at hi
    all_goals norm_num [actualAcquisition]

theorem actual_source_conservative_lipschitz_radii_and_order :
    ((3/10:ℝ)/1)=3/10 ∧ ((3/10:ℝ)/3)=1/10 ∧ ((3/10:ℝ)/2)=3/20 ∧
      (1/10:ℝ)<3/20 ∧ (3/20:ℝ)<3/10 := by norm_num

theorem actual_valid_larger_slope_produces_a_subset_of_the_original_cone
    (center observation allowance first second threshold : ℝ) (h : first ≤ second) :
    actualCone center observation allowance second threshold ⊆
      actualCone center observation allowance first threshold := by
  intro x hx
  have hm := mul_le_mul_of_nonneg_right h (abs_nonneg (x-center))
  change threshold ≤ observation-allowance-second*|x-center| at hx
  change threshold ≤ observation-allowance-first*|x-center|
  linarith

theorem actual_source_two_constraint_intersection_and_individual_tests :
    Icc (1/10:ℝ) (1/2) ∩ Icc (3/10) (4/5)=Icc (3/10) (1/2) ∧
      (2/5:ℝ) ∈ Icc (1/10) (1/2) ∩ Icc (3/10) (4/5) ∧
      ((1/5:ℝ) ∈ Icc (1/10) (1/2) ∧ (1/5:ℝ) ∉ Icc (3/10) (4/5)) ∧
      ((7/10:ℝ) ∉ Icc (1/10) (1/2) ∧ (7/10:ℝ) ∈ Icc (3/10) (4/5)) := by
  refine ⟨?_,by norm_num,by norm_num,by norm_num⟩
  ext x
  simp only [mem_inter_iff,mem_Icc]
  constructor
  · exact fun h => ⟨h.2.1,h.1.2⟩
  · intro h
    constructor <;> constructor <;> linarith [h.1,h.2]

theorem actual_source_observation_cones_and_their_clipped_union :
    actualCone (1/5) (7/20) (1/20) 1 (1/10)=Icc 0 (2/5) ∧
      actualCone (3/5) (9/20) (1/20) 1 (1/10)=Icc (3/10) (9/10) ∧
      (Icc (0:ℝ) (2/5) ∪ Icc (3/10) (9/10)) ∩ Icc 0 1=Icc 0 (9/10) := by
  constructor
  · rw [actual_positive_slope_cone_is_the_closed_interval _ _ _ _ _ (by norm_num)]
    norm_num
  constructor
  · rw [actual_positive_slope_cone_is_the_closed_interval _ _ _ _ _ (by norm_num)]
    norm_num
  · ext x
    simp only [mem_inter_iff,mem_union,mem_Icc]
    constructor
    · intro h
      rcases h.1 with h | h <;> constructor <;> linarith [h.1,h.2]
    · intro h
      refine ⟨?_,⟨h.1,by linarith [h.2]⟩⟩
      by_cases hx : x ≤ 2/5
      · exact Or.inl ⟨h.1,hx⟩
      · exact Or.inr ⟨by linarith,h.2⟩

theorem actual_negative_slack_cone_is_empty
    (center observation allowance slope threshold : ℝ)
    (hs : 0 ≤ slope) (hslack : observation-allowance-threshold < 0) :
    actualCone center observation allowance slope threshold=∅ := by
  ext x
  simp only [Set.mem_empty_iff_false,iff_false]
  intro hx
  have hp := mul_nonneg hs (abs_nonneg (x-center))
  change threshold ≤ observation-allowance-slope*|x-center| at hx
  linarith

theorem actual_constraint_intersection_of_witness_unions_has_forall_exists_order
    {C J X : Type*} (certificates : C → J → Set X) (x : X) :
    x ∈ ⋂ i, ⋃ j, certificates i j ↔ ∀ i, ∃ j, x ∈ certificates i j := by simp

def actualConstraintBound (i j : Fin 2) : ℝ := !![1/5,-1/10;-3/10,1/10] i j

theorem actual_source_distinct_constraint_witnesses_and_both_min_max_values :
    min (max (1/5:ℝ) (-1/10)) (max (-3/10) (1/10))=1/10 ∧
      max (min (1/5:ℝ) (-3/10)) (min (-1/10) (1/10))=(-1/10) ∧
      (∀ i : Fin 2, ∃ j : Fin 2, 0 ≤ actualConstraintBound i j) ∧
      ¬(∃ j : Fin 2, ∀ i : Fin 2, 0 ≤ actualConstraintBound i j) := by
  refine ⟨by norm_num,by norm_num,?_,?_⟩
  · intro i
    fin_cases i
    · exact ⟨0,by norm_num [actualConstraintBound]⟩
    · exact ⟨1,by norm_num [actualConstraintBound]⟩
  · rintro ⟨j,hj⟩
    fin_cases j
    · have h := hj 1
      norm_num [actualConstraintBound] at h
    · have h := hj 0
      norm_num [actualConstraintBound] at h

theorem actual_each_constraint_with_its_own_valid_witness_is_safe
    {C J : Type*} (bounds : C → J → ℝ) (values : C → ℝ)
    (hvalid : ∀ i j, bounds i j ≤ values i) (hwitness : ∀ i, ∃ j, 0 ≤ bounds i j) :
    ∀ i, 0 ≤ values i := by
  intro i
  obtain ⟨j,hj⟩ := hwitness i
  exact hj.trans (hvalid i j)

end SafeLearning.CompleteModulesLoSBOPracticeNumbers
