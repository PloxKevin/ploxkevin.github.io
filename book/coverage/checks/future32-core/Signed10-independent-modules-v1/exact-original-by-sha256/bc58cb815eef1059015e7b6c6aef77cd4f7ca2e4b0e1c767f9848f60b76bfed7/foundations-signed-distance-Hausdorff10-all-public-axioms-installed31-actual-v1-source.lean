import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsSignedDistanceHausdorff32
variable {E : Type*} [MetricSpace E]

def signedDistance (C : Set E) (x : E) : ℝ :=
  Metric.infDist x C-Metric.infDist x Cᶜ

def safeSidePositiveDistance (C : Set E) (x : E) : ℝ := -signedDistance C x

theorem actual_signed_distance_has_the_printed_two_sides (C : Set E) (x : E) :
    (x∉C → signedDistance C x=Metric.infDist x C) ∧
    (x∈C → signedDistance C x= -Metric.infDist x Cᶜ) := by
  constructor
  · intro hx
    rw [signedDistance,Metric.infDist_zero_of_mem (show x∈Cᶜ from hx),sub_zero]
  · intro hx
    rw [signedDistance,Metric.infDist_zero_of_mem hx,zero_sub]

theorem actual_signed_distance_zero_iff_boundary_for_nonempty_proper_closed_sets
    (C : Set E) (hC : IsClosed C) (hne : C.Nonempty) (hproper : Cᶜ.Nonempty)
    (x : E) : signedDistance C x=0 ↔ x∈frontier C := by
  rw [frontier_eq_closure_inter_closure,hC.closure_eq]
  by_cases hx : x∈C
  · rw [(actual_signed_distance_has_the_printed_two_sides C x).2 hx]
    simp only [mem_inter_iff,hx,true_and,neg_eq_zero]
    exact (Metric.mem_closure_iff_infDist_zero hproper).symm
  · have hp : 0 < Metric.infDist x C := (hC.notMem_iff_infDist_pos hne).mp hx
    rw [(actual_signed_distance_has_the_printed_two_sides C x).1 hx]
    simp only [mem_inter_iff,hx,false_and,iff_false]
    exact ne_of_gt hp

theorem actual_safe_side_positive_convention_has_the_opposite_sign
    (C : Set E) (hC : IsClosed C) (hne : C.Nonempty) (hproper : Cᶜ.Nonempty)
    (x : E) :
    (0 < signedDistance C x ↔ x∉C) ∧
    (0 < safeSidePositiveDistance C x ↔ x∈interior C) := by
  constructor
  · by_cases hx : x∈C
    · rw [(actual_signed_distance_has_the_printed_two_sides C x).2 hx]
      simp only [hx,not_true,iff_false,not_lt]
      exact neg_nonpos.mpr Metric.infDist_nonneg
    · rw [(actual_signed_distance_has_the_printed_two_sides C x).1 hx]
      exact (hC.notMem_iff_infDist_pos hne).symm
  · by_cases hx : x∈C
    · have he : safeSidePositiveDistance C x=Metric.infDist x Cᶜ := by
        rw [safeSidePositiveDistance,(actual_signed_distance_has_the_printed_two_sides C x).2 hx,neg_neg]
      rw [he,← Metric.infDist_pos_iff_notMem_closure hproper,closure_compl]
      simp only [mem_compl_iff,not_not]
    · have hp : 0 < Metric.infDist x C := (hC.notMem_iff_infDist_pos hne).mp hx
      have hi : x∉interior C := fun h => hx (interior_subset h)
      rw [safeSidePositiveDistance,(actual_signed_distance_has_the_printed_two_sides C x).1 hx]
      simp only [hi,iff_false,not_lt]
      exact neg_nonpos.mpr (le_of_lt hp)

theorem actual_strict_and_nonstrict_sign_sets_differ_exactly_on_boundary
    (C : Set E) (hC : IsClosed C) (hne : C.Nonempty) (hproper : Cᶜ.Nonempty) :
    ({x | 0 ≤ signedDistance C x}\{x | 0 < signedDistance C x})=frontier C ∧
    ({x | 0 ≤ safeSidePositiveDistance C x}\{x | 0 < safeSidePositiveDistance C x})=frontier C := by
  have hz:=actual_signed_distance_zero_iff_boundary_for_nonempty_proper_closed_sets C hC hne hproper
  constructor
  · ext x
    change (0 ≤ signedDistance C x ∧ ¬ 0 < signedDistance C x) ↔ x∈frontier C
    rw [← hz]
    constructor
    · intro h; linarith
    · intro h; simp [h]
  · ext x
    change (0 ≤ -signedDistance C x ∧ ¬ 0 < -signedDistance C x) ↔ x∈frontier C
    rw [← hz]
    constructor
    · intro h; linarith
    · intro h; simp [h]

theorem actual_signed_distance_is_continuous (C : Set E) : Continuous (signedDistance C) := by
  exact (Metric.continuous_infDist_pt C).sub (Metric.continuous_infDist_pt Cᶜ)

theorem actual_nonempty_compact_Hausdorff_distance_is_the_printed_maximum_of_two_suprema
    (A B : Set E) (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    Metric.hausdorffDist A B = max
      (sSup ((fun a => Metric.infDist a B) '' A))
      (sSup ((fun b => Metric.infDist b A) '' B)) := by
  have hf:=Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hAn hBn hA.isBounded hB.isBounded
  have hfr : Metric.hausdorffEDist B A ≠ ⊤ := by rwa [Metric.hausdorffEDist_comm]
  have hbA : BddAbove ((fun a => Metric.infDist a B) '' A) := by
    refine ⟨Metric.hausdorffDist A B,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Metric.infDist_le_hausdorffDist_of_mem hx hf
  have hbB : BddAbove ((fun b => Metric.infDist b A) '' B) := by
    refine ⟨Metric.hausdorffDist A B,?_⟩
    rintro y ⟨x,hx,rfl⟩
    simpa only [Metric.hausdorffDist_comm] using Metric.infDist_le_hausdorffDist_of_mem hx hfr
  apply le_antisymm
  · apply Metric.hausdorffDist_le_of_infDist
    · obtain ⟨x,hx⟩:=hAn
      exact (Metric.infDist_nonneg.trans (le_csSup hbA ⟨x,hx,rfl⟩)).trans (le_max_left _ _)
    · intro x hx
      exact (le_csSup hbA ⟨x,hx,rfl⟩).trans (le_max_left _ _)
    · intro x hx
      exact (le_csSup hbB ⟨x,hx,rfl⟩).trans (le_max_right _ _)
  · apply max_le
    · apply csSup_le (hAn.image _)
      rintro y ⟨x,hx,rfl⟩
      exact Metric.infDist_le_hausdorffDist_of_mem hx hf
    · apply csSup_le (hBn.image _)
      rintro y ⟨x,hx,rfl⟩
      simpa only [Metric.hausdorffDist_comm] using Metric.infDist_le_hausdorffDist_of_mem hx hfr

theorem actual_Hausdorff_distance_on_nonempty_compact_sets_has_metric_properties
    (A B C : Set E) (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hCn : C.Nonempty) :
    (Metric.hausdorffDist A B=0 ↔ A=B) ∧
    Metric.hausdorffDist A B=Metric.hausdorffDist B A ∧
    Metric.hausdorffDist A C ≤ Metric.hausdorffDist A B+Metric.hausdorffDist B C := by
  have hf:=Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hAn hBn hA.isBounded hB.isBounded
  exact ⟨hA.isClosed.hausdorffDist_zero_iff_eq hB.isClosed hf,
    Metric.hausdorffDist_comm,Metric.hausdorffDist_triangle hf⟩

theorem actual_interval_distance_two_to_zero_one_is_one :
    Metric.infDist (2:ℝ) (Icc 0 1)=1 := by
  apply le_antisymm
  · have h:=Metric.infDist_le_dist_of_mem (show (1:ℝ)∈Icc 0 1 by norm_num) (x:=(2:ℝ))
    norm_num [Real.dist_eq] at h ⊢
    exact h
  · apply (Metric.le_infDist (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)).mpr
    intro y hy
    rw [Real.dist_eq,abs_of_nonneg (by linarith [hy.2] : 0 ≤ (2:ℝ)-y)]
    linarith [hy.2]

theorem actual_printed_interval_Hausdorff_distance_is_one :
    Metric.hausdorffDist (Icc (0:ℝ) 1) (Icc 0 2)=1 := by
  apply le_antisymm
  · apply Metric.hausdorffDist_le_of_mem_dist (by norm_num : (0:ℝ) ≤ 1)
    · intro x hx
      exact ⟨x,⟨hx.1,by linarith [hx.2]⟩,by simp⟩
    · intro x hx
      by_cases h : x ≤ 1
      · exact ⟨x,⟨hx.1,h⟩,by simp⟩
      · refine ⟨1,by norm_num,?_⟩
        rw [Real.dist_eq,abs_of_nonneg (by linarith : 0 ≤ x-1)]
        linarith [hx.2]
  · have hf:=Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (show (Icc (0:ℝ) 2).Nonempty from ⟨0,by norm_num⟩)
      (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
      isCompact_Icc.isBounded isCompact_Icc.isBounded
    have h:=Metric.infDist_le_hausdorffDist_of_mem (show (2:ℝ)∈Icc 0 2 by norm_num) hf
    rwa [actual_interval_distance_two_to_zero_one_is_one,Metric.hausdorffDist_comm] at h

theorem actual_real_distance_totalization_on_full_space_requires_the_proper_set_domain
    (x : ℝ) : signedDistance (univ : Set ℝ) x=0 ∧ x∉frontier (univ : Set ℝ) := by
  simp [signedDistance,Metric.infDist_zero_of_mem (mem_univ x)]

end SafeLearning.CompleteFoundationsSignedDistanceHausdorff32

#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_signed_distance_has_the_printed_two_sides
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_signed_distance_zero_iff_boundary_for_nonempty_proper_closed_sets
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_safe_side_positive_convention_has_the_opposite_sign
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_strict_and_nonstrict_sign_sets_differ_exactly_on_boundary
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_signed_distance_is_continuous
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_nonempty_compact_Hausdorff_distance_is_the_printed_maximum_of_two_suprema
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_Hausdorff_distance_on_nonempty_compact_sets_has_metric_properties
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_interval_distance_two_to_zero_one_is_one
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_printed_interval_Hausdorff_distance_is_one
#print axioms SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.actual_real_distance_totalization_on_full_space_requires_the_proper_set_domain
