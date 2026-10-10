import SafeLearning.CompleteModulesTanhChords
import SafeLearning.CompleteModulesDiagonalQC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesTanhRefinement
open CompleteModulesTanhChords CompleteModulesTheory
open CompleteModulesLipSDP CompleteModulesDiagonalQC

def actualSectorQCMatrix (lower upper : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2*lower*upper,lower+upper;lower+upper,-2]

theorem actual_sector_qc_matrix_has_the_literal_quadratic (lower upper input output : ℝ) :
    quadratic (actualSectorQCMatrix lower upper) ![input,output] =
      scalarQC lower upper input output := by
  simp [quadratic,actualSectorQCMatrix,scalarQC,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_positive_lower_slope_has_a_strictly_negative_top_left_entry
    (lower upper : ℝ) (hl : 0 < lower) (hu : 0 < upper) :
    actualSectorQCMatrix lower upper 0 0 < 0 := by
  change -2*lower*upper < 0
  nlinarith [mul_pos hl hu]

def actualAllowedQCPairs (lower : ℝ) : Set (ℝ × ℝ) :=
  {pair | 0 ≤ scalarQC lower 1 pair.1 pair.2}

theorem actual_positive_lower_slope_strictly_shrinks_the_source_qc_abstraction
    (lower : ℝ) (hl : 0 < lower) (hu : lower ≤ 1) :
    actualAllowedQCPairs lower ⊆ actualAllowedQCPairs 0 ∧
      (1,0) ∈ actualAllowedQCPairs 0 ∧ (1,0) ∉ actualAllowedQCPairs lower := by
  refine ⟨?_,by norm_num [actualAllowedQCPairs,scalarQC],?_⟩
  · intro pair hp
    obtain ⟨slope,hs,hu,he⟩ :=
      (scalar_qc_iff_admissible_chord lower 1 pair.1 pair.2 hu).mp hp
    apply (scalar_qc_iff_admissible_chord 0 1 pair.1 pair.2 (by norm_num)).mpr
    exact ⟨slope,hl.le.trans hs,hu,he⟩
  · simp only [actualAllowedQCPairs,Set.mem_ofPred_eq,scalarQC]
    nlinarith

theorem actual_local_tanh_increments_satisfy_the_literal_refined_qc
    (radius first second : ℝ) (hf : |first| ≤ radius) (hs : |second| ≤ radius) :
    0 ≤ quadratic (actualSectorQCMatrix (1-(Real.tanh radius)^2) 1)
      ![first-second,Real.tanh first-Real.tanh second] := by
  rw [actual_sector_qc_matrix_has_the_literal_quadratic]
  have hupper : 1-(Real.tanh radius)^2 ≤ 1 := by nlinarith [sq_nonneg (Real.tanh radius)]
  apply (scalar_qc_iff_admissible_chord _ 1 _ _ hupper).mpr
  by_cases he : first = second
  · subst second
    exact ⟨1-(Real.tanh radius)^2,le_rfl,hupper,by simp⟩
  · obtain ⟨hp,hl,hu⟩ :=
      actual_local_tanh_chord_has_the_literal_positive_lower_and_upper_bound radius first second hf hs he
    exact ⟨(Real.tanh first-Real.tanh second)/(first-second),hl,hu,
      (div_mul_cancel₀ _ (sub_ne_zero.mpr he)).symm⟩

theorem actual_local_origin_tanh_graph_satisfies_the_tighter_secant_qc
    (radius point : ℝ) (hr : 0 < radius) (hp : |point| ≤ radius) :
    0 ≤ quadratic (actualSectorQCMatrix (Real.tanh radius/radius) 1) ![point,Real.tanh point] := by
  rw [actual_sector_qc_matrix_has_the_literal_quadratic,scalar_qc_factorization]
  nlinarith [tanh_local_origin_sector radius point hr hp]

def actualOffsetTanh (center deviation : ℝ) : ℝ := Real.tanh (center+deviation)-Real.tanh center

theorem actual_offset_tanh_uses_a_true_local_incremental_qc
    (radius center deviation : ℝ) (hc : |center| ≤ radius)
    (hd : |center+deviation| ≤ radius) :
    0 ≤ quadratic (actualSectorQCMatrix (1-(Real.tanh radius)^2) 1)
      ![deviation,actualOffsetTanh center deviation] := by
  simpa only [add_sub_cancel_left,actualOffsetTanh] using
    actual_local_tanh_increments_satisfy_the_literal_refined_qc radius (center+deviation) center hd hc

theorem actual_smaller_interval_makes_the_source_containment_condition_stricter
    (small large : ℝ) (hs : 0 ≤ small) (hl : small < large) :
    {point : ℝ | |point| ≤ small} ⊆ {point : ℝ | |point| ≤ large} ∧
      large ∈ {point : ℝ | |point| ≤ large} ∧ large ∉ {point : ℝ | |point| ≤ small} := by
  have hlarge : 0 ≤ large := hs.trans hl.le
  refine ⟨fun _ hp => hp.trans hl.le,?_,?_⟩
  · simpa only [Set.mem_ofPred_eq,abs_of_nonneg hlarge] using le_refl large
  · simp only [Set.mem_ofPred_eq,abs_of_nonneg hlarge]
    exact not_le_of_gt hl

end SafeLearning.CompleteModulesTanhRefinement
