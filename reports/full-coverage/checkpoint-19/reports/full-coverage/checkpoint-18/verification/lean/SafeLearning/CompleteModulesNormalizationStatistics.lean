import SafeLearning.CompleteModulesGeneralNormalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesNormalizationStatistics
open CompleteModulesLipSDP

def actualRowNormalizedLastLayer {I O : Type*} [Fintype I] (weight : Matrix O I ℝ) : Matrix O I ℝ :=
  fun row column => weight row column/‖WithLp.toLp 2 (weight row)‖

def actualHalfLastLayer : Matrix (Fin 1) (Fin 1) ℝ := (1/2:ℝ) • 1

theorem actual_half_last_layer_row_has_norm_one_half :
    ‖WithLp.toLp 2 (actualHalfLastLayer 0)‖=(1/2:ℝ) := by
  have h := squared_norm_of_coordinates (actualHalfLastLayer 0)
  norm_num [actualHalfLastLayer,Matrix.one_apply,Fin.sum_univ_one] at h
  change ‖WithLp.toLp 2 (actualHalfLastLayer 0)‖^2=(1/4:ℝ) at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (actualHalfLastLayer 0))]

theorem actual_half_last_layer_row_normalizes_to_identity :
    actualRowNormalizedLastLayer actualHalfLastLayer=1 := by
  ext row column
  fin_cases row
  fin_cases column
  change actualHalfLastLayer 0 0/‖WithLp.toLp 2 (actualHalfLastLayer 0)‖=(1:ℝ)
  rw [actual_half_last_layer_row_has_norm_one_half]
  norm_num [actualHalfLastLayer,Matrix.one_apply]

def actualEuclideanFinalLayer {I O : Type*} [Fintype I] [Fintype O]
    (weight : Matrix O I ℝ) (input : EuclideanSpace ℝ I) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 (weight *ᵥ WithLp.ofLp input)

theorem actual_row_normalization_increases_the_half_layer_distance_gain
    (first second : EuclideanSpace ℝ (Fin 1)) :
    dist (actualEuclideanFinalLayer actualHalfLastLayer first)
      (actualEuclideanFinalLayer actualHalfLastLayer second)=(1/2:ℝ)*dist first second ∧
    dist (actualEuclideanFinalLayer (actualRowNormalizedLastLayer actualHalfLastLayer) first)
      (actualEuclideanFinalLayer (actualRowNormalizedLastLayer actualHalfLastLayer) second)=dist first second := by
  constructor
  · simp [actualEuclideanFinalLayer,actualHalfLastLayer,dist_eq_norm,← WithLp.toLp_sub,
      Matrix.smul_mulVec,WithLp.toLp_smul,← smul_sub,norm_smul,Real.norm_eq_abs]
  · rw [actual_half_last_layer_row_normalizes_to_identity]
    simp [actualEuclideanFinalLayer]

theorem actual_row_normalized_half_layer_exceeds_the_original_bound :
    ¬∀ first second : EuclideanSpace ℝ (Fin 1),
      dist (actualEuclideanFinalLayer (actualRowNormalizedLastLayer actualHalfLastLayer) first)
        (actualEuclideanFinalLayer (actualRowNormalizedLastLayer actualHalfLastLayer) second) ≤
          (1/2:ℝ)*dist first second := by
  intro h
  let first : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => (1:ℝ))
  have hb := h first 0
  rw [(actual_row_normalization_increases_the_half_layer_distance_gain first 0).2] at hb
  have hn : ‖first‖=1 := by
    have hs : ‖first‖^2=1 := by
      simpa only [first,Fin.sum_univ_one,one_pow] using
        squared_norm_of_coordinates (fun _ : Fin 1 => (1:ℝ))
    nlinarith [norm_nonneg first]
  norm_num [dist_zero_right,hn] at hb

def actualCleanTestIndices {D C : Type*} [Fintype D] [DecidableEq C]
    (prediction truth : D → C) : Finset D :=
  Finset.univ.filter (fun datum => prediction datum=truth datum)

def actualCertifiedTestIndices {D C : Type*} [Fintype D] [DecidableEq C]
    (prediction truth : D → C) (certificate : D → Prop) [DecidablePred certificate] : Finset D :=
  Finset.univ.filter (fun datum => prediction datum=truth datum ∧ certificate datum)

def actualCleanAccuracy {D C : Type*} [Fintype D] [DecidableEq C]
    (prediction truth : D → C) : ℝ :=
  ((actualCleanTestIndices prediction truth).card : ℝ)/(Fintype.card D : ℝ)

def actualCertifiedAccuracy {D C : Type*} [Fintype D] [DecidableEq C]
    (prediction truth : D → C) (certificate : D → Prop) [DecidablePred certificate] : ℝ :=
  ((actualCertifiedTestIndices prediction truth certificate).card : ℝ)/(Fintype.card D : ℝ)

theorem actual_certified_test_indices_are_clean_test_indices
    {D C : Type*} [Fintype D] [DecidableEq C] (prediction truth : D → C)
    (certificate : D → Prop) [DecidablePred certificate] :
    actualCertifiedTestIndices prediction truth certificate ⊆ actualCleanTestIndices prediction truth := by
  intro datum hdatum
  simp only [actualCertifiedTestIndices,actualCleanTestIndices,Finset.mem_filter,Finset.mem_univ,true_and] at *
  exact hdatum.1

theorem actual_certified_accuracy_is_no_greater_than_clean_accuracy
    {D C : Type*} [Fintype D] [DecidableEq C] (prediction truth : D → C)
    (certificate : D → Prop) [DecidablePred certificate] :
    actualCertifiedAccuracy prediction truth certificate ≤ actualCleanAccuracy prediction truth := by
  unfold actualCertifiedAccuracy actualCleanAccuracy
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (actual_certified_test_indices_are_clean_test_indices prediction truth certificate)

end SafeLearning.CompleteModulesNormalizationStatistics
