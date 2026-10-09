import SafeLearning.CompleteAppliedBandit

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SafeLearning.CompletePolicyImportance
open CompleteAppliedProbability CompleteAppliedBandit

def binaryLaw (q : unitInterval) : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![1 - (q : ℝ), (q : ℝ)] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_zero, add_zero]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr q.2.2) q.2.1]
    simp)

def dataParameter : unitInterval := ⟨1 / 100, by norm_num⟩
def candidateParameter : unitInterval := ⟨1 / 2, by norm_num⟩
def likelihoodRatio {n : ℕ} (data candidate : PMF (Fin n)) (i : Fin n) : ℝ :=
  (candidate i).toReal / (data i).toReal

theorem actual_binary_expectation (q : unitInterval) (f : Fin 2 → ℝ) :
    finiteExpectation (binaryLaw q) f = (1 - (q : ℝ)) * f 0 + (q : ℝ) * f 1 := by
  unfold finiteExpectation
  simp only [binaryLaw, PMF.ofFintype_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.sum_univ_zero, add_zero]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2), ENNReal.toReal_ofReal q.2.1]

theorem actual_ratios_and_normalization :
    likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter) 0 = 50 / 99 ∧
      likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter) 1 = 50 ∧
      (∫ i, likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter) i
        ∂(binaryLaw dataParameter).toMeasure) = 1 := by
  have h0 : likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter) 0 =
      50 / 99 := by norm_num [likelihoodRatio, binaryLaw, dataParameter, candidateParameter]
  have h1 : likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter) 1 =
      50 := by norm_num [likelihoodRatio, binaryLaw, dataParameter, candidateParameter]
  refine ⟨h0, h1, ?_⟩
  rw [← finite_expectation_is_actual_integral, actual_binary_expectation, h0, h1]
  norm_num [dataParameter]

theorem actual_finite_importance_identity {n : ℕ} (data candidate : PMF (Fin n))
    (hsupport : ∀ i, data i = 0 → candidate i = 0) (f : Fin n → ℝ) :
    (∫ i, likelihoodRatio data candidate i * f i ∂data.toMeasure) =
      ∫ i, f i ∂candidate.toMeasure := by
  simp only [← finite_expectation_is_actual_integral, finiteExpectation]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : (data i).toReal = 0
  · have hpzero : data i = 0 :=
      (ENNReal.toReal_eq_zero_iff (data i)).mp hp |>.resolve_right (data.apply_ne_top i)
    simp [likelihoodRatio, hp, hsupport i hpzero]
  · unfold likelihoodRatio
    field_simp

theorem actual_ratio_variance :
    finiteVariance (binaryLaw dataParameter)
      (likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter)) = 2401 / 99 := by
  have h := actual_ratios_and_normalization
  have hm : finiteExpectation (binaryLaw dataParameter)
      (likelihoodRatio (binaryLaw dataParameter) (binaryLaw candidateParameter)) = 1 := by
    rw [finite_expectation_is_actual_integral]
    exact h.2.2
  rw [finiteVariance, hm, actual_binary_expectation, h.1, h.2.1]
  norm_num [dataParameter]

theorem missing_support_actual_counterexample :
    (PMF.pure (0 : Fin 2)) 1 = 0 ∧ (binaryLaw candidateParameter) 1 ≠ 0 ∧
      (∫ i, likelihoodRatio (PMF.pure (0 : Fin 2)) (binaryLaw candidateParameter) i *
        (if i = 1 then (1 : ℝ) else 0) ∂(PMF.pure (0 : Fin 2)).toMeasure) = 0 ∧
      (∫ i, (if i = 1 then (1 : ℝ) else 0) ∂(binaryLaw candidateParameter).toMeasure) = 1 / 2 := by
  refine ⟨by simp, by norm_num [binaryLaw, candidateParameter], ?_, ?_⟩
  · simp only [← finite_expectation_is_actual_integral, finiteExpectation, Fin.sum_univ_two]
    simp [likelihoodRatio]
  · rw [← finite_expectation_is_actual_integral, actual_binary_expectation]
    norm_num [candidateParameter]

theorem unsupported_action_has_zero_data_probability :
    (PMF.pure (0 : Fin 2)).toMeasure {1} = 0 := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

theorem impossible_finite_ratio_on_unsupported_action :
    ¬ ∃ w : ℝ, ((PMF.pure (0 : Fin 2)) 1).toReal * w =
      ((binaryLaw candidateParameter) 1).toReal := by
  norm_num [binaryLaw, candidateParameter]

end SafeLearning.CompletePolicyImportance
