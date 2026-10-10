import SafeLearning.CompleteAppliedFiniteEntropy

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSoftValues
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedFiniteEntropy SafeLearning.CompleteAppliedFiniteKL
open SafeLearning.CompleteAppliedFiniteKLSupport
open SafeLearning.CompleteAppliedInformation
open scoped ENNReal NNReal

def actualActionValues : Fin 2 → ℝ := ![0,Real.log 3]

def actualSoftLaw : PMF (Fin 2) :=
  PMF.ofFintype (fun i => ENNReal.ofReal ((![1/4,3/4] : Fin 2 → ℝ) i)) (by
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (0:ℝ) ≤ 3/4)]
    norm_num)

def actualSoftValue : ℝ := Real.log (∑ i : Fin 2,Real.exp (actualActionValues i))

def actualRegularizedObjective (law : PMF (Fin 2)) : ℝ :=
  (∫ action,actualActionValues action ∂law.toMeasure)+shannonEntropy law

theorem actual_true_softmax_probabilities_and_value :
    (actualSoftLaw 0).toReal=1/4 ∧ (actualSoftLaw 1).toReal=3/4 ∧
      (∀ i : Fin 2,(actualSoftLaw i).toReal=
        Real.exp (actualActionValues i)/(∑ j : Fin 2,Real.exp (actualActionValues j))) ∧
      actualSoftValue=Real.log 4 := by
  have he : ∑ i : Fin 2,Real.exp (actualActionValues i)=4 := by
    norm_num [actualActionValues,Fin.sum_univ_succ,Real.exp_log (by norm_num : (0:ℝ)<3)]
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [actualSoftLaw,PMF.ofFintype_apply,ENNReal.toReal_div]
  · norm_num [actualSoftLaw,PMF.ofFintype_apply,ENNReal.toReal_div]
  · intro i
    rw [he]
    fin_cases i <;> norm_num [actualSoftLaw,PMF.ofFintype_apply,ENNReal.toReal_div,
      actualActionValues,Real.exp_log (by norm_num : (0:ℝ)<3)]
  · rw [actualSoftValue,he]

theorem actual_softmax_has_full_support (action : Fin 2) : actualSoftLaw action ≠ 0 := by
  fin_cases action <;> norm_num [actualSoftLaw,PMF.ofFintype_apply]

theorem actual_softmax_log_mass (action : Fin 2) :
    Real.log (actualSoftLaw action).toReal=actualActionValues action-Real.log 4 := by
  fin_cases action
  all_goals norm_num [actualSoftLaw,PMF.ofFintype_apply,actualActionValues,Real.log_div]

/-- The actual expected reward plus Shannon entropy is optimized using canonical KL. -/
theorem actual_regularized_objective_is_soft_value_minus_true_kl (law : PMF (Fin 2)) :
    (klDiv law.toMeasure actualSoftLaw.toMeasure).toReal=
      actualSoftValue-actualRegularizedObjective law := by
  rw [actual_finite_kl_sum law actualSoftLaw actual_softmax_has_full_support,
    actual_true_softmax_probabilities_and_value.2.2.2,actualRegularizedObjective,
    PMF.integral_eq_sum,actual_entropy_sum]
  have hi (action : Fin 2) : (law action).toReal*
      Real.log ((law action).toReal/(actualSoftLaw action).toReal)=
      (law action).toReal*Real.log (law action).toReal-
        (law action).toReal*actualActionValues action+
          (law action).toReal*Real.log 4 := by
    by_cases hz : (law action).toReal=0
    · simp [hz]
    · have hq : (actualSoftLaw action).toReal ≠ 0 := by
        fin_cases action <;> norm_num [actualSoftLaw,PMF.ofFintype_apply,ENNReal.toReal_div]
      rw [Real.log_div hz hq,actual_softmax_log_mass]
      ring
  simp only [hi,Finset.sum_add_distrib,Finset.sum_sub_distrib,smul_eq_mul,
    neg_mul,Finset.sum_neg_distrib,← Finset.sum_mul,actual_finite_weights_sum,one_mul]
  ring

theorem actual_softmax_uniquely_maximizes_the_true_regularized_objective
    (law : PMF (Fin 2)) :
    actualRegularizedObjective law ≤ actualSoftValue ∧
      (actualRegularizedObjective law=actualSoftValue ↔ law=actualSoftLaw) := by
  have hnonnegative := ENNReal.toReal_nonneg (a:=klDiv law.toMeasure actualSoftLaw.toMeasure)
  rw [actual_regularized_objective_is_soft_value_minus_true_kl] at hnonnegative
  refine ⟨by linarith,?_⟩
  have hfin := actual_finite_kl_is_finite law actualSoftLaw actual_softmax_has_full_support
  have hz : (klDiv law.toMeasure actualSoftLaw.toMeasure).toReal=0 ↔
      klDiv law.toMeasure actualSoftLaw.toMeasure=0 := by
    rw [ENNReal.toReal_eq_zero_iff]
    simp only [hfin,or_false]
  rw [← actual_finite_gibbs_equality law actualSoftLaw,← hz,
    actual_regularized_objective_is_soft_value_minus_true_kl]
  constructor <;> intro h <;> linarith

theorem actual_unregularized_softmax_mean_is_not_its_soft_value :
    (∫ action,actualActionValues action ∂actualSoftLaw.toMeasure)=(3/4)*Real.log 3 ∧
      (∫ action,actualActionValues action ∂actualSoftLaw.toMeasure)<actualSoftValue ∧
      actualSoftValue-max (actualActionValues 0) (actualActionValues 1)=Real.log (4/3) := by
  have hmean : (∫ action,actualActionValues action ∂actualSoftLaw.toMeasure)=(3/4)*Real.log 3 := by
    rw [PMF.integral_eq_sum]
    norm_num [Fin.sum_univ_succ,actualActionValues,actualSoftLaw,PMF.ofFintype_apply,
      ENNReal.toReal_div]
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨hmean,?_,?_⟩
  · rw [hmean,actual_true_softmax_probabilities_and_value.2.2.2]
    linarith
  · rw [actual_true_softmax_probabilities_and_value.2.2.2]
    simp only [actualActionValues,Matrix.cons_val_zero,Matrix.cons_val_one,max_eq_right hl3.le]
    exact (Real.log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)).symm

theorem actual_source_soft_value_and_gap_roundings :
    |actualSoftValue-1.386294| < (0.0000005:ℝ) ∧
      |Real.log 3-1.098612| < 0.0000005 ∧
      |Real.log (4/3)-0.287682| < 0.0000005 ∧
      0 < Real.log (4/3) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h3l := Real.log_three_gt_d9
  have h3u := Real.log_three_lt_d9
  have hv := actual_true_softmax_probabilities_and_value.2.2.2
  have hl4 : Real.log 4=2*Real.log 2 := Real.log_four_eq
  have hgap : Real.log (4/3)=2*Real.log 2-Real.log 3 := by
    rw [Real.log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0),hl4]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hv,hl4]
    apply abs_lt.mpr;constructor <;> linarith
  · apply abs_lt.mpr;constructor <;> linarith
  · rw [hgap]
    apply abs_lt.mpr;constructor <;> linarith
  · exact Real.log_pos (by norm_num)

end SafeLearning.CompleteAppliedSoftValues
