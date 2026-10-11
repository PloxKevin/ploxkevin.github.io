import SafeLearning.CompleteAppliedFinitePinsker
import SafeLearning.CompleteAppliedValidationNumbers
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedInformationExamples
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteKL
open SafeLearning.CompleteAppliedFiniteVariation SafeLearning.CompleteAppliedFinitePinsker
open SafeLearning.CompleteAppliedValidationNumbers
open scoped ENNReal NNReal Classical

def pLaw : PMF (Fin 3) := PMF.ofFintype
  ![ENNReal.ofReal (3/5:ℝ),ENNReal.ofReal (3/10:ℝ),ENNReal.ofReal (1/10:ℝ)]
  (by norm_num [Fin.sum_univ_three]; rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num)
def qLaw : PMF (Fin 3) := PMF.ofFintype
  ![ENNReal.ofReal (2/5:ℝ),ENNReal.ofReal (2/5:ℝ),ENNReal.ofReal (1/5:ℝ)]
  (by norm_num [Fin.sum_univ_three]; rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num)
def excludedLaw : PMF (Fin 3) := PMF.ofFintype
  ![ENNReal.ofReal (1/2:ℝ),ENNReal.ofReal (1/2:ℝ),0]
  (by norm_num [Fin.sum_univ_three]; rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)];
      norm_num)

theorem actual_source_positive_support :
    (∀ i,pLaw i≠0) ∧ (∀ i,qLaw i≠0) := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [pLaw,qLaw]

theorem actual_source_directional_log_ratios :
    (klDiv pLaw.toMeasure qLaw.toMeasure).toReal=
      (3/5)*Real.log (3/2)+(3/10)*Real.log (3/4)+(1/10)*Real.log (1/2) ∧
    (klDiv qLaw.toMeasure pLaw.toMeasure).toReal=
      (2/5)*Real.log (2/3)+(2/5)*Real.log (4/3)+(1/5)*Real.log 2 := by
  constructor
  · rw [actual_finite_kl_sum _ _ actual_source_positive_support.2]
    norm_num [pLaw,qLaw,Fin.sum_univ_three]
  · rw [actual_finite_kl_sum _ _ actual_source_positive_support.1]
    norm_num [pLaw,qLaw,Fin.sum_univ_three]

theorem actual_source_directional_log_forms :
    (klDiv pLaw.toMeasure qLaw.toMeasure).toReal=(9/10)*Real.log 3-(13/10)*Real.log 2 ∧
    (klDiv qLaw.toMeasure pLaw.toMeasure).toReal=(7/5)*Real.log 2-(4/5)*Real.log 3 := by
  rw [actual_source_directional_log_ratios.1,actual_source_directional_log_ratios.2]
  norm_num [Real.log_div,Real.log_four_eq]
  constructor <;> ring

theorem actual_source_total_variation : totalVariation pLaw qLaw=1/5 := by
  rw [actual_finite_total_variation]
  norm_num [pLaw,qLaw,Fin.sum_univ_three]

theorem actual_source_pinsker_both_directions :
    totalVariation pLaw qLaw≤Real.sqrt ((klDiv pLaw.toMeasure qLaw.toMeasure).toReal/2) ∧
    totalVariation qLaw pLaw≤Real.sqrt ((klDiv qLaw.toMeasure pLaw.toMeasure).toReal/2) := by
  constructor
  · exact actual_finite_pinsker_finite_real _ _
      (actual_finite_kl_is_finite _ _ actual_source_positive_support.2)
  · exact actual_finite_pinsker_finite_real _ _
      (actual_finite_kl_is_finite _ _ actual_source_positive_support.1)

theorem actual_source_KL_rounding :
    |(klDiv pLaw.toMeasure qLaw.toMeasure).toReal-(877/10000:ℝ)|<1/20000 ∧
    |(klDiv qLaw.toMeasure pLaw.toMeasure).toReal-(915/10000:ℝ)|<1/20000 := by
  rw [actual_source_directional_log_forms.1,actual_source_directional_log_forms.2]
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_source_sqrt_KL_rounding :
    |Real.sqrt ((klDiv pLaw.toMeasure qLaw.toMeasure).toReal/2)-(209/1000:ℝ)|<1/2000 ∧
    |Real.sqrt ((klDiv qLaw.toMeasure pLaw.toMeasure).toReal/2)-(214/1000:ℝ)|<1/2000 := by
  have hf:=actual_source_directional_log_forms.1
  have hr:=actual_source_directional_log_forms.2
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  have hsf:=Real.sq_sqrt (show 0≤(klDiv pLaw.toMeasure qLaw.toMeasure).toReal/2 by positivity)
  have hsr:=Real.sq_sqrt (show 0≤(klDiv qLaw.toMeasure pLaw.toMeasure).toReal/2 by positivity)
  rw [hf] at hsf
  rw [hr] at hsr
  rw [hf,hr]
  constructor <;> rw [abs_lt] <;> constructor
  all_goals nlinarith [Real.sqrt_nonneg ((9/10)*Real.log 3/2-(13/10)*Real.log 2/2),
    Real.sqrt_nonneg (((9/10)*Real.log 3-(13/10)*Real.log 2)/2),
    Real.sqrt_nonneg (((7/5)*Real.log 2-(4/5)*Real.log 3)/2)]

theorem actual_missing_support_source_direction : klDiv pLaw.toMeasure excludedLaw.toMeasure=⊤ := by
  exact actual_missing_support_infinite_kl _ _ 2
    (by norm_num [pLaw]) (by norm_num [excludedLaw])

theorem actual_reverse_excluded_law_KL :
    (klDiv excludedLaw.toMeasure pLaw.toMeasure).toReal=
      (1/2)*Real.log (5/6)+(1/2)*Real.log (5/3) ∧
    klDiv excludedLaw.toMeasure pLaw.toMeasure≠⊤ := by
  constructor
  · rw [actual_finite_kl_sum _ _ actual_source_positive_support.1]
    norm_num [excludedLaw,pLaw,Fin.sum_univ_three]
  · exact actual_finite_kl_is_finite _ _ actual_source_positive_support.1

theorem actual_reverse_excluded_KL_rounding :
    |(klDiv excludedLaw.toMeasure pLaw.toMeasure).toReal-(164/1000:ℝ)|<1/2000 := by
  rw [actual_reverse_excluded_law_KL.1]
  have h6:Real.log (6:ℝ)=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have h20:Real.log (20:ℝ)=2*Real.log 2+Real.log 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  norm_num [Real.log_div] at *
  rw [h6]
  obtain ⟨h20l,h20u⟩:=log20_enclosure
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  rw [abs_lt]
  constructor <;> linarith

theorem actual_finite_KL_constraint_preserves_old_support {n : ℕ}
    (new old : PMF (Fin n)) (epsilon : ℝ)
    (hconstraint : klDiv new.toMeasure old.toMeasure≤ENNReal.ofReal epsilon) :
    ∀ i, new i ≠ 0 → old i ≠ 0 := by
  intro i hi hzero
  have hinf:=actual_missing_support_infinite_kl new old i hi hzero
  rw [hinf] at hconstraint
  have he:ENNReal.ofReal epsilon=⊤:=top_le_iff.mp hconstraint
  exact ENNReal.ofReal_ne_top he

end SafeLearning.CompleteAppliedInformationExamples
