import SafeLearning.CompleteAppliedInformation
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedInformationBridges
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedTwoAtomRisk
open scoped ENNReal NNReal Classical

theorem actual_binary_tv_half_atom_sum (q r : unitInterval) :
    totalVariation (costLaw q) (costLaw r)=
      (|(costLaw q 0).toReal-(costLaw r 0).toReal|+
        |(costLaw q 1).toReal-(costLaw r 1).toReal|)/2 := by
  rw [actual_binary_total_variation]
  simp only [costLaw,PMF.ofFintype_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2),ENNReal.toReal_ofReal q.2.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr r.2.2),ENNReal.toReal_ofReal r.2.1]
  rw [show 1-(q:ℝ)-(1-(r:ℝ))=-((q:ℝ)-(r:ℝ)) by ring,abs_neg]
  ring

theorem actual_infinite_direction_pinsker_is_vacuous :
    ((klDiv (costLaw fair).toMeasure (costLaw certain).toMeasure/2)^(1/2:ℝ))=⊤ ∧
      ∀ candidate:ℝ≥0∞,candidate≤
        ((klDiv (costLaw fair).toMeasure (costLaw certain).toMeasure/2)^(1/2:ℝ)) := by
  rw [actual_support_mismatch_directions.2,ENNReal.top_div_of_ne_top (by norm_num : (2:ℝ≥0∞)≠⊤),
    ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ)<1/2)]
  simp

end SafeLearning.CompleteAppliedInformationBridges
