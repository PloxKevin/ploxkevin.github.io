import SafeLearning.CompleteAppliedFiniteEntropy
import SafeLearning.CompleteFoundationsExponentialLesson

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory InformationTheory Set Filter
namespace SafeLearning.CompleteAppliedTemperatureSoftmax
open SafeLearning.CompleteAppliedFiniteEntropy SafeLearning.CompleteAppliedFiniteKL
open SafeLearning.CompleteAppliedFiniteKLSupport SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteFoundationsExponentialLesson

variable {n : ℕ} [NeZero n]

def actualPartition (scores : Fin n → ℝ) (temperature : ℝ) : ℝ :=
  ∑ i, Real.exp (scores i / temperature)

theorem actual_partition_is_strictly_positive (scores : Fin n → ℝ) (temperature : ℝ) :
    0 < actualPartition scores temperature := by
  classical
  unfold actualPartition
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

def actualTemperatureLaw (scores : Fin n → ℝ) (temperature : ℝ) : PMF (Fin n) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (Real.exp (scores i / temperature) /
    actualPartition scores temperature)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        (div_pos (Real.exp_pos _) (actual_partition_is_strictly_positive _ _)).le)]
      rw [← Finset.sum_div]
      change ENNReal.ofReal (actualPartition scores temperature /
        actualPartition scores temperature)=1
      rw [div_self (actual_partition_is_strictly_positive _ _).ne']
      norm_num)

def actualTemperatureValue (scores : Fin n → ℝ) (temperature : ℝ) : ℝ :=
  temperature * Real.log (actualPartition scores temperature)

def actualTemperatureObjective (scores : Fin n → ℝ) (temperature : ℝ)
    (law : PMF (Fin n)) : ℝ :=
  (∫ i, scores i ∂law.toMeasure) + temperature * shannonEntropy law

theorem actual_temperature_law_has_the_literal_normalized_exponential_masses
    (scores : Fin n → ℝ) (temperature : ℝ) (i : Fin n) :
    (actualTemperatureLaw scores temperature i).toReal=
      Real.exp (scores i / temperature) / actualPartition scores temperature := by
  rw [actualTemperatureLaw,PMF.ofFintype_apply,ENNReal.toReal_ofReal]
  exact (div_pos (Real.exp_pos _) (actual_partition_is_strictly_positive _ _)).le

theorem actual_temperature_law_has_full_support_and_positive_real_masses
    (scores : Fin n → ℝ) (temperature : ℝ) (i : Fin n) :
    actualTemperatureLaw scores temperature i ≠ 0 ∧
      0 < (actualTemperatureLaw scores temperature i).toReal := by
  have h : 0 < Real.exp (scores i / temperature) / actualPartition scores temperature :=
    div_pos (Real.exp_pos _) (actual_partition_is_strictly_positive _ _)
  refine ⟨?_,?_⟩
  · simp only [actualTemperatureLaw,PMF.ofFintype_apply,ne_eq,ENNReal.ofReal_eq_zero]
    exact not_le.mpr h
  · rwa [actual_temperature_law_has_the_literal_normalized_exponential_masses]

theorem actual_temperature_law_log_mass (scores : Fin n → ℝ) (temperature : ℝ)
    (i : Fin n) :
    Real.log (actualTemperatureLaw scores temperature i).toReal=
      scores i / temperature - Real.log (actualPartition scores temperature) := by
  rw [actual_temperature_law_has_the_literal_normalized_exponential_masses,
    Real.log_div (Real.exp_pos _).ne' (actual_partition_is_strictly_positive _ _).ne',
    Real.log_exp]

/-- The canonical measure-theoretic KL is finite and gives the actual variational gap. -/
theorem actual_expected_score_plus_temperature_entropy_is_value_minus_true_kl
    (scores : Fin n → ℝ) (temperature : ℝ) (ht : 0 < temperature)
    (law : PMF (Fin n)) :
    temperature * (klDiv law.toMeasure (actualTemperatureLaw scores temperature).toMeasure).toReal=
      actualTemperatureValue scores temperature - actualTemperatureObjective scores temperature law := by
  have hs := fun i => (actual_temperature_law_has_full_support_and_positive_real_masses
    scores temperature i).1
  rw [actual_finite_kl_sum law (actualTemperatureLaw scores temperature) hs,
    actualTemperatureValue,actualTemperatureObjective,PMF.integral_eq_sum,actual_entropy_sum,
    Finset.mul_sum]
  have hi (i : Fin n) : temperature * ((law i).toReal *
      Real.log ((law i).toReal / (actualTemperatureLaw scores temperature i).toReal))=
      temperature*((law i).toReal*Real.log (law i).toReal) - (law i).toReal*scores i +
        (law i).toReal*(temperature*Real.log (actualPartition scores temperature)) := by
    by_cases hz : (law i).toReal=0
    · simp [hz]
    · rw [Real.log_div hz
        (actual_temperature_law_has_full_support_and_positive_real_masses scores temperature i).2.ne',
        actual_temperature_law_log_mass]
      field_simp
      ring
  simp only [hi,Finset.sum_add_distrib,Finset.sum_sub_distrib,smul_eq_mul,
    neg_mul,Finset.sum_neg_distrib,← Finset.mul_sum,← Finset.sum_mul,
    actual_finite_weights_sum,one_mul]
  ring

theorem actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
    (scores : Fin n → ℝ) (temperature : ℝ) (ht : 0 < temperature)
    (law : PMF (Fin n)) :
    actualTemperatureObjective scores temperature law ≤ actualTemperatureValue scores temperature ∧
      (actualTemperatureObjective scores temperature law=actualTemperatureValue scores temperature ↔
        law=actualTemperatureLaw scores temperature) := by
  have hs := fun i => (actual_temperature_law_has_full_support_and_positive_real_masses
    scores temperature i).1
  have hgap := actual_expected_score_plus_temperature_entropy_is_value_minus_true_kl scores temperature ht law
  have hnon := mul_nonneg ht.le (ENNReal.toReal_nonneg
    (a:=klDiv law.toMeasure (actualTemperatureLaw scores temperature).toMeasure))
  refine ⟨by linarith,?_⟩
  have hfin := actual_finite_kl_is_finite law (actualTemperatureLaw scores temperature) hs
  have hz : (klDiv law.toMeasure (actualTemperatureLaw scores temperature).toMeasure).toReal=0 ↔
      klDiv law.toMeasure (actualTemperatureLaw scores temperature).toMeasure=0 := by
    rw [ENNReal.toReal_eq_zero_iff]
    simp only [hfin,or_false]
  rw [← actual_finite_gibbs_equality law (actualTemperatureLaw scores temperature),← hz]
  constructor
  · intro he
    exact (mul_eq_zero.mp (by linarith : temperature*
      (klDiv law.toMeasure (actualTemperatureLaw scores temperature).toMeasure).toReal=0)).resolve_left ht.ne'
  · intro he
    rw [he,mul_zero] at hgap
    linarith

theorem actual_temperature_value_has_the_source_maximum_gap_and_true_zero_temperature_limit
    (scores : Fin n → ℝ) :
    (∀ temperature>0, actualMaximum scores ≤ actualTemperatureValue scores temperature ∧
      actualTemperatureValue scores temperature ≤ actualMaximum scores + temperature*Real.log n) ∧
      Tendsto (actualTemperatureValue scores) (𝓝[>] (0:ℝ)) (𝓝 (actualMaximum scores)) := by
  constructor
  · intro temperature ht
    simpa only [actualTemperatureValue,actualPartition,actualSoftMaximum,Fintype.card_fin]
      using actual_soft_maximum_is_between_maximum_and_maximum_plus_temperature_log_card scores temperature ht
  · exact actual_soft_maximum_tends_to_actual_maximum_as_temperature_decreases_to_zero scores

end SafeLearning.CompleteAppliedTemperatureSoftmax
