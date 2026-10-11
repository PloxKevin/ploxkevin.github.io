import SafeLearning.CompleteAppliedBinaryTemperature
import SafeLearning.CompleteFoundationsExponentialNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory InformationTheory
namespace SafeLearning.CompleteAppliedBinaryTemperatureNumbers
open SafeLearning.CompleteAppliedBinaryTemperature SafeLearning.CompleteAppliedTemperatureSoftmax
open SafeLearning.CompleteFoundationsExponentialNumerics

theorem actual_e_reciprocal_and_squared_reciprocal_enclosures :
    (367879/1000000:ℝ)<(Real.exp 1)⁻¹ ∧ (Real.exp 1)⁻¹<367880/1000000 ∧
      (135335/1000000:ℝ)<((Real.exp 1)^2)⁻¹ ∧ ((Real.exp 1)^2)⁻¹<135336/1000000 := by
  have h := actual_exponential_rational_enclosures_needed_by_the_source
  have hp := Real.exp_pos (1:ℝ)
  have h2l := pow_lt_pow_left₀ h.1 (by norm_num) (by norm_num : (2:ℕ)≠0)
  have h2u := pow_lt_pow_left₀ h.2.1 hp.le (by norm_num : (2:ℕ)≠0)
  norm_num1 at h2l h2u
  rw [← one_div,← one_div]
  refine ⟨?_,?_,?_,?_⟩
  · rw [lt_div_iff₀ hp];nlinarith [h.2.1]
  · rw [div_lt_iff₀ hp];nlinarith [h.1]
  · rw [lt_div_iff₀ (pow_pos hp 2)];nlinarith [h2u]
  · rw [div_lt_iff₀ (pow_pos hp 2)];nlinarith [h2l]

theorem actual_four_comparison_exponentials_have_certified_bounds :
    Real.exp (12692/100000:ℝ)<1135327/1000000 ∧
      (1135348/1000000:ℝ)<Real.exp (12694/100000) ∧
      Real.exp (31326/100000:ℝ)<1367878/1000000 ∧
      (1367890/1000000:ℝ)<Real.exp (31327/100000) := by
  have h1 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (12692/100000:ℝ) (by norm_num)
  have h2 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (12694/100000:ℝ) (by norm_num)
  have h3 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (31326/100000:ℝ) (by norm_num)
  have h4 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (31327/100000:ℝ) (by norm_num)
  norm_num [expPolynomial,Finset.sum_range_succ,Nat.factorial,abs_le] at h1 h2 h3 h4
  refine ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_binary_soft_values_have_true_log_normalizations :
    actualTemperatureValue actualBinaryScores (1/2)=1+(1/2)*Real.log (1+((Real.exp 1)^2)⁻¹) ∧
      actualTemperatureValue actualBinaryScores 1=1+Real.log (1+(Real.exp 1)⁻¹) := by
  have hp := Real.exp_pos (1:ℝ)
  have he2 : Real.exp (2:ℝ)=(Real.exp 1)^2 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add,pow_two]
  have hprod (x : ℝ) (hx : 0 < x) : 1+x=x*(1+x⁻¹) := by field_simp;ring
  have hlog (x : ℝ) (hx : 0 < x) :
      Real.log (1+x)=Real.log x+Real.log (1+x⁻¹) := by
    rw [hprod x hx,Real.log_mul hx.ne' (by positivity)]
  rw [(actual_binary_softmax_and_soft_value_have_the_literal_formulas (1/2)).2.2,
    (actual_binary_softmax_and_soft_value_have_the_literal_formulas 1).2.2]
  norm_num only [one_div_one_div,div_one]
  rw [he2,hlog ((Real.exp 1)^2) (pow_pos hp 2),hlog (Real.exp 1) hp,
    Real.log_pow,Real.log_exp]
  constructor <;> ring

theorem actual_binary_soft_value_enclosures :
    (106346/100000:ℝ)<actualTemperatureValue actualBinaryScores (1/2) ∧
      actualTemperatureValue actualBinaryScores (1/2)<106347/100000 ∧
      (131326/100000:ℝ)<actualTemperatureValue actualBinaryScores 1 ∧
      actualTemperatureValue actualBinaryScores 1<131327/100000 := by
  have hr := actual_e_reciprocal_and_squared_reciprocal_enclosures
  have he := actual_four_comparison_exponentials_have_certified_bounds
  have hlo2 : Real.exp (12692/100000:ℝ)<1+((Real.exp 1)^2)⁻¹ := by linarith [hr.2.2.1,he.1]
  have hup2 : 1+((Real.exp 1)^2)⁻¹<Real.exp (12694/100000:ℝ) := by linarith [hr.2.2.2,he.2.1]
  have hlo1 : Real.exp (31326/100000:ℝ)<1+(Real.exp 1)⁻¹ := by linarith [hr.1,he.2.2.1]
  have hup1 : 1+(Real.exp 1)⁻¹<Real.exp (31327/100000:ℝ) := by linarith [hr.2.1,he.2.2.2]
  have hl2 := Real.log_lt_log (Real.exp_pos _) hlo2
  have hu2 := Real.log_lt_log (by positivity : 0 < 1+((Real.exp 1)^2)⁻¹) hup2
  have hl1 := Real.log_lt_log (Real.exp_pos _) hlo1
  have hu1 := Real.log_lt_log (by positivity : 0 < 1+(Real.exp 1)⁻¹) hup1
  rw [Real.log_exp] at hl2 hu2 hl1 hu1
  rw [actual_binary_soft_values_have_true_log_normalizations.1,
    actual_binary_soft_values_have_true_log_normalizations.2]
  refine ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_binary_action_probability_enclosures :
    (11920/100000:ℝ)<(actualTemperatureLaw actualBinaryScores (1/2) 0).toReal ∧
      (actualTemperatureLaw actualBinaryScores (1/2) 0).toReal<11921/100000 ∧
      (88079/100000:ℝ)<(actualTemperatureLaw actualBinaryScores (1/2) 1).toReal ∧
      (actualTemperatureLaw actualBinaryScores (1/2) 1).toReal<88080/100000 ∧
      (26894/100000:ℝ)<(actualTemperatureLaw actualBinaryScores 1 0).toReal ∧
      (actualTemperatureLaw actualBinaryScores 1 0).toReal<26895/100000 ∧
      (73105/100000:ℝ)<(actualTemperatureLaw actualBinaryScores 1 1).toReal ∧
      (actualTemperatureLaw actualBinaryScores 1 1).toReal<73106/100000 := by
  have h := actual_exponential_rational_enclosures_needed_by_the_source
  have hp := Real.exp_pos (1:ℝ)
  have h2l := pow_lt_pow_left₀ h.1 (by norm_num) (by norm_num : (2:ℕ)≠0)
  have h2u := pow_lt_pow_left₀ h.2.1 hp.le (by norm_num : (2:ℕ)≠0)
  norm_num1 at h2l h2u
  have he2 : Real.exp (2:ℝ)=(Real.exp 1)^2 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add,pow_two]
  rw [(actual_binary_softmax_and_soft_value_have_the_literal_formulas (1/2)).1,
    (actual_binary_softmax_and_soft_value_have_the_literal_formulas (1/2)).2.1,
    (actual_binary_softmax_and_soft_value_have_the_literal_formulas 1).1,
    (actual_binary_softmax_and_soft_value_have_the_literal_formulas 1).2.1]
  norm_num only [one_div_one_div,div_one]
  rw [he2]
  have hp1 : 0 < 1+Real.exp (1:ℝ) := by positivity
  have hp2 : 0 < 1+(Real.exp (1:ℝ))^2 := by positivity
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [lt_div_iff₀ hp2];nlinarith [h2u]
  · rw [div_lt_iff₀ hp2];nlinarith [h2l]
  · rw [lt_div_iff₀ hp2];nlinarith [h2l]
  · rw [div_lt_iff₀ hp2];nlinarith [h2u]
  · rw [lt_div_iff₀ hp1];nlinarith [h.2.1]
  · rw [div_lt_iff₀ hp1];nlinarith [h.1]
  · rw [lt_div_iff₀ hp1];nlinarith [h.1]
  · rw [div_lt_iff₀ hp1];nlinarith [h.2.1]

theorem actual_source_soft_values_and_uniform_variational_gap_have_certified_roundings :
    |actualTemperatureValue actualBinaryScores (1/2)-(1.0635:ℝ)|<0.00005 ∧
      |actualTemperatureValue actualBinaryScores 1-(1.3133:ℝ)|<0.00005 ∧
      |(1/2+(1/2)*Real.log 2)-(0.8466:ℝ)|<0.00005 ∧
      |(klDiv actualUniformBinaryLaw.toMeasure
        (actualTemperatureLaw actualBinaryScores (1/2)).toMeasure).toReal-(0.4338:ℝ)|<0.00005 ∧
      |(1+(1/2)*Real.log 2)-(1.3466:ℝ)|<0.00005 ∧
      |(1+Real.log 2)-(1.6931:ℝ)|<0.00005 := by
  have hv := actual_binary_soft_value_enclosures
  have hloglo := Real.log_two_gt_d9
  have hloghi := Real.log_two_lt_d9
  have hgap := (actual_uniform_binary_entropy_expected_score_and_true_variational_identity
    (1/2) (by norm_num)).2.2.2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals apply abs_lt.mpr;constructor
  all_goals linarith [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2]

end SafeLearning.CompleteAppliedBinaryTemperatureNumbers
