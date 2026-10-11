import SafeLearning.CompleteFoundationsCosineExactLogEstimate
import SafeLearning.CompleteFoundationsCosineLocalGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsCosineSourceConsequences
open SafeLearning.CompleteFoundationsCosineContraction
open SafeLearning.CompleteFoundationsCosineNumerics
open SafeLearning.CompleteFoundationsCosineIterates
open SafeLearning.CompleteFoundationsCosineErrorBounds
open SafeLearning.CompleteFoundationsCosineExactLogEstimate

/-- The unrounded logarithmic formula is equivalent to the actual a priori
certificate at every integer iteration. -/
theorem actual_apriori_tolerance_iff_exact_log_threshold (n : ℕ) :
    apriori n≤1/1000000 ↔ actualLogThreshold≤(n:ℝ) := by
  have hs := actual_sine_one_strict_contraction_range
  have hc := actual_cosine_one_positive_and_below_one
  have hA : 0<actualNumerator := by
    unfold actualNumerator apriori
    simp only [pow_zero,mul_one]
    exact mul_pos (div_pos (sub_pos.mpr hc.2) (sub_pos.mpr hs.2)) (by norm_num)
  have hprod : 0<actualNumerator*(Real.sin 1)^n := mul_pos hA (pow_pos hs.1 n)
  have hd : 0<Real.log (1/Real.sin 1) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hs.1).mpr (by simpa using hs.2)
  have hscale : apriori n=actualNumerator*(Real.sin 1)^n/1000000 := by
    unfold actualNumerator
    simp only [apriori,pow_zero,mul_one]
    ring
  have htol : apriori n≤1/1000000 ↔ actualNumerator*(Real.sin 1)^n≤1 := by
    rw [hscale,div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<1000000)]
  have hlog : Real.log (actualNumerator*(Real.sin 1)^n)=
      Real.log actualNumerator-(n:ℝ)*Real.log (1/Real.sin 1) := by
    rw [Real.log_mul (ne_of_gt hA) (ne_of_gt (pow_pos hs.1 n)),Real.log_pow,
      one_div,Real.log_inv]
    ring
  rw [htol,←Real.log_le_log_iff hprod (by norm_num : (0:ℝ)<1),Real.log_one,hlog]
  unfold actualLogThreshold
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- The numerical entries are rounded approximations and cannot be used as
literal equalities for the actual ninth and tenth iterates. -/
theorem actual_ninth_and_tenth_iterates_differ_from_printed_decimals :
    Real.cos^[9] 1≠(731404/1000000:ℝ) ∧
      Real.cos^[10] 1≠(744237/1000000:ℝ) := by
  have h9 := actual_source_first_thirty_two_iterations_enclosed 9 (by omega)
  have h10 := actual_source_first_thirty_two_iterations_enclosed 10 (by omega)
  norm_num [lowerBound,upperBound,sourceTable] at h9 h10
  constructor <;> intro h <;> norm_num at h <;> linarith

theorem actual_posteriori_factor_is_not_the_printed_decimal :
    Real.sin 1/(1-Real.sin 1)≠(531/100:ℝ) := by
  have h := actual_posteriori_factor_rational_enclosure.2
  intro he
  linarith

theorem actual_tenth_certificates_are_not_the_printed_decimals :
    posterioriTen≠(68/1000:ℝ) ∧ apriori 10≠(52/100:ℝ) := by
  have hp := actual_posteriori_factor_rational_enclosure
  have hs := actual_ninth_to_tenth_step_certified_enclosure
  have hlo : (530799350/100000000:ℝ)*(1283331230/100000000000)<posterioriTen :=
    mul_lt_mul hp.1 hs.1.le (by norm_num) (by linarith [hp.1])
  have ha := (actual_apriori_rational_sandwich 10).2
  have hhi : upperApriori 10<(52/100:ℝ) := by norm_num [upperApriori]
  constructor <;> intro he <;> linarith

theorem actual_rounded_factor_times_step_rounds_to_printed_posteriori :
    |(531/100:ℝ)*(12833/1000000)-(68/1000:ℝ)|<1/2000 := by norm_num

end SafeLearning.CompleteFoundationsCosineSourceConsequences
