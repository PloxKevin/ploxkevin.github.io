import SafeLearning.CompleteModulesLoSBOGaussianHorizon
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SafeLearning.CompleteModulesAdaptiveGaussianEnvelope35

open CompleteModulesLoSBOGaussianHorizon

theorem conditional_gaussian_kernel_implies_genuine_marginal_gaussian_law
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : Ω → ℝ) (history : Ω → H) (variance : ℝ≥0)
    (hn : AEMeasurable noise P) (hh : AEMeasurable history P)
    (hconditional : condDistrib noise history P =ᵐ[P.map history]
      Kernel.const H (gaussianReal 0 variance)) :
    HasLaw noise (gaussianReal 0 variance) P := by
  haveI : IsProbabilityMeasure (P.map history) := Measure.isProbabilityMeasure_map hh
  refine ⟨hn, ?_⟩
  calc
    P.map noise = condDistrib noise history P ∘ₘ P.map history :=
      (condDistrib_comp_map hh hn).symm
    _ = Kernel.const H (gaussianReal 0 variance) ∘ₘ P.map history :=
      Measure.comp_congr hconditional
    _ = gaussianReal 0 variance := by
      rw [Measure.const_comp, measure_univ, one_smul]

/-- Conditional laws, not independence of adaptively chosen queries, suffice. -/
theorem adaptive_conditional_gaussian_errors_obey_the_finite_horizon_envelope
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (horizon : ℕ) (ht : 1 ≤ horizon)
    (noise : Fin horizon → Ω → ℝ) (history : Fin horizon → Ω → H)
    (hn : ∀ t, AEMeasurable (noise t) P) (hh : ∀ t, AEMeasurable (history t) P)
    (sigma : ℝ≥0) (hs : 0 < sigma) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hconditional : ∀ t, condDistrib (noise t) (history t) P =ᵐ[P.map (history t)]
      Kernel.const H (gaussianReal 0 (sigma ^ 2))) :
    P.real {omega | ∃ t, actualHorizonRadius sigma horizon delta < |noise t omega|} ≤ delta := by
  exact actual_all_horizon_gaussian_noise_exceedance_probability_is_at_most_delta
    P horizon ht noise sigma hs delta hd hd1 (fun t =>
      conditional_gaussian_kernel_implies_genuine_marginal_gaussian_law
        P (noise t) (history t) (sigma ^ 2) (hn t) (hh t) (hconditional t))

def sourceSigma : ℝ≥0 := ⟨3 / 20, by norm_num⟩
def sourceEnvelope : ℝ := actualHorizonRadius sourceSigma 100 (1 / 100)
def sourceCertifiedRadius : ℝ := ((19 / 20 : ℝ) - sourceEnvelope) / (4 / 5)

theorem source_envelope_is_the_actual_printed_expression :
    sourceEnvelope = (3 / 20 : ℝ) * Real.sqrt (2 * Real.log 20000) := by
  norm_num [sourceEnvelope, sourceSigma, actualHorizonRadius]

theorem actual_log_twenty_thousand_has_a_rational_enclosure :
    (99034875 / 10000000 : ℝ) < Real.log 20000 ∧
      Real.log 20000 < (99034876 / 10000000 : ℝ) := by
  have ht := CompleteModulesGPNumerics.log_twenty_enclosure
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have he : (20000 : ℝ) = (20 : ℝ) ^ 4 / (2 : ℝ) ^ 3 := by norm_num
  rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  constructor <;> norm_num at * <;> linarith

theorem source_envelope_and_first_radius_have_the_printed_six_decimal_roundings :
    |sourceEnvelope - (667575 / 1000000 : ℝ)| < 1 / 2000000 ∧
      |sourceCertifiedRadius - (353031 / 1000000 : ℝ)| < 1 / 2000000 ∧
      0 < sourceCertifiedRadius ∧ sourceCertifiedRadius < 1 := by
  have hl := actual_log_twenty_thousand_has_a_rational_enclosure
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.log 20000 by linarith)
  have hn := Real.sqrt_nonneg (2 * Real.log 20000)
  have he : (6675754 / 10000000 : ℝ) < sourceEnvelope ∧
      sourceEnvelope < (6675755 / 10000000 : ℝ) := by
    rw [source_envelope_is_the_actual_printed_expression]
    constructor <;> nlinarith
  dsimp [sourceCertifiedRadius]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_lt]
    constructor <;> linarith [he.1, he.2]
  · rw [abs_lt]
    constructor <;> linarith [he.1, he.2]
  · linarith [he.2]
  · linarith [he.1]

theorem actual_source_hundred_adaptive_errors_fail_the_envelope_with_probability_at_most_one_percent
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : Fin 100 → Ω → ℝ) (history : Fin 100 → Ω → H)
    (hn : ∀ t, AEMeasurable (noise t) P) (hh : ∀ t, AEMeasurable (history t) P)
    (hconditional : ∀ t, condDistrib (noise t) (history t) P =ᵐ[P.map (history t)]
      Kernel.const H (gaussianReal 0 (sourceSigma ^ 2))) :
    P.real {omega | ∃ t, sourceEnvelope < |noise t omega|} ≤ (1 / 100 : ℝ) := by
  exact adaptive_conditional_gaussian_errors_obey_the_finite_horizon_envelope
    P 100 (by norm_num) noise history hn hh sourceSigma
    (by norm_num [sourceSigma]) (1 / 100) (by norm_num) (by norm_num) hconditional

/-- The radius protects the true function on the event bounding the first error. -/
theorem first_reading_and_lipschitz_bound_certify_every_point_in_the_source_radius
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (hlip : LipschitzWith (4 / 5 : ℝ≥0) f) (center point : X) (error : ℝ)
    (hreading : (19 / 20 : ℝ) = f center + error)
    (herror : |error| ≤ sourceEnvelope)
    (hdistance : dist point center ≤ sourceCertifiedRadius) :
    0 ≤ f point := by
  have hcenter : (19 / 20 : ℝ) - sourceEnvelope ≤ f center := by
    linarith [le_abs_self error]
  have hdist := hlip.dist_le_mul point center
  rw [Real.dist_eq] at hdist
  have hdrop : f center - f point ≤ (4 / 5 : ℝ) * dist point center := by
    norm_num at hdist
    linarith [neg_le_abs (f point - f center)]
  have hbudget : (4 / 5 : ℝ) * dist point center ≤ (19 / 20 : ℝ) - sourceEnvelope := by
    dsimp [sourceCertifiedRadius] at hdistance
    linarith
  linarith

end SafeLearning.CompleteModulesAdaptiveGaussianEnvelope35
