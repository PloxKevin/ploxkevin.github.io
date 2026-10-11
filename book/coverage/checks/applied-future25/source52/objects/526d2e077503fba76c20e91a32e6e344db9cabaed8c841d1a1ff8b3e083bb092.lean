import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLoSBOPracticeNumerics

def actualMultiplier : ℝ := 1+Real.sqrt (2+2*Real.log 10)
def actualLowerEndpoint : ℝ := 1/2-(1/10)*actualMultiplier

theorem actual_log_ten_is_enclosed_from_genuine_log_twenty_and_log_two :
    (230258508/100000000:ℝ)<Real.log 10 ∧ Real.log 10<(230258510/100000000:ℝ) := by
  have h20 := CompleteModulesGPNumerics.log_twenty_enclosure
  have h2 := Real.log_two_near_10
  have he : Real.log (10:ℝ)=Real.log 20-Real.log 2 := by
    rw [←Real.log_div (by norm_num : (20:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
    norm_num
  rw [he]
  constructor <;> linarith [(abs_le.mp h2).1,(abs_le.mp h2).2,h20.1,h20.2]

theorem actual_source_real_beta_formula_reduces_to_the_literal_multiplier :
    Real.sqrt (1/25:ℝ)=1/5 ∧
      1+((1/5:ℝ)/Real.sqrt (1/25))*Real.sqrt (2+2*Real.log (1/(1/10)))=actualMultiplier := by
  have hs : Real.sqrt (1/25:ℝ)=1/5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hs,?_⟩
  rw [hs]
  norm_num [actualMultiplier]

theorem actual_source_multiplier_and_lower_endpoint_have_the_printed_roundings :
    |actualMultiplier-(35700526/10000000:ℝ)|<1/20000000 ∧
      |actualLowerEndpoint-(1429947/10000000:ℝ)|<1/20000000 ∧
      actualLowerEndpoint<(1/5:ℝ) ∧
      (1/2:ℝ)-(1/10)*2=3/10 ∧ (1/5:ℝ)<3/10 := by
  obtain ⟨hl,hu⟩ := actual_log_ten_is_enclosed_from_genuine_log_twenty_and_log_two
  have hp : 0 ≤ 2+2*Real.log 10 := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (2+2*Real.log 10)
  have hb : (357005255/100000000:ℝ)<actualMultiplier ∧
      actualMultiplier<(357005258/100000000:ℝ) := by
    unfold actualMultiplier
    constructor <;> nlinarith
  refine ⟨?_,?_,?_,by norm_num,by norm_num⟩
  · rw [abs_lt]
    constructor <;> linarith [hb.1,hb.2]
  · unfold actualLowerEndpoint
    rw [abs_lt]
    constructor <;> linarith [hb.1,hb.2]
  · unfold actualLowerEndpoint
    linarith [hb.1]

end SafeLearning.CompleteModulesLoSBOPracticeNumerics
