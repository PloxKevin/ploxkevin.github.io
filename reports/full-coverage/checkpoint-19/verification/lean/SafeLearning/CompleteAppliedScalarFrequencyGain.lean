import SafeLearning.CompleteAppliedScalarStepResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteAppliedScalarFrequencyGain
open CompleteAppliedScalarStepResponse

def actualFrequencyGain (omega : ℝ) : ℝ := ‖sourceTransfer ((omega:ℂ)*Complex.I)‖

theorem actual_source_frequency_denominator_and_reciprocal_moduli (omega : ℝ) :
    ‖((omega:ℂ)*Complex.I)+2‖=Real.sqrt (4+omega^2) ∧
      actualFrequencyGain omega=1/Real.sqrt (4+omega^2) := by
  have hd : ‖((omega:ℂ)*Complex.I)+2‖=Real.sqrt (4+omega^2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  refine ⟨hd,?_⟩
  rw [actualFrequencyGain,sourceTransfer,norm_div,norm_one,hd]

theorem actual_source_zero_and_two_frequency_values_and_rounding :
    actualFrequencyGain 0=1/2 ∧ actualFrequencyGain 2=1/Real.sqrt 8 ∧
      |actualFrequencyGain 2-(353553/1000000:ℝ)|<1/2000000 := by
  have h0 := (actual_source_frequency_denominator_and_reciprocal_moduli 0).2
  have h2 := (actual_source_frequency_denominator_and_reciprocal_moduli 2).2
  norm_num at h0
  have h2eq : actualFrequencyGain 2=1/Real.sqrt 8 := by
    convert h2 using 1 <;> norm_num
  refine ⟨h0,h2eq,?_⟩
  rw [h2eq,abs_lt]
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<8)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤8)
  have hlo : (3535525/10000000:ℝ)<1/Real.sqrt 8 := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith
  have hhi : 1/Real.sqrt 8<(3535535/10000000:ℝ) := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  constructor <;> linarith

theorem actual_half_is_the_attained_worst_frequency_gain :
    IsGreatest (Set.range actualFrequencyGain) (1/2:ℝ) ∧
      sSup (Set.range actualFrequencyGain)=1/2 := by
  have hupper (omega : ℝ) : actualFrequencyGain omega≤1/2 := by
    rw [(actual_source_frequency_denominator_and_reciprocal_moduli omega).2]
    have hp : 0<Real.sqrt (4+omega^2) := Real.sqrt_pos.mpr (by positivity)
    have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤4+omega^2)
    rw [div_le_iff₀ hp]
    nlinarith [sq_nonneg omega,Real.sqrt_nonneg (4+omega^2)]
  have hg : IsGreatest (Set.range actualFrequencyGain) (1/2:ℝ) := by
    refine ⟨⟨0,actual_source_zero_and_two_frequency_values_and_rounding.1⟩,?_⟩
    rintro gain ⟨omega,rfl⟩
    exact hupper omega
  exact ⟨hg,hg.csSup_eq⟩

end SafeLearning.CompleteAppliedScalarFrequencyGain
