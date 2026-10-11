import Mathlib

set_option autoImplicit false
noncomputable section
open scoped ENNReal NNReal
namespace SafeLearning.CompleteModulesDesignSequenceEnergy
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def actualEnergy (y : ℕ → E) : ℝ≥0∞ := ∑' t,ENNReal.ofReal (‖y t‖^2)
def actualL2Norm (y : ℕ → E) : ℝ := Real.sqrt (actualEnergy y).toReal

theorem actual_source_initial_storage_certificate_bounds_true_infinite_sequence_energy
    (input : ℕ → E) (output : ℕ → F) (hinput : actualEnergy input=9)
    (hcertificate : actualEnergy output≤ENNReal.ofReal 4+4*actualEnergy input) :
    actualEnergy output≤40 ∧ actualEnergy output≠⊤ ∧
      actualL2Norm output≤Real.sqrt 40 := by
  have he : actualEnergy output≤40 := by norm_num [hinput] at hcertificate;exact hcertificate
  have hf : actualEnergy output≠⊤ := ne_top_of_le_ne_top (by norm_num : (40:ℝ≥0∞)≠⊤) he
  refine ⟨he,hf,?_⟩
  have hr : (actualEnergy output).toReal≤40 := by
    simpa using ENNReal.toReal_mono (by norm_num : (40:ℝ≥0∞)≠⊤) he
  exact Real.sqrt_le_sqrt hr

theorem actual_zero_initial_storage_is_a_genuine_finite_l2_gain_certificate
    (input : ℕ → E) (output : ℕ → F) (hinput : actualEnergy input≠⊤)
    (hcertificate : actualEnergy output≤ENNReal.ofReal 0+4*actualEnergy input) :
    actualEnergy output≠⊤ ∧ actualL2Norm output≤2*actualL2Norm input := by
  have he : actualEnergy output≤4*actualEnergy input := by simpa using hcertificate
  have hfinite : (4:ℝ≥0∞)*actualEnergy input≠⊤ := ENNReal.mul_ne_top (by norm_num) hinput
  have hf := ne_top_of_le_ne_top hfinite he
  refine ⟨hf,?_⟩
  have hr := ENNReal.toReal_mono hfinite he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hr
  have hs0:=Real.sq_sqrt (ENNReal.toReal_nonneg (a:=actualEnergy input))
  have hs1:=Real.sq_sqrt (ENNReal.toReal_nonneg (a:=actualEnergy output))
  unfold actualL2Norm
  nlinarith [Real.sqrt_nonneg (actualEnergy input).toReal,
    Real.sqrt_nonneg (actualEnergy output).toReal]

def sourcePulse (a : ℝ) : ℕ → ℝ := fun t=>if t=0 then a else 0

theorem actual_source_single_pulse_has_its_true_infinite_energy (a : ℝ) :
    actualEnergy (sourcePulse a)=ENNReal.ofReal (a^2) := by
  unfold actualEnergy
  rw [tsum_eq_single 0]
  · simp [sourcePulse,Real.norm_eq_abs,sq_abs]
  · intro t ht;simp [sourcePulse,ht]

theorem actual_source_nonzero_initial_storage_pulse_cannot_use_the_zero_storage_gain :
    actualEnergy (sourcePulse 3)=9 ∧
      actualEnergy (sourcePulse (Real.sqrt 40))=40 ∧
      actualEnergy (sourcePulse (Real.sqrt 40))≤ENNReal.ofReal 4+4*actualEnergy (sourcePulse 3) ∧
      ¬actualL2Norm (sourcePulse (Real.sqrt 40))≤2*actualL2Norm (sourcePulse 3) := by
  have hs:=Real.sq_sqrt (show (0:ℝ)≤40 by norm_num)
  have hi : actualEnergy (sourcePulse 3)=9 := by rw [actual_source_single_pulse_has_its_true_infinite_energy];norm_num
  have ho : actualEnergy (sourcePulse (Real.sqrt 40))=40 := by
    rw [actual_source_single_pulse_has_its_true_infinite_energy,hs];norm_num
  refine ⟨hi,ho,by norm_num [hi,ho],?_⟩
  unfold actualL2Norm
  rw [hi,ho]
  norm_num
  nlinarith [Real.sqrt_nonneg 40]

end SafeLearning.CompleteModulesDesignSequenceEnergy
