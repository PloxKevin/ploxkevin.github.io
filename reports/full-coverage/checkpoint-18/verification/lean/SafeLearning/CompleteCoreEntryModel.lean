import Mathlib
import SafeLearning.CompleteCoreBook
import SafeLearning.CompleteAppliedReturns

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SafeLearning.CompleteCoreEntryModel

local instance : MeasurableSpace (Fin 2) := ⊤

theorem mode_weight_zero (p : ℝ≥0) (hp : p ≤ 1) :
    (CompleteCoreBook.modeLaw p hp 0).toReal=1-(p : ℝ) := by
  change ((↑(1-p : ℝ≥0) : ℝ≥0∞)).toReal=1-(p : ℝ)
  rw [ENNReal.coe_toReal]
  rw [NNReal.coe_sub hp]
  norm_num

theorem mode_weight_one (p : ℝ≥0) (hp : p ≤ 1) :
    (CompleteCoreBook.modeLaw p hp 1).toReal=(p : ℝ) := by
  change ((↑p : ℝ≥0∞)).toReal=(p : ℝ)
  simp

def conditionalEntry (mode : Fin 2) : PMF (Fin 2) :=
  if mode=0 then CompleteCoreBook.modeLaw (1/50) (by rw [← NNReal.coe_le_coe];norm_num)
  else CompleteCoreBook.modeLaw (1/5) (by rw [← NNReal.coe_le_coe];norm_num)

-- The source's two-stage experiment: choose a mode, then its Bernoulli entry.
def entryLaw (p : ℝ≥0) (hp : p ≤ 1) : PMF (Fin 2) :=
  (CompleteCoreBook.modeLaw p hp).bind conditionalEntry

theorem actual_entry_probability (p : ℝ≥0) (hp : p ≤ 1) :
    (entryLaw p hp 1).toReal=(1-(p : ℝ))*(1/50)+(p : ℝ)*(1/5) := by
  rw [entryLaw,PMF.bind_apply,tsum_fintype,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one,Fin.succ_zero_eq_one]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul]
  rw [mode_weight_zero,mode_weight_one]
  norm_num [conditionalEntry,mode_weight_one]

theorem actual_entry_never_zero (p : ℝ≥0) (hp : p ≤ 1) :
    1/50 ≤ (entryLaw p hp 1).toReal := by
  rw [actual_entry_probability]
  have hh := p.coe_nonneg
  linarith

theorem one_step_actual_indicator_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (entry : Ω → Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hlaw : HasLaw entry (entryLaw p hp).toMeasure μ) :
    (∫ omega, (![0,1] : Fin 2 → ℝ) (entry omega) ∂μ)=
      (1-(p : ℝ))*(1/50)+(p : ℝ)*(1/5) := by
  have hm : Measurable (![0,1] : Fin 2 → ℝ) := measurable_from_top
  rw [show (fun omega => (![0,1] : Fin 2 → ℝ) (entry omega))=
    (![0,1] : Fin 2 → ℝ) ∘ entry from rfl]
  rw [hlaw.integral_comp hm.aestronglyMeasurable,PMF.integral_eq_sum]
  simpa [Fin.sum_univ_succ,smul_eq_mul] using actual_entry_probability p hp

theorem actual_pathwise_indicator_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (entry : ℕ → Ω → Fin 2)
    (p : ℝ≥0) (hp : p ≤ 1)
    (hlaw : ∀ n, HasLaw (entry n) (entryLaw p hp).toMeasure μ)
    (gamma : ℝ) (hg : |gamma| < 1) :
    (∫ omega, ∑' n : ℕ, gamma^n*(![0,1] : Fin 2 → ℝ) (entry n omega) ∂μ)=
      ((1-(p : ℝ))*(1/50)+(p : ℝ)*(1/5))/(1-gamma) := by
  have hm : Measurable (![0,1] : Fin 2 → ℝ) := measurable_from_top
  have hmeas : ∀ n,AEStronglyMeasurable
      (fun omega => (![0,1] : Fin 2 → ℝ) (entry n omega)) μ :=
    fun n => (hm.comp_aemeasurable (hlaw n).aemeasurable).aestronglyMeasurable
  have hbound : ∀ n,∀ᵐ omega ∂μ, |(![0,1] : Fin 2 → ℝ) (entry n omega)| ≤ 1 := by
    intro n
    exact ae_of_all μ (fun omega => by generalize entry n omega=i;fin_cases i <;> norm_num)
  rw [CompleteAppliedReturns.discounted_expectation_interchange μ _ gamma 1 hg hmeas hbound]
  have heq : (fun n : ℕ => gamma^n*(∫ omega, (![0,1] : Fin 2 → ℝ) (entry n omega) ∂μ))=
      (fun n : ℕ => gamma^n*((1-(p : ℝ))*(1/50)+(p : ℝ)*(1/5))) := by
    funext n
    rw [one_step_actual_indicator_expectation μ (entry n) p hp (hlaw n)]
  rw [heq,CoreModules.discounted_constant _ _ hg]

theorem actual_indicator_return_equals_mode_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (entry : ℕ → Ω → Fin 2)
    (p : ℝ≥0) (hp : p ≤ 1)
    (hlaw : ∀ n, HasLaw (entry n) (entryLaw p hp).toMeasure μ)
    (gamma : ℝ) (hg : |gamma| < 1) :
    (∫ omega, ∑' n : ℕ, gamma^n*(![0,1] : Fin 2 → ℝ) (entry n omega) ∂μ)=
      CompleteCoreBook.modeReturn p hp gamma (1/50) (1/5) := by
  rw [actual_pathwise_indicator_return μ entry p hp hlaw gamma hg,
    CompleteCoreBook.mode_discounted_return p hp gamma _ _ hg]

theorem tighter_budget_actual_entry_probability :
    (entryLaw (1/4) (by rw [← NNReal.coe_le_coe];norm_num) 1).toReal=13/200 ∧
      0 < (entryLaw (1/4) (by rw [← NNReal.coe_le_coe];norm_num) 1).toReal := by
  rw [actual_entry_probability]
  norm_num

end SafeLearning.CompleteCoreEntryModel
