import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRGain

def actualParameterizedCurrentKernel (gain storage angle : ℝ) : ℝ := Real.sin angle*Real.sqrt (gain^2-storage)
def actualParameterizedDelayedKernel (storage angle : ℝ) : ℝ := Real.cos angle*Real.sqrt storage

theorem actual_parameterized_kernel_absolute_gain_bound
    (gain storage angle : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle| ≤ gain := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (![|Real.sin angle|,|Real.cos angle|] : Fin 2 → ℝ)
    ![Real.sqrt (gain^2-storage),Real.sqrt storage]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    sq_abs,Real.sq_sqrt (sub_nonneg.mpr hupper),Real.sq_sqrt hstorage] at hc
  rw [Real.sin_sq_add_cos_sq,one_mul] at hc
  have he : |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=
      |Real.sin angle| *Real.sqrt (gain^2-storage)+|Real.cos angle| *Real.sqrt storage := by
    simp [actualParameterizedCurrentKernel,actualParameterizedDelayedKernel,abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [he]
  have hn : 0 ≤ |Real.sin angle| *Real.sqrt (gain^2-storage)+|Real.cos angle| *Real.sqrt storage := by positivity
  nlinarith

def actualFIRTransfer (currentGain delayedGain frequency : ℝ) : ℂ :=
  (currentGain:ℂ)+(delayedGain:ℂ)*Complex.exp (-((frequency:ℂ)*Complex.I))

theorem actual_fir_frequency_bound (currentGain delayedGain frequency : ℝ) :
    ‖actualFIRTransfer currentGain delayedGain frequency‖ ≤ |currentGain|+|delayedGain| := by
  unfold actualFIRTransfer
  have he : ‖Complex.exp (-((frequency:ℂ)*Complex.I))‖=1 := by
    rw [Complex.norm_exp]
    simp
  simpa only [norm_mul,he,mul_one,Complex.norm_real,Real.norm_eq_abs] using
    norm_add_le (currentGain:ℂ) ((delayedGain:ℂ)*Complex.exp (-((frequency:ℂ)*Complex.I)))

theorem actual_positive_fir_frequency_bound_is_attained_at_zero
    (currentGain delayedGain : ℝ) (hcurrent : 0 ≤ currentGain) (hdelayed : 0 ≤ delayedGain) :
    ‖actualFIRTransfer currentGain delayedGain 0‖=|currentGain|+|delayedGain| := by
  simp [actualFIRTransfer,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hcurrent,abs_of_nonneg hdelayed,abs_of_nonneg (add_nonneg hcurrent hdelayed)]

theorem actual_positive_fir_frequency_supremum
    (currentGain delayedGain : ℝ) (hcurrent : 0 ≤ currentGain) (hdelayed : 0 ≤ delayedGain) :
    sSup (Set.range (fun frequency : ℝ => ‖actualFIRTransfer currentGain delayedGain frequency‖))=
      |currentGain|+|delayedGain| := by
  have hgreatest : IsGreatest (Set.range (fun frequency : ℝ => ‖actualFIRTransfer currentGain delayedGain frequency‖))
      (|currentGain|+|delayedGain|) := by
    constructor
    · exact ⟨0,actual_positive_fir_frequency_bound_is_attained_at_zero currentGain delayedGain hcurrent hdelayed⟩
    · rintro value ⟨frequency,rfl⟩
      exact actual_fir_frequency_bound currentGain delayedGain frequency
  exact hgreatest.isLUB.csSup_eq (Set.range_nonempty _)

theorem actual_parameterized_fir_frequency_gain_bound
    (gain storage angle frequency : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    ‖actualFIRTransfer (actualParameterizedCurrentKernel gain storage angle)
        (actualParameterizedDelayedKernel storage angle) frequency‖ ≤ gain :=
  (actual_fir_frequency_bound _ _ frequency).trans
    (actual_parameterized_kernel_absolute_gain_bound gain storage angle hgain hstorage hupper)

/-- The exact squared Cauchy--Schwarz gap identifies the alignment condition. -/
theorem actual_parameterized_gain_squared_gap
    (gain storage angle : ℝ) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    gain^2-(|actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|)^2=
      (|Real.sin angle| *Real.sqrt storage-|Real.cos angle| *Real.sqrt (gain^2-storage))^2 := by
  have hp := Real.sq_sqrt hstorage
  have hr := Real.sq_sqrt (sub_nonneg.mpr hupper)
  have ht := Real.sin_sq_add_cos_sq angle
  rw [actualParameterizedCurrentKernel,actualParameterizedDelayedKernel]
  simp only [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : |Real.sin angle|^2=Real.sin angle^2 := sq_abs _
  have hc : |Real.cos angle|^2=Real.cos angle^2 := sq_abs _
  nlinarith

end SafeLearning.CompleteModulesFIRGain
