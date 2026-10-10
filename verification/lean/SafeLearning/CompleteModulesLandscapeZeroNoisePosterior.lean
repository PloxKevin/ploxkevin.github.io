import SafeLearning.CompleteModulesSafeOptKernelPosteriorError

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeZeroNoisePosterior
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
open CompleteModulesKernel CompleteModulesSafeOptKernelPosteriorError

def actualZeroNoiseEvent {Ω : Type*} (Y : ℕ → Ω → ℝ) : Set Ω :=
  {omega | ∀ i, Y i omega = 0}

/-- Countably many actual zero-width noise support assumptions give one
common almost-everywhere zero-noise event. -/
theorem actual_zero_width_noise_support_gives_one_common_alltime_zero_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0) :
    ∀ᵐ omega ∂μ, ∀ i, Y i omega = 0 := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [hY i] with omega hw
  exact le_antisymm hw.2 hw.1

/-- The actual common zero-noise event has probability one. No query or
noise independence hypothesis is needed. -/
theorem actual_common_alltime_zero_noise_event_has_probability_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0) :
    μ (actualZeroNoiseEvent Y) = 1 := by
  have he : actualZeroNoiseEvent Y =ᵐ[μ] (univ : Set Ω) := by
    filter_upwards [actual_zero_width_noise_support_gives_one_common_alltime_zero_event μ Y hY]
      with omega hw
    simp [actualZeroNoiseEvent, hw]
  rw [measure_congr he, measure_univ]

/-- The actual kernel self-normalized noise quadratic vanishes for every
sample count when all of its actual observed noise values are zero. -/
theorem actual_allzero_noise_has_zero_kernel_noise_quadratic_at_every_round
    {X : Type*} (kernel : X → X → ℝ) (lambda : ℝ) (query : ℕ → X)
    (noise : ℕ → ℝ) (hnoise : ∀ i, noise i = 0) :
    ∀ n, actualKernelNoiseQuadratic kernel lambda query noise n = 0 := by
  intro n
  simp [actualKernelNoiseQuadratic, hnoise]

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- The true deterministic regularized posterior error has only its RKHS
bias contribution for zero observed noise. The squared-norm convention gives sqrt B. -/
theorem actual_zero_noise_regularized_kernel_posterior_has_the_squared_norm_band
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (f : H)
    (B : ℝ) (hf : ‖f‖ ^ 2 ≤ B) (noise : ℕ → ℝ) (hnoise : ∀ i, noise i = 0) :
    ∀ n x,
      |f x - actualKernelMeanAt kernel lambda query (fun y => f y) noise n x| ≤
        Real.sqrt B * Real.sqrt (actualKernelVarianceAt kernel lambda query n x) := by
  intro n x
  have he := actual_finite_kernel_posterior_error_is_bounded_at_every_input_and_round
    kernel hkernel lambda hlambda query f noise n x
  rw [actual_allzero_noise_has_zero_kernel_noise_quadratic_at_every_round
    kernel lambda query noise hnoise n] at he
  simp only [Real.sqrt_zero, zero_div, add_zero] at he
  exact he.trans (mul_le_mul_of_nonneg_right (Real.le_sqrt_of_sq_le hf) (Real.sqrt_nonneg _))

/-- One common actual event simultaneously contains all zero noise values,
all zero kernel noise quadratics, and every-round/every-input posterior band. -/
theorem actual_zero_width_noise_support_gives_one_common_alltime_kernel_posterior_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → Ω → X) (f : H)
    (B : ℝ) (hf : ‖f‖ ^ 2 ≤ B) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0) :
    ∀ᵐ omega ∂μ, (∀ i, Y i omega = 0) ∧
      (∀ n, actualKernelNoiseQuadratic kernel lambda (fun i => query i omega) (fun i => Y i omega) n = 0) ∧
      ∀ n x,
        |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y)
          (fun i => Y i omega) n x| ≤
        Real.sqrt B * Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x) := by
  filter_upwards [actual_zero_width_noise_support_gives_one_common_alltime_zero_event μ Y hY]
    with omega hw
  exact ⟨hw, actual_allzero_noise_has_zero_kernel_noise_quadratic_at_every_round
    kernel lambda (fun i => query i omega) (fun i => Y i omega) hw,
    actual_zero_noise_regularized_kernel_posterior_has_the_squared_norm_band
      kernel hkernel lambda hlambda (fun i => query i omega) f B hf (fun i => Y i omega) hw⟩

/-- The actual simultaneous posterior event has probability one, including
arbitrary repeated outcome-dependent queries and zero observations. -/
theorem actual_zero_noise_alltime_kernel_posterior_event_has_probability_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → Ω → X) (f : H)
    (B : ℝ) (hf : ‖f‖ ^ 2 ≤ B) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0) :
    μ {omega | (∀ i, Y i omega = 0) ∧
      (∀ n, actualKernelNoiseQuadratic kernel lambda (fun i => query i omega) (fun i => Y i omega) n = 0) ∧
      ∀ n x,
        |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y)
          (fun i => Y i omega) n x| ≤
        Real.sqrt B * Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} = 1 := by
  have ha := actual_zero_width_noise_support_gives_one_common_alltime_kernel_posterior_event
    μ kernel hkernel lambda hlambda query f B hf Y hY
  calc
    _ = μ univ := measure_congr (by
      filter_upwards [ha] with omega hw
      exact propext (iff_true_intro hw))
    _ = 1 := measure_univ

end SafeLearning.CompleteModulesLandscapeZeroNoisePosterior
