import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeContinuousMixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]

/-- The actual Bochner integral of a parameterized real-valued process. -/
def mixture (ν : Measure Θ) (M : Θ → ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  ∫ theta, M theta n omega ∂ν

/-- Joint measurability in the filtration and the parameter gives adaptedness of the integral. -/
theorem mixture_stronglyAdapted (ν : Measure Θ) [SFinite ν]
    (F : Filtration ℕ mΩ) (M : Θ → ℕ → Ω → ℝ)
    (hjoint : ∀ n, StronglyMeasurable[(F n).prod mΘ]
      (fun p : Ω × Θ => M p.2 n p.1)) :
    StronglyAdapted F (mixture ν M) := by
  intro n
  exact (hjoint n).integral_prod_right'

/-- Product integrability gives integrability of the mixed process. -/
theorem mixture_integrable (μ : Measure Ω) (ν : Measure Θ) [SFinite ν]
    (M : Θ → ℕ → Ω → ℝ)
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν))
    (n : ℕ) :
    Integrable (mixture ν M n) μ := by
  exact (hprod n).integral_prod_left

/-- Fubini on a restricted sample-space measure, using actual product integrability. -/
theorem mixture_setIntegral_eq (μ : Measure Ω) [SFinite μ]
    (ν : Measure Θ) [SFinite ν] (M : Θ → ℕ → Ω → ℝ)
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν))
    (n : ℕ) (s : Set Ω) :
    (∫ omega in s, mixture ν M n omega ∂μ) =
      ∫ theta, (∫ omega in s, M theta n omega ∂μ) ∂ν := by
  have hi : Integrable (fun p : Ω × Θ => M p.2 n p.1) ((μ.restrict s).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hprod n).integrableOn
  exact integral_integral_swap hi

/-- Integrating a genuinely jointly measurable, product-integrable family of supermartingales
    yields a supermartingale; no supermartingale property of the mixture is assumed. -/
theorem mixture_supermartingale (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure Θ) [SFinite ν] (F : Filtration ℕ mΩ) (M : Θ → ℕ → Ω → ℝ)
    (hM : ∀ theta, Supermartingale (M theta) F μ)
    (hjoint : ∀ n, StronglyMeasurable[(F n).prod mΘ]
      (fun p : Ω × Θ => M p.2 n p.1))
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν)) :
    Supermartingale (mixture ν M) F μ := by
  apply supermartingale_of_setIntegral_succ_le
    (mixture_stronglyAdapted ν F M hjoint) (mixture_integrable μ ν M hprod)
  intro n s hs
  rw [mixture_setIntegral_eq μ ν M hprod (n + 1) s,
    mixture_setIntegral_eq μ ν M hprod n s]
  have hi (j : ℕ) :
      Integrable (fun p : Ω × Θ => M p.2 j p.1) ((μ.restrict s).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hprod j).integrableOn
  exact integral_mono (hi (n + 1)).integral_prod_right (hi n).integral_prod_right
    (fun theta => (hM theta).setIntegral_le (Nat.le_succ n) hs)

/-- Pointwise nonnegativity is preserved by the actual parameter integral. -/
theorem mixture_nonnegative (ν : Measure Θ) (M : Θ → ℕ → Ω → ℝ)
    (hM : ∀ theta n omega, 0 ≤ M theta n omega) (n : ℕ) (omega : Ω) :
    0 ≤ mixture ν M n omega := by
  exact integral_nonneg (fun theta => hM theta n omega)

/-- A probability mixture of processes starting at one also starts at one. -/
theorem mixture_initial_one (ν : Measure Θ) [IsProbabilityMeasure ν]
    (M : Θ → ℕ → Ω → ℝ) (hM : ∀ theta omega, M theta 0 omega = 1) (omega : Ω) :
    mixture ν M 0 omega = 1 := by
  simp [mixture, hM]

end SafeLearning.CompleteModulesLandscapeContinuousMixture
