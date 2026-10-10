import SafeLearning.CompleteModulesLandscapeContinuousMixture
import SafeLearning.CompleteAppliedStopping

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeMixtureVille
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
open CompleteModulesLandscapeContinuousMixture

variable {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]

/-- Actual Ville's inequality for the derived continuous-mixture supermartingale. -/
theorem mixture_ville (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure Θ) [SFinite ν] (F : Filtration ℕ mΩ) (M : Θ → ℕ → Ω → ℝ)
    (hM : ∀ theta, Supermartingale (M theta) F μ)
    (hjoint : ∀ n, StronglyMeasurable[(F n).prod mΘ]
      (fun p : Ω × Θ => M p.2 n p.1))
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν))
    (hnonneg : ∀ theta n omega, 0 ≤ M theta n omega) (c : ℝ) (hc : 0 < c) :
    μ.real {omega | ∃ n, c ≤ mixture ν M n omega} ≤
      (∫ omega, mixture ν M 0 omega ∂μ) / c := by
  exact CompleteAppliedStopping.ville μ F (mixture ν M)
    (mixture_supermartingale μ ν F M hM hjoint hprod)
    (fun n => Eventually.of_forall fun omega => mixture_nonnegative ν M hnonneg n omega) c hc

/-- A probability mixture starting at one has a genuine all-time crossing bound. -/
theorem mixture_all_time_crossing_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (F : Filtration ℕ mΩ) (M : Θ → ℕ → Ω → ℝ)
    (hM : ∀ theta, Supermartingale (M theta) F μ)
    (hjoint : ∀ n, StronglyMeasurable[(F n).prod mΘ]
      (fun p : Ω × Θ => M p.2 n p.1))
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν))
    (hnonneg : ∀ theta n omega, 0 ≤ M theta n omega)
    (hinit : ∀ theta omega, M theta 0 omega = 1) (delta : ℝ) (hd : 0 < delta) :
    μ.real {omega | ∃ n, 1 / delta ≤ mixture ν M n omega} ≤ delta := by
  have hv := mixture_ville μ ν F M hM hjoint hprod hnonneg (1 / delta) (by positivity)
  have hi : (∫ omega, mixture ν M 0 omega ∂μ) = 1 := by
    have hm : mixture ν M 0 = fun _ => 1 := by
      funext omega
      exact mixture_initial_one ν M hinit omega
    rw [hm]
    simp
  rw [hi] at hv
  simpa using hv

/-- The common all-time event is derived as a measurable complement of the actual crossing set. -/
theorem mixture_simultaneous_confidence_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (F : Filtration ℕ mΩ) (M : Θ → ℕ → Ω → ℝ)
    (hM : ∀ theta, Supermartingale (M theta) F μ)
    (hjoint : ∀ n, StronglyMeasurable[(F n).prod mΘ]
      (fun p : Ω × Θ => M p.2 n p.1))
    (hprod : ∀ n, Integrable (fun p : Ω × Θ => M p.2 n p.1) (μ.prod ν))
    (hnonneg : ∀ theta n omega, 0 ≤ M theta n omega)
    (hinit : ∀ theta omega, M theta 0 omega = 1) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n, mixture ν M n omega < 1 / delta} := by
  let bad : Set Ω := {omega | ∃ n, 1 / delta ≤ mixture ν M n omega}
  have hbad : MeasurableSet bad := by
    have heq : bad = ⋃ n, {omega | 1 / delta ≤ mixture ν M n omega} := by
      ext omega
      simp [bad]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_le measurable_const
      (((mixture_stronglyAdapted ν F M hjoint) n).mono (F.le n)).measurable
  have hv := mixture_all_time_crossing_probability μ ν F M hM hjoint hprod hnonneg hinit delta hd
  have heq : {omega | ∀ n, mixture ν M n omega < 1 / delta} = badᶜ := by
    ext omega
    simp [bad, not_le]
  rw [heq, measureReal_compl hbad, probReal_univ]
  change μ.real bad ≤ delta at hv
  linarith

end SafeLearning.CompleteModulesLandscapeMixtureVille
