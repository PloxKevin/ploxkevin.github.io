import SafeLearning.CompleteAppliedProbability
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTailBounds
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem actual_markov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hi : Integrable X μ) (hn : ∀ᵐ omega ∂μ,0≤X omega)
    (epsilon : ℝ) (he : 0<epsilon) :
    μ.real {omega | epsilon≤X omega}≤(∫ omega,X omega ∂μ)/epsilon := by
  have hh := mul_meas_ge_le_integral_of_nonneg hn hi epsilon
  exact (le_div_iff₀ he).mpr (by simpa [mul_comm] using hh)

theorem source_markov_two_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hi : Integrable X μ) (hn : ∀ᵐ omega ∂μ,0≤X omega)
    (hmean : (∫ omega,X omega ∂μ)=2) :
    μ.real {omega | 8≤X omega}≤1/4 ∧
    μ.real {omega | 1≤X omega}≤2 ∧
    μ.real {omega | 1≤X omega}≤1 := by
  have h8 := actual_markov μ X hi hn 8 (by norm_num)
  have h1 := actual_markov μ X hi hn 1 (by norm_num)
  rw [hmean] at h8 h1
  norm_num at h8 h1
  exact ⟨h8,h1,measureReal_le_one⟩

theorem threshold_one_bound_sharp :
    (∫ x : ℝ,x ∂Measure.dirac 2)=2 ∧
    (∀ᵐ x : ℝ ∂Measure.dirac 2,0≤x) ∧
    (Measure.dirac (2:ℝ)).real {x | 1≤x}=1 ∧
    (Measure.dirac (2:ℝ)).real {x | 8≤x}=0 := by
  norm_num [measureReal_def,ae_dirac_eq,Set.indicator]

end SafeLearning.CompleteAppliedTailBounds
