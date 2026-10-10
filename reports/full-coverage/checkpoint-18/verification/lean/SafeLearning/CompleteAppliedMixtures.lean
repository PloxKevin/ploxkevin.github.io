import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedMixtures
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Choose either component law with equal probability. The component laws can
be arbitrary probability measures; no Gaussian shape is imposed. -/
def halfMixture {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : Measure Ω :=
  (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν

instance halfMixture_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (halfMixture μ ν) := by
  constructor
  simp [halfMixture,Measure.add_apply,Measure.smul_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv]
  norm_num

theorem half_mixture_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (X : Ω → ℝ) (hμ : Integrable X μ) (hν : Integrable X ν) :
    (∫ omega, X omega ∂halfMixture μ ν)=
      (1/2)*(∫ omega,X omega ∂μ)+(1/2)*(∫ omega,X omega ∂ν) := by
  rw [halfMixture,integral_add_measure
    (hμ.smul_measure (by norm_num)) (hν.smul_measure (by norm_num))]
  simp [integral_smul_measure,smul_eq_mul]

theorem half_mixture_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (X : Ω → ℝ) (hμ : MemLp X 2 μ) (hν : MemLp X 2 ν) :
    MemLp X 2 (halfMixture μ ν) := by
  have hμ' := hμ.smul_measure (by norm_num : (1/2 : ℝ≥0∞)≠∞)
  have hν' := hν.smul_measure (by norm_num : (1/2 : ℝ≥0∞)≠∞)
  exact (memLp_two_iff_integrable_sq
    (hμ'.aestronglyMeasurable.add_measure hν'.aestronglyMeasurable)).mpr
      (hμ'.integrable_sq.add_measure hν'.integrable_sq)

theorem half_mixture_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hμ : MemLp X 2 μ) (hν : MemLp X 2 ν) (a b : ℝ)
    (ha : (∫ omega,X omega ∂μ)=a) (hb : (∫ omega,X omega ∂ν)=b) :
    (∫ omega,X omega ∂halfMixture μ ν)=(a+b)/2 := by
  rw [half_mixture_integral μ ν X (hμ.integrable (by norm_num))
    (hν.integrable (by norm_num)),ha,hb]
  ring

theorem half_mixture_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hμ : MemLp X 2 μ) (hν : MemLp X 2 ν) (a b : ℝ)
    (ha : (∫ omega,X omega ∂μ)=a) (hb : (∫ omega,X omega ∂ν)=b) :
    variance X (halfMixture μ ν)=
      (variance X μ+variance X ν)/2+(a-b)^2/4 := by
  rw [variance_eq_sub (half_mixture_memLp μ ν X hμ hν),
    half_mixture_mean μ ν X hμ hν a b ha hb]
  have hsq := half_mixture_integral μ ν (fun omega => (X omega)^2)
    hμ.integrable_sq hν.integrable_sq
  change (∫ omega, (X omega)^2 ∂halfMixture μ ν)=_ at hsq
  simp only [Pi.pow_apply]
  rw [hsq,variance_eq_sub hμ,variance_eq_sub hν,ha,hb]
  simp only [Pi.pow_apply]
  ring

theorem disagreement_variance_five {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hμ : MemLp X 2 μ) (hν : MemLp X 2 ν)
    (ha : (∫ omega,X omega ∂μ)=0) (hb : (∫ omega,X omega ∂ν)=4)
    (hvμ : variance X μ=1) (hvν : variance X ν=1) :
    (∫ omega,X omega ∂halfMixture μ ν)=2 ∧
    variance X (halfMixture μ ν)=5 ∧ (0-2:ℝ)^2/2+(4-2)^2/2=4 := by
  rw [half_mixture_mean μ ν X hμ hν 0 4 ha hb,
    half_mixture_variance μ ν X hμ hν 0 4 ha hb,hvμ,hvν]
  norm_num

theorem ensemble_variance_two {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hμ : MemLp X 2 μ) (hν : MemLp X 2 ν)
    (ha : (∫ omega,X omega ∂μ)=0) (hb : (∫ omega,X omega ∂ν)=2)
    (hvμ : variance X μ=1) (hvν : variance X ν=1) :
    (∫ omega,X omega ∂halfMixture μ ν)=1 ∧ variance X (halfMixture μ ν)=2 := by
  rw [half_mixture_mean μ ν X hμ hν 0 2 ha hb,
    half_mixture_variance μ ν X hμ hν 0 2 ha hb,hvμ,hvν]
  norm_num

def optimisticEnvironment : Fin 2 → ℝ := ![1,100]
def pessimisticEnvironment : Fin 2 → ℝ := ![1,-100]

theorem unsupported_action_counterexample :
    optimisticEnvironment 0=pessimisticEnvironment 0 ∧
    optimisticEnvironment 0=1 ∧ optimisticEnvironment 1=100 ∧
    pessimisticEnvironment 1=-100 ∧ optimisticEnvironment≠pessimisticEnvironment := by
  norm_num [optimisticEnvironment,pessimisticEnvironment]

end SafeLearning.CompleteAppliedMixtures
