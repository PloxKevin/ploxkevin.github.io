import SafeLearning.CompleteAppliedDensityScaling

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedIndependenceDefinitions
open MeasureTheory ProbabilityTheory Set
open SafeLearning.CompleteAppliedDensityScaling
open scoped ENNReal NNReal Function

variable {Omega Value Other : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Value] [MeasurableSpace Other]

theorem actual_independence_is_factorization_of_every_measurable_pair_of_events
    (measure : Measure Omega) (first : Omega → Value) (second : Omega → Other) :
    IndepFun first second measure ↔ ∀ left right,MeasurableSet left → MeasurableSet right →
      measure (first ⁻¹' left ∩ second ⁻¹' right)=
        measure (first ⁻¹' left)*measure (second ⁻¹' right) :=
  indepFun_iff_measure_inter_preimage_eq_mul

theorem actual_independence_is_the_true_joint_law_product
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (first : Omega → Value) (second : Omega → Other)
    (hfirst : Measurable first) (hsecond : Measurable second) :
    IndepFun first second measure ↔
      measure.map (fun outcome => (first outcome,second outcome))=
        (measure.map first).prod (measure.map second) :=
  indepFun_iff_map_prod_eq_prod_map_map hfirst.aemeasurable hsecond.aemeasurable

def actualIsIID (sample : ℕ → Omega → Value) (law : Measure Value)
    (measure : Measure Omega) : Prop :=
  iIndepFun sample measure ∧ ∀ index,HasLaw (sample index) law measure

theorem actual_independent_transform_products_are_integrable_and_factorize_expectation
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (first : Omega → Value) (second : Omega → Other)
    (hindependent : IndepFun first second measure)
    (left : Value → ℝ) (right : Other → ℝ)
    (hleft : Measurable left) (hright : Measurable right)
    (hileft : Integrable (left ∘ first) measure)
    (hiright : Integrable (right ∘ second) measure) :
    Integrable (fun outcome => left (first outcome)*right (second outcome)) measure ∧
      (∫ outcome,left (first outcome)*right (second outcome) ∂measure)=
        (∫ outcome,left (first outcome) ∂measure)*
          (∫ outcome,right (second outcome) ∂measure) := by
  have h := hindependent.comp hleft hright
  exact ⟨h.integrable_mul hileft hiright,
    h.integral_fun_mul_eq_mul_integral hileft.aestronglyMeasurable hiright.aestronglyMeasurable⟩

theorem actual_independent_square_integrable_quantities_have_zero_covariance_and_additive_variance
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (first second : Omega → ℝ) (hfirst : MemLp first 2 measure)
    (hsecond : MemLp second 2 measure) (hindependent : IndepFun first second measure) :
    covariance first second measure=0 ∧
      variance (fun outcome => first outcome+second outcome) measure=
        variance first measure+variance second measure := by
  exact ⟨hindependent.covariance_eq_zero hfirst hsecond,
    hindependent.variance_add hfirst hsecond⟩

theorem actual_independent_density_laws_have_the_true_product_density
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (first second : Omega → ℝ) (hfirst : Measurable first) (hsecond : Measurable second)
    (hindependent : IndepFun first second measure)
    (left right : ℝ → ℝ) (hleft : Measurable left) (hright : Measurable right)
    (hlaw : measure.map first=actualDensityLaw left)
    (hrlaw : measure.map second=actualDensityLaw right)
    (hnonnegative : ∀ x,0 ≤ left x) :
    measure.map (fun outcome => (first outcome,second outcome))=
      (volume.prod volume).withDensity (fun pair : ℝ × ℝ =>
        ENNReal.ofReal (left pair.1*right pair.2)) := by
  rw [hindependent.map_prod_eq_prod_map_map hfirst.aemeasurable hsecond.aemeasurable,
    hlaw,hrlaw,actualDensityLaw,actualDensityLaw,
    prod_withDensity hleft.ennreal_ofReal hright.ennreal_ofReal]
  congr 1
  funext pair
  exact (ENNReal.ofReal_mul (hnonnegative _)).symm

def actualGaussianNoiseLaw (variance : ℝ≥0) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ => gaussianReal 0 variance)

def actualNoiseCoordinate (index : ℕ) (outcome : ℕ → ℝ) : ℝ := outcome index

theorem actual_gaussian_noise_coordinates_are_mutually_independent_with_the_same_true_law
    (variance : ℝ≥0) :
    iIndepFun actualNoiseCoordinate (actualGaussianNoiseLaw variance) ∧
      ∀ index,HasLaw (actualNoiseCoordinate index) (gaussianReal 0 variance)
        (actualGaussianNoiseLaw variance) := by
  constructor
  · exact iIndepFun_infinitePi (fun _ => measurable_id)
  · intro index
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 variance) index).hasLaw

theorem actual_constructed_gaussian_noise_is_iid (variance : ℝ≥0) :
    actualIsIID actualNoiseCoordinate (gaussianReal 0 variance) (actualGaussianNoiseLaw variance) :=
  actual_gaussian_noise_coordinates_are_mutually_independent_with_the_same_true_law variance

def actualFixedFunctionObservation (function : Value → ℝ) (queries : ℕ → Value)
    (index : ℕ) (outcome : ℕ → ℝ) : ℝ :=
  function (queries index)+actualNoiseCoordinate index outcome

omit [MeasurableSpace Value] in
theorem actual_fixed_function_observation_noise_is_the_true_iid_coordinate
    (function : Value → ℝ) (queries : ℕ → Value) (index : ℕ) (outcome : ℕ → ℝ) :
    actualFixedFunctionObservation function queries index outcome-function (queries index)=
      actualNoiseCoordinate index outcome := by
  unfold actualFixedFunctionObservation
  ring

end SafeLearning.CompleteAppliedIndependenceDefinitions
