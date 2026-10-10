import SafeLearning.CompleteAppliedCalibrationRepeatedJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteAppliedCalibrationGeneralRepeated
open CompleteAppliedCalibrationIndependentExtension
open CompleteAppliedCalibrationRepeatedJoint
open CompleteAppliedCalibrationAverages

def coordinateLaw (n : ℕ) (noise : Fin n→Measure ℝ) : Option (Fin n)→Measure ℝ
  | none=>gaussianReal 0 (2/3)
  | some i=>noise i

instance coordinateLaw_probability (n : ℕ) (noise : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (noise i)] (i : Option (Fin n)) :
    IsProbabilityMeasure (coordinateLaw n noise i) := by
  cases i <;> unfold coordinateLaw <;> infer_instance

theorem actual_centered_coordinates_are_the_literal_offset_and_fresh_readings
    (n : ℕ) (pair : ℝ×(Fin n→ℝ)) :
    centeredFamily n pair none=pair.1-7/6 ∧
    (∀i:Fin n,centeredFamily n pair (some i)=pair.2 i) := by
  exact ⟨rfl,fun _=>rfl⟩

theorem actual_arbitrary_fresh_noise_product_retains_the_true_conditional_offset
    (n : ℕ) (noise : Fin n→Measure ℝ) [∀i,IsProbabilityMeasure (noise i)] :
    HasLaw (centeredFamily n) (Measure.pi (coordinateLaw n noise))
      (extendedPosteriorKernel (Measure.pi noise) (2,-1)) := by
  refine ⟨(show Measurable (centeredFamily n) by unfold centeredFamily;fun_prop).aemeasurable,?_⟩
  rw [actual_observed_calibration_preserves_the_entire_independent_data_law]
  have hshift : ((gaussianReal (7/6) (2/3)).prod (Measure.pi noise)).map
      (fun pair:ℝ×(Fin n→ℝ)=>(pair.1-7/6,pair.2))=
      (gaussianReal 0 (2/3)).prod (Measure.pi noise) := by
    have h := Measure.map_prod_map (gaussianReal (7/6) (2/3)) (Measure.pi noise)
      (show Measurable (fun latent:ℝ=>latent-7/6) by fun_prop) measurable_id
    rw [CompleteAppliedSequentialCalibration.actual_offset_correction_has_zero_mean_gaussian_error,
      Measure.map_id] at h
    convert h.symm using 1
    ext pair
    rfl
  have hswap : ((gaussianReal 0 (2/3)).prod (Measure.pi noise)).map Prod.swap=
      (Measure.pi noise).prod (gaussianReal 0 (2/3)) := Measure.prod_swap
  have hpi := Measure.pi_map_piOptionEquivProd (coordinateLaw n noise)
  change (((gaussianReal (7/6) (2/3)).prod (Measure.pi noise)).map
    ((MeasurableEquiv.piOptionEquivProd (fun _:Option (Fin n)=>ℝ)).symm ∘
      Prod.swap ∘ (fun pair:ℝ×(Fin n→ℝ)=>(pair.1-7/6,pair.2))))=_
  rw [←Measure.map_map (by fun_prop) (by fun_prop),
    ←Measure.map_map measurable_swap (by fun_prop),hshift,hswap]
  exact hpi

theorem actual_arbitrary_conditioned_noise_coordinates_are_independent
    (n : ℕ) (noise : Fin n→Measure ℝ) [∀i,IsProbabilityMeasure (noise i)] :
    (∀i,HasLaw (fun pair=>centeredFamily n pair i) (coordinateLaw n noise i)
      (extendedPosteriorKernel (Measure.pi noise) (2,-1))) ∧
    iIndepFun (fun i pair=>centeredFamily n pair i)
      (extendedPosteriorKernel (Measure.pi noise) (2,-1)) := by
  have hfamily := actual_arbitrary_fresh_noise_product_retains_the_true_conditional_offset n noise
  have hcoordinates : ∀i,HasLaw (fun pair=>centeredFamily n pair i)
      (coordinateLaw n noise i) (extendedPosteriorKernel (Measure.pi noise) (2,-1)) :=
    fun i=>(measurePreserving_eval (coordinateLaw n noise) i).hasLaw.comp hfamily
  exact ⟨hcoordinates,(iIndepFun_iff_hasLaw_pi_pi hcoordinates).mpr hfamily⟩

theorem actual_average_formula_contains_only_one_shared_offset
    (n : ℕ) :
    averageError n (fun i pair=>centeredFamily n pair i)=
      (fun pair:ℝ×(Fin n→ℝ)=>pair.1-7/6+(n:ℝ)⁻¹*∑i:Fin n,pair.2 i) := by
  funext pair
  have hc := actual_centered_coordinates_are_the_literal_offset_and_fresh_readings n pair
  simp only [averageError,hc.1,hc.2]

theorem actual_arbitrary_square_integrable_unit_variance_noises_have_the_source_average_variance
    (n : ℕ) (hn : 0<n) (noise : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (noise i)]
    (hL2noise : ∀i,MemLp (id:ℝ→ℝ) 2 (noise i))
    (hvariance : ∀i,Var[(id:ℝ→ℝ);noise i]=1) :
    Var[(fun pair:ℝ×(Fin n→ℝ)=>pair.1-7/6+(n:ℝ)⁻¹*∑i:Fin n,pair.2 i);
      extendedPosteriorKernel (Measure.pi noise) (2,-1)]=2/3+1/(n:ℝ) ∧
    (∀i j:Fin n,i≠j→covariance
      (fun pair:ℝ×(Fin n→ℝ)=>pair.1-7/6+pair.2 i)
      (fun pair:ℝ×(Fin n→ℝ)=>pair.1-7/6+pair.2 j)
      (extendedPosteriorKernel (Measure.pi noise) (2,-1))=2/3) := by
  have hc := actual_arbitrary_conditioned_noise_coordinates_are_independent n noise
  have hL2 : ∀i,MemLp (fun pair=>centeredFamily n pair i) 2
      (extendedPosteriorKernel (Measure.pi noise) (2,-1)) := by
    intro i
    cases i with
    | none=>exact (hc.1 none).memLp (memLp_id_gaussianReal 2)
    | some i=>exact (hc.1 (some i)).memLp (hL2noise i)
  have ho : Var[(fun pair=>centeredFamily n pair none);
      extendedPosteriorKernel (Measure.pi noise) (2,-1)]=2/3 := by
    rw [(hc.1 none).variance_eq]
    exact variance_id_gaussianReal
  have he : ∀i:Fin n,Var[(fun pair=>centeredFamily n pair (some i));
      extendedPosteriorKernel (Measure.pi noise) (2,-1)]=1 := by
    intro i
    rw [(hc.1 (some i)).variance_eq]
    exact hvariance i
  have havg := actual_independent_noise_average_has_the_derived_variance_floor n hn _ hL2 hc.2 ho he
  rw [actual_average_formula_contains_only_one_shared_offset] at havg
  refine ⟨havg,?_⟩
  intro i j hij
  exact actual_distinct_reading_errors_have_the_shared_offset_covariance n _ hL2 hc.2 ho i j hij

end SafeLearning.CompleteAppliedCalibrationGeneralRepeated
