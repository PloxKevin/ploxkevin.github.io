import SafeLearning.CompleteAppliedCalibrationIndependentExtension
import SafeLearning.CompleteAppliedCalibrationAverages

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteAppliedCalibrationRepeatedJoint
open CompleteAppliedCalibrationIndependentExtension
open CompleteAppliedCalibrationAverages

def freshNoiseLaw (n : ℕ) : Measure (Fin n→ℝ) :=
  Measure.pi (fun _=>gaussianReal 0 1)

def centeredCoordinateLaw (n : ℕ) : Option (Fin n)→Measure ℝ
  | none=>gaussianReal 0 (2/3)
  | some _=>gaussianReal 0 1

instance freshNoiseLaw_probability (n : ℕ) : IsProbabilityMeasure (freshNoiseLaw n) := by
  unfold freshNoiseLaw;infer_instance

instance centeredCoordinateLaw_probability (n : ℕ) (i : Option (Fin n)) :
    IsProbabilityMeasure (centeredCoordinateLaw n i) := by
  cases i <;> unfold centeredCoordinateLaw <;> infer_instance

def centeredFamily (n : ℕ) (pair : ℝ×(Fin n→ℝ)) : Option (Fin n)→ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _:Option (Fin n)=>ℝ)).symm
    (pair.2,pair.1-7/6)

theorem actual_observed_calibration_and_all_fresh_noises_have_the_product_posterior
    (n : ℕ) :
    extendedPosteriorKernel (freshNoiseLaw n) (2,-1)=
      (gaussianReal (7/6) (2/3)).prod (freshNoiseLaw n) :=
  actual_observed_calibration_preserves_the_entire_independent_data_law _

theorem actual_centered_shared_offset_and_fresh_noises_have_the_derived_pi_law
    (n : ℕ) :
    HasLaw (centeredFamily n) (Measure.pi (centeredCoordinateLaw n))
      (extendedPosteriorKernel (freshNoiseLaw n) (2,-1)) := by
  refine ⟨(show Measurable (centeredFamily n) by unfold centeredFamily;fun_prop).aemeasurable,?_⟩
  rw [actual_observed_calibration_and_all_fresh_noises_have_the_product_posterior]
  have hshift : ((gaussianReal (7/6) (2/3)).prod (freshNoiseLaw n)).map
      (fun pair:ℝ×(Fin n→ℝ)=>(pair.1-7/6,pair.2))=
      (gaussianReal 0 (2/3)).prod (freshNoiseLaw n) := by
    have h := Measure.map_prod_map (gaussianReal (7/6) (2/3)) (freshNoiseLaw n)
      (show Measurable (fun latent:ℝ=>latent-7/6) by fun_prop) measurable_id
    rw [CompleteAppliedSequentialCalibration.actual_offset_correction_has_zero_mean_gaussian_error,
      Measure.map_id] at h
    convert h.symm using 1
    ext pair
    rfl
  have hswap : ((gaussianReal 0 (2/3)).prod (freshNoiseLaw n)).map Prod.swap=
      (freshNoiseLaw n).prod (gaussianReal 0 (2/3)) := Measure.prod_swap
  have hpi := Measure.pi_map_piOptionEquivProd (centeredCoordinateLaw n)
  change (((gaussianReal (7/6) (2/3)).prod (freshNoiseLaw n)).map
    ((MeasurableEquiv.piOptionEquivProd (fun _:Option (Fin n)=>ℝ)).symm ∘
      Prod.swap ∘ (fun pair:ℝ×(Fin n→ℝ)=>(pair.1-7/6,pair.2))))=_
  rw [←Measure.map_map (by fun_prop) (by fun_prop),
    ←Measure.map_map measurable_swap (by fun_prop),hshift,hswap]
  exact hpi

theorem actual_conditioned_family_has_independent_gaussian_coordinates
    (n : ℕ) :
    (∀i,HasLaw (fun pair=>centeredFamily n pair i) (centeredCoordinateLaw n i)
      (extendedPosteriorKernel (freshNoiseLaw n) (2,-1))) ∧
    iIndepFun (fun i pair=>centeredFamily n pair i)
      (extendedPosteriorKernel (freshNoiseLaw n) (2,-1)) := by
  have hfamily := actual_centered_shared_offset_and_fresh_noises_have_the_derived_pi_law n
  have hcoordinates : ∀i,HasLaw (fun pair=>centeredFamily n pair i)
      (centeredCoordinateLaw n i) (extendedPosteriorKernel (freshNoiseLaw n) (2,-1)) :=
    fun i=>(measurePreserving_eval (centeredCoordinateLaw n) i).hasLaw.comp hfamily
  refine ⟨hcoordinates,(iIndepFun_iff_hasLaw_pi_pi hcoordinates).mpr ?_⟩
  exact hfamily

theorem actual_conditioned_average_variance_and_cross_reading_covariance
    (n : ℕ) (hn : 0<n) :
    Var[averageError n (fun i pair=>centeredFamily n pair i);
      extendedPosteriorKernel (freshNoiseLaw n) (2,-1)]=2/3+1/(n:ℝ) ∧
    (∀i j:Fin n,i≠j→covariance
      (fun pair=>centeredFamily n pair none+centeredFamily n pair (some i))
      (fun pair=>centeredFamily n pair none+centeredFamily n pair (some j))
      (extendedPosteriorKernel (freshNoiseLaw n) (2,-1))=2/3) := by
  have hc := actual_conditioned_family_has_independent_gaussian_coordinates n
  have hL2 : ∀i,MemLp (fun pair=>centeredFamily n pair i) 2
      (extendedPosteriorKernel (freshNoiseLaw n) (2,-1)) := by
    intro i
    cases i with
    | none=>exact (hc.1 none).memLp (memLp_id_gaussianReal 2)
    | some i=>exact (hc.1 (some i)).memLp (memLp_id_gaussianReal 2)
  have ho : Var[(fun pair=>centeredFamily n pair none);
      extendedPosteriorKernel (freshNoiseLaw n) (2,-1)]=2/3 := by
    rw [(hc.1 none).variance_eq]
    exact variance_id_gaussianReal
  have he : ∀i:Fin n,Var[(fun pair=>centeredFamily n pair (some i));
      extendedPosteriorKernel (freshNoiseLaw n) (2,-1)]=1 := by
    intro i
    rw [(hc.1 (some i)).variance_eq]
    exact variance_id_gaussianReal
  exact ⟨actual_independent_noise_average_has_the_derived_variance_floor n hn _ hL2 hc.2 ho he,
    fun i j hij=>actual_distinct_reading_errors_have_the_shared_offset_covariance n _ hL2 hc.2 ho i j hij⟩

end SafeLearning.CompleteAppliedCalibrationRepeatedJoint
