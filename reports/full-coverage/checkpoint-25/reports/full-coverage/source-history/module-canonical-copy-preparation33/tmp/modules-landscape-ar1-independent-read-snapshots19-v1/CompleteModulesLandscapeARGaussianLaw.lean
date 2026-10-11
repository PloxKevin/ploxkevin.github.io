import SafeLearning.CompleteModulesLandscapeARGaussianAlgebra
import SafeLearning.CompleteModulesGaussianRectangularDesignLaws
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesLandscapeARGaussianLaw
open CompleteModulesLandscapeARGaussianAlgebra
open CompleteModulesGaussianMatrixLaws CompleteModulesGaussianRectangularDesignLaws

def noiseLaw (T : ℕ) : Measure (Fin T→ℝ) := Measure.pi (fun _=>gaussianReal 0 1)
instance (T : ℕ) : IsProbabilityMeasure (noiseLaw T) := by unfold noiseLaw;infer_instance

def vectorTrajectory (k goal sigma : ℝ) (T : ℕ) (w : Fin T→ℝ) : Fin (T+1)→ℝ :=
  fun t=>trajectory k goal sigma w t.val

def trajectoryLaw (k goal sigma : ℝ) (T : ℕ) : Measure (Fin (T+1)→ℝ) :=
  (noiseLaw T).map (vectorTrajectory k goal sigma T)

theorem actual_canonical_noises_are_independent_standard_gaussians (T : ℕ) :
    iIndepFun (fun j:Fin T=>fun w:Fin T→ℝ=>w j) (noiseLaw T) ∧
      ∀j:Fin T,HasLaw (fun w:Fin T→ℝ=>w j) (gaussianReal 0 1) (noiseLaw T) := by
  constructor
  · exact iIndepFun_pi (μ:=fun _ : Fin T=>gaussianReal 0 1)
      (X:=fun _=>id) (fun _=>measurable_id.aemeasurable)
  · intro j
    exact (measurePreserving_eval (fun _ : Fin T=>gaussianReal 0 1) j).hasLaw

theorem actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map
    (k goal sigma : ℝ) (T : ℕ) :
    vectorTrajectory k goal sigma T=
      (fun w=>(fun t:Fin (T+1)=>trueMean k goal t.val)+(design k sigma T)*ᵥw) := by
  funext w
  exact actual_finite_vector_trajectory_is_the_affine_matrix_map k goal sigma w

theorem actual_finite_trajectory_is_measurable (k goal sigma : ℝ) (T : ℕ) :
    Measurable (vectorTrajectory k goal sigma T) := by
  rw [actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map]
  exact measurable_const.add (designCLM (design k sigma T)).continuous.measurable

theorem actual_recursive_trajectory_has_a_genuine_joint_gaussian_law
    (k goal sigma : ℝ) (T : ℕ) :
    HasGaussianLaw (vectorTrajectory k goal sigma T) (noiseLaw T) := by
  have hg := actual_independent_standard_gaussian_parameter_law_provides_the_linear_kernel_prior_for_every_finite_design
    (design k sigma T)
  let m : Fin (T+1)→ℝ := fun t=>trueMean k goal t.val
  have hlinear : HasGaussianLaw (fun w:Fin T→ℝ=>(design k sigma T)*ᵥw) (noiseLaw T) := hg.1
  haveI := hlinear.isGaussian_map
  have hi : IsGaussian (((noiseLaw T).map (fun w:Fin T→ℝ=>(design k sigma T)*ᵥw)).map
      (fun z:Fin (T+1)→ℝ=>m+z)) := by infer_instance
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_const_add m).aemeasurable
    hlinear.aemeasurable] at hi
  rw [actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map]
  exact ⟨measurable_const.add (designCLM (design k sigma T)).continuous.measurable |>.aemeasurable,hi⟩

theorem actual_recursive_trajectory_law_is_normalized_and_gaussian
    (k goal sigma : ℝ) (T : ℕ) :
    IsProbabilityMeasure (trajectoryLaw k goal sigma T) ∧
      IsGaussian (trajectoryLaw k goal sigma T) := by
  have hg := actual_recursive_trajectory_has_a_genuine_joint_gaussian_law k goal sigma T
  haveI := hg.isGaussian_map
  unfold trajectoryLaw
  exact ⟨inferInstance,hg.isGaussian_map⟩

theorem actual_recursive_trajectory_coordinate_means_are_the_printed_means
    (k goal sigma : ℝ) (T : ℕ) (t : Fin (T+1)) :
    (∫w,(vectorTrajectory k goal sigma T w) t ∂noiseLaw T)=trueMean k goal t.val := by
  have hg := actual_independent_standard_gaussian_parameter_law_provides_the_linear_kernel_prior_for_every_finite_design
    (design k sigma T)
  have hi := (hg.1.eval t).integrable
  rw [actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map]
  change (∫w,trueMean k goal t.val+((design k sigma T)*ᵥw) t ∂noiseLaw T)=_
  unfold noiseLaw
  rw [integral_add (integrable_const _) hi]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change trueMean k goal t.val+(∫w,((design k sigma T)*ᵥw) t
    ∂Measure.pi (fun _ : Fin T=>gaussianReal 0 1))=_
  rw [hg.2.1 t,add_zero]

theorem actual_recursive_trajectory_covariance_is_the_affine_design_gram
    (k goal sigma : ℝ) (T : ℕ) (s t : Fin (T+1)) :
    cov[fun w=>(vectorTrajectory k goal sigma T w) s,
      fun w=>(vectorTrajectory k goal sigma T w) t;noiseLaw T]=
        ((design k sigma T)*(design k sigma T)ᵀ) s t := by
  have hg := actual_independent_standard_gaussian_parameter_law_provides_the_linear_kernel_prior_for_every_finite_design
    (design k sigma T)
  rw [actual_vector_trajectory_is_exactly_the_affine_finite_gaussian_noise_map]
  change cov[fun w=>trueMean k goal s.val+((design k sigma T)*ᵥw) s,
    fun w=>trueMean k goal t.val+((design k sigma T)*ᵥw) t;noiseLaw T]=_
  unfold noiseLaw
  rw [covariance_const_add_left (hg.1.eval s).integrable,
    covariance_const_add_right (hg.1.eval t).integrable]
  exact hg.2.2 s t

theorem actual_recursive_trajectory_has_the_printed_temporal_covariance
    (k goal sigma : ℝ) (T : ℕ) (s t : Fin (T+1)) (hst:s.val≤t.val) :
    cov[fun w=>(vectorTrajectory k goal sigma T w) s,
      fun w=>(vectorTrajectory k goal sigma T w) t;noiseLaw T]=
        (1-k)^(t.val-s.val)*trueVariance k sigma s.val := by
  rw [actual_recursive_trajectory_covariance_is_the_affine_design_gram]
  exact actual_affine_design_gram_is_the_true_temporal_covariance k sigma T s t hst

theorem actual_recursive_trajectory_has_the_printed_state_variance
    (k goal sigma : ℝ) (T : ℕ) (t : Fin (T+1)) :
    Var[fun w=>(vectorTrajectory k goal sigma T w) t;noiseLaw T]=trueVariance k sigma t.val := by
  have hg := actual_recursive_trajectory_has_a_genuine_joint_gaussian_law k goal sigma T
  rw [←covariance_self (hg.eval t).aemeasurable,
    actual_recursive_trajectory_has_the_printed_temporal_covariance k goal sigma T t t (le_refl _)]
  simp

theorem actual_every_state_has_the_true_scalar_gaussian_marginal
    (k goal sigma : ℝ) (T : ℕ) (t : Fin (T+1)) :
    (noiseLaw T).map (fun w=>(vectorTrajectory k goal sigma T w) t)=
      gaussianReal (trueMean k goal t.val) (trueVariance k sigma t.val).toNNReal := by
  have hg := actual_recursive_trajectory_has_a_genuine_joint_gaussian_law k goal sigma T
  rw [(hg.eval t).map_eq_gaussianReal,
    actual_recursive_trajectory_coordinate_means_are_the_printed_means,
    actual_recursive_trajectory_has_the_printed_state_variance]

theorem actual_zero_noise_has_the_entire_deterministic_trajectory_law
    (k goal : ℝ) (T : ℕ) :
    trajectoryLaw k goal 0 T=Measure.dirac (fun t:Fin (T+1)=>trueMean k goal t.val) := by
  have he : vectorTrajectory k goal 0 T=
      (fun _w:Fin T→ℝ=>fun t:Fin (T+1)=>trueMean k goal t.val) := by
    funext w t
    exact actual_zero_noise_scale_is_the_deterministic_mean_trajectory k goal w t.val
  simp [trajectoryLaw,he]

theorem actual_any_iid_standard_gaussian_noise_vector_generates_this_same_recursive_joint_law
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (k goal sigma : ℝ) (T : ℕ) (w : Omega→Fin T→ℝ)
    (hw : HasLaw w (noiseLaw T) P) :
    P.map (fun o=>vectorTrajectory k goal sigma T (w o))=trajectoryLaw k goal sigma T := by
  unfold trajectoryLaw
  rw [←hw.map_eq]
  exact (AEMeasurable.map_map_of_aemeasurable
    (actual_finite_trajectory_is_measurable k goal sigma T).aemeasurable hw.aemeasurable).symm

end SafeLearning.CompleteModulesLandscapeARGaussianLaw
