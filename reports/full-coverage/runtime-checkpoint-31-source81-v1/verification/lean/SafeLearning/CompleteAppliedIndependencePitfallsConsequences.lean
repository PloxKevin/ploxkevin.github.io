import SafeLearning.CompleteAppliedIndependencePitfalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedIndependencePitfallsConsequences
open CompleteAppliedIndependenceDefinitions CompleteAppliedIndependencePitfalls

theorem actual_zero_control_states_are_the_literal_shared_noise_sums (noise : ℕ → ℝ) :
    episodeTrajectory (fun _ => 0) (0,noise) 1=noise 0 ∧
      episodeTrajectory (fun _ => 0) (0,noise) 2=noise 0+noise 1 := by
  simp [episodeTrajectory]

theorem actual_positive_variance_zero_control_episode_has_dependent_first_two_states
    (variance : ℝ≥0) (hv : 0<variance) :
    ¬IndepFun
      (fun noise => episodeTrajectory (fun _ => 0) (0,noise) 1)
      (fun noise => episodeTrajectory (fun _ => 0) (0,noise) 2)
      (actualGaussianNoiseLaw variance) := by
  have h1 : (fun noise => episodeTrajectory (fun _ => 0) (0,noise) 1)=
      actualNoiseCoordinate 0 := by
    funext noise
    simp [episodeTrajectory,actualNoiseCoordinate]
  have h2 : (fun noise => episodeTrajectory (fun _ => 0) (0,noise) 2)=
      (fun sample => actualNoiseCoordinate 0 sample+actualNoiseCoordinate 1 sample) := by
    funext noise
    simp [episodeTrajectory,actualNoiseCoordinate]
  rw [h1,h2]
  exact (actual_same_episode_states_share_noise_and_are_dependent_for_positive_gaussian_variance
    variance hv).2

theorem actual_zero_noise_fixed_initial_trajectory_is_constant_and_its_states_are_independent
    (variance : ℝ≥0) :
    (∀ n,episodeTrajectory (fun _ => 0) (0,fun _ => 0) n=0) ∧
      ∀ i j,IndepFun
        (fun _ : ℕ → ℝ => episodeTrajectory (fun _ => 0) (0,fun _ => 0) i)
        (fun _ : ℕ → ℝ => episodeTrajectory (fun _ => 0) (0,fun _ => 0) j)
        (actualGaussianNoiseLaw variance) := by
  have hzero : ∀ n,episodeTrajectory (fun _ => 0) (0,fun _ => 0) n=0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n hn => simp [episodeTrajectory,hn]
  refine ⟨hzero,?_⟩
  intro i j
  simp only [hzero]
  letI : IsProbabilityMeasure (actualGaussianNoiseLaw variance) := by
    unfold actualGaussianNoiseLaw
    infer_instance
  exact indepFun_const_left 0 (fun _ => 0)

theorem actual_nonzero_gaussian_initial_coordinate_is_not_independent_of_itself
    (variance : ℝ≥0) (hv : 0<variance) :
    ¬IndepFun (actualNoiseCoordinate 0) (actualNoiseCoordinate 0)
      (actualGaussianNoiseLaw variance) := by
  letI : IsProbabilityMeasure (actualGaussianNoiseLaw variance) := by
    unfold actualGaussianNoiseLaw
    infer_instance
  obtain ⟨_,hlaw⟩ := actual_gaussian_noise_coordinates_are_mutually_independent_with_the_same_true_law variance
  have hm : MemLp (actualNoiseCoordinate 0) 2 (actualGaussianNoiseLaw variance) :=
    (hlaw 0).memLp (memLp_id_gaussianReal 2)
  intro h
  have hz := h.covariance_eq_zero hm hm
  rw [covariance_self (hlaw 0).aemeasurable,(hlaw 0).variance_eq,variance_id_gaussianReal] at hz
  exact (ne_of_gt (show 0<(variance:ℝ) from hv)) hz

theorem actual_shared_random_controller_creates_dependent_episode_states
    (variance : ℝ≥0) (hv : 0<variance) :
    ¬IndepFun
      (fun sample => episodeTrajectory (fun _ => actualNoiseCoordinate 0 sample)
        (0,fun _ => 0) 1)
      (fun sample => episodeTrajectory (fun _ => actualNoiseCoordinate 0 sample)
        (0,fun _ => 0) 1)
      (actualGaussianNoiseLaw variance) := by
  simpa only [episodeTrajectory,zero_add,add_zero] using
    actual_nonzero_gaussian_initial_coordinate_is_not_independent_of_itself variance hv

theorem actual_controller_updated_from_a_previous_episode_can_make_the_next_episode_dependent
    (variance : ℝ≥0) (hv : 0<variance) :
    ¬IndepFun
      (fun sample => episodeTrajectory (fun _ => 0) (0,sample) 1)
      (fun sample => episodeTrajectory
        (fun _ => episodeTrajectory (fun _ => 0) (0,sample) 1)
        (0,fun _ => 0) 1)
      (actualGaussianNoiseLaw variance) := by
  have h1 : (fun sample => episodeTrajectory (fun _ => 0) (0,sample) 1)=
      actualNoiseCoordinate 0 := by
    funext sample
    simp [episodeTrajectory,actualNoiseCoordinate]
  have h2 : (fun sample => episodeTrajectory
      (fun _ => episodeTrajectory (fun _ => 0) (0,sample) 1) (0,fun _ => 0) 1)=
      actualNoiseCoordinate 0 := by
    funext sample
    simp [episodeTrajectory,actualNoiseCoordinate]
  rw [h1,h2]
  exact actual_nonzero_gaussian_initial_coordinate_is_not_independent_of_itself variance hv

end SafeLearning.CompleteAppliedIndependencePitfallsConsequences
