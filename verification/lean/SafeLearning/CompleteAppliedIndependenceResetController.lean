import SafeLearning.CompleteAppliedIndependencePitfalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteAppliedIndependenceResetController
open CompleteAppliedIndependenceDefinitions CompleteAppliedIndependencePitfalls

theorem actual_fixed_reset_controller_erases_every_previous_state
    (initial : ℝ) (noise : ℕ → ℝ) (n : ℕ) :
    episodeTrajectory (fun x => -x) (initial,noise) (n+1)=noise n := by
  simp [episodeTrajectory]

theorem actual_positive_gaussian_noise_reset_control_states_are_mutually_independent
    (initial : ℝ) (variance : ℝ≥0) :
    iIndepFun (fun n => fun noise => episodeTrajectory (fun x => -x) (initial,noise) (n+1))
      (actualGaussianNoiseLaw variance) := by
  have he : (fun n => fun noise => episodeTrajectory (fun x => -x) (initial,noise) (n+1))=
      actualNoiseCoordinate := by
    funext n noise
    simp [actual_fixed_reset_controller_erases_every_previous_state,actualNoiseCoordinate]
  rw [he]
  exact (actual_gaussian_noise_coordinates_are_mutually_independent_with_the_same_true_law variance).1

theorem actual_first_two_reset_control_states_are_independent_even_with_positive_gaussian_noise
    (initial : ℝ) (variance : ℝ≥0) :
    IndepFun
      (fun noise => episodeTrajectory (fun x => -x) (initial,noise) 1)
      (fun noise => episodeTrajectory (fun x => -x) (initial,noise) 2)
      (actualGaussianNoiseLaw variance) := by
  exact (actual_positive_gaussian_noise_reset_control_states_are_mutually_independent initial variance).indepFun
    (by norm_num : (0:ℕ)≠1)

end SafeLearning.CompleteAppliedIndependenceResetController
