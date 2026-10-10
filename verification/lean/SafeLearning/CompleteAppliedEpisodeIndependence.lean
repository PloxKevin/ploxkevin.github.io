import SafeLearning.CompleteAppliedIndependencePitfalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteAppliedEpisodeIndependence
open CompleteAppliedIndependencePitfalls

variable {Episode Omega : Type*} [MeasurableSpace Omega]

theorem actual_arbitrary_independent_input_data_give_independent_whole_feedback_episodes
    (P : Measure Omega) (data : Episode → Omega → ℝ × (ℕ → ℝ))
    (hind : iIndepFun data P) (policy : ℝ → ℝ) (hp : Measurable policy) :
    iIndepFun (fun e o => episodeTrajectory policy (data e o)) P := by
  exact hind.comp (fun _ => episodeTrajectory policy)
    (fun _ => actual_fixed_controller_episode_trajectory_is_measurable policy hp)

theorem actual_arbitrary_episode_probability_laws_construct_independent_whole_feedback_episodes
    (episodeLaw : Episode → Measure (ℝ × (ℕ → ℝ)))
    [∀ e, IsProbabilityMeasure (episodeLaw e)]
    (policy : ℝ → ℝ) (hp : Measurable policy) :
    iIndepFun (fun e sample => episodeTrajectory policy (sample e))
      (Measure.infinitePi episodeLaw) := by
  exact iIndepFun_infinitePi
    (fun _ => actual_fixed_controller_episode_trajectory_is_measurable policy hp)

def timedEpisodeTrajectory (policy : ℕ → ℝ → ℝ) (data : ℝ × (ℕ → ℝ)) : ℕ → ℝ
  | 0 => data.1
  | n+1 => timedEpisodeTrajectory policy data n +
      policy n (timedEpisodeTrajectory policy data n) + data.2 n

theorem actual_fixed_time_dependent_feedback_episode_is_measurable
    (policy : ℕ → ℝ → ℝ) (hp : ∀ n, Measurable (policy n)) :
    Measurable (timedEpisodeTrajectory policy) := by
  apply measurable_pi_iff.mpr
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n hn =>
    exact (hn.add ((hp n).comp hn)).add
      ((measurable_pi_apply n).comp measurable_snd)

theorem actual_arbitrary_independent_data_give_independent_time_dependent_feedback_episodes
    (P : Measure Omega) (data : Episode → Omega → ℝ × (ℕ → ℝ))
    (hind : iIndepFun data P) (policy : ℕ → ℝ → ℝ)
    (hp : ∀ n, Measurable (policy n)) :
    iIndepFun (fun e o => timedEpisodeTrajectory policy (data e o)) P := by
  exact hind.comp (fun _ => timedEpisodeTrajectory policy)
    (fun _ => actual_fixed_time_dependent_feedback_episode_is_measurable policy hp)

theorem actual_independently_drawn_arbitrary_initial_and_noise_sequence_laws_construct_episodes
    (initialLaw : Episode → Measure ℝ) [∀ e, IsProbabilityMeasure (initialLaw e)]
    (noiseSequenceLaw : Episode → Measure (ℕ → ℝ))
    [∀ e, IsProbabilityMeasure (noiseSequenceLaw e)]
    (policy : ℕ → ℝ → ℝ) (hp : ∀ n, Measurable (policy n)) :
    iIndepFun (fun e sample => timedEpisodeTrajectory policy (sample e))
      (Measure.infinitePi (fun e => (initialLaw e).prod (noiseSequenceLaw e))) := by
  exact iIndepFun_infinitePi
    (fun _ => actual_fixed_time_dependent_feedback_episode_is_measurable policy hp)

theorem actual_time_dependent_stationary_specialization_is_the_original_source_trajectory
    (policy : ℝ → ℝ) (data : ℝ × (ℕ → ℝ)) (n : ℕ) :
    timedEpisodeTrajectory (fun _ => policy) data n=episodeTrajectory policy data n := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [timedEpisodeTrajectory, episodeTrajectory, hn]

end SafeLearning.CompleteAppliedEpisodeIndependence
