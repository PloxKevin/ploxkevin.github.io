import SafeLearning.CompleteModulesLandscapeARGaussianLaw
import SafeLearning.CompleteModulesLandscapeARStableMoments
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace SafeLearning.CompleteModulesLandscapeARPathFluctuation
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARGaussianLaw
open CompleteModulesLandscapeARStableMoments

/-- The actual countably infinite product of normalized standard Gaussian noise laws. -/
def infiniteNoiseLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure infiniteNoiseLaw := by
  unfold infiniteNoiseLaw
  infer_instance

/-- The original recurrence, now defined for all times on the infinite noise space. -/
def infiniteTrajectory (k goal sigma : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t+1 => infiniteTrajectory k goal sigma w t -
      k*(infiniteTrajectory k goal sigma w t-goal) + sigma*w t

theorem actual_infinite_noises_are_independent_normalized_standard_gaussians :
    iIndepFun (fun t : ℕ => fun w : ℕ → ℝ => w t) infiniteNoiseLaw ∧
      ∀ t : ℕ, HasLaw (fun w : ℕ → ℝ => w t) (gaussianReal 0 1) infiniteNoiseLaw := by
  constructor
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
      (X := fun _ => id) (fun _ => measurable_id)
  · intro t
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) t).hasLaw

theorem actual_infinite_noise_prefix_has_the_existing_finite_product_law (T : ℕ) :
    HasLaw (fun w : ℕ → ℝ => fun j : Fin T => w j.val) (noiseLaw T) infiniteNoiseLaw := by
  refine ⟨(measurable_pi_iff.mpr (fun j : Fin T => measurable_pi_apply j.val)).aemeasurable, ?_⟩
  unfold infiniteNoiseLaw noiseLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun j : Fin T => j.val) Fin.val_injective,
    Measure.infinitePi_eq_pi]

theorem actual_infinite_trajectory_satisfies_the_literal_initial_condition_and_recursion
    (k goal sigma : ℝ) (w : ℕ → ℝ) :
    infiniteTrajectory k goal sigma w 0=0 ∧ ∀ t : ℕ,
      infiniteTrajectory k goal sigma w (t+1)=infiniteTrajectory k goal sigma w t-
        k*(infiniteTrajectory k goal sigma w t-goal)+sigma*w t := by
  exact ⟨rfl, fun _ => rfl⟩

theorem actual_infinite_trajectory_agrees_with_every_existing_finite_horizon_prefix
    (k goal sigma : ℝ) (w : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) :
    infiniteTrajectory k goal sigma w t=
      trajectory k goal sigma (fun j : Fin T => w j.val) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t<T := by omega
    rw [infiniteTrajectory, trajectory, ih (by omega),
      actual_fresh_noise_is_the_corresponding_finite_product_coordinate _ t hlt]

theorem actual_infinite_trajectory_prefix_has_the_existing_true_joint_gaussian_law
    (k goal sigma : ℝ) (T : ℕ) :
    HasLaw (fun w : ℕ → ℝ => fun t : Fin (T+1) => infiniteTrajectory k goal sigma w t.val)
      (trajectoryLaw k goal sigma T) infiniteNoiseLaw := by
  have hfinite : HasLaw (vectorTrajectory k goal sigma T)
      (trajectoryLaw k goal sigma T) (noiseLaw T) :=
    ⟨(actual_finite_trajectory_is_measurable k goal sigma T).aemeasurable, rfl⟩
  have h := hfinite.comp (actual_infinite_noise_prefix_has_the_existing_finite_product_law T)
  convert h using 1
  funext w t
  exact actual_infinite_trajectory_agrees_with_every_existing_finite_horizon_prefix
    k goal sigma w T t.val (by omega)

theorem actual_standard_gaussian_has_positive_probability_of_both_fixed_tail_events :
    (gaussianReal 0 1) (Ioi (1 : ℝ)) ≠ 0 ∧
      (gaussianReal 0 1) (Iio (-1 : ℝ)) ≠ 0 := by
  constructor
  · intro hzero
    have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0) hzero
    simp only [Real.volume_Ioi] at hv
    exact ENNReal.top_ne_zero hv
  · intro hzero
    have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0) hzero
    simp only [Real.volume_Iio] at hv
    exact ENNReal.top_ne_zero hv

/-- A direct specialization of the official second Borel--Cantelli lemma to actual noise events.
The positive probability is proved from the true Gaussian measure in the applications below. -/
theorem actual_positive_probability_noise_event_occurs_infinitely_often
    (B : Set ℝ) (hB : MeasurableSet B) (hp : (gaussianReal 0 1) B ≠ 0) :
    ∀ᵐ w ∂infiniteNoiseLaw, ∃ᶠ t in atTop, w t ∈ B := by
  let events : ℕ → Set (ℕ → ℝ) := fun t => (fun w => w t) ⁻¹' B
  have hm : ∀ t, MeasurableSet (events t) := fun t => hB.preimage (measurable_pi_apply t)
  have hind := actual_infinite_noises_are_independent_normalized_standard_gaussians.1
  have hs : iIndepSet events infiniteNoiseLaw := by
    apply (iIndepSet_iff_meas_biInter hm).mpr
    intro S
    exact hind.measure_inter_preimage_eq_mul S (sets := fun _ => B) (fun _ _ => hB)
  have hprob : ∀ t, infiniteNoiseLaw (events t)=(gaussianReal 0 1) B := by
    intro t
    exact (actual_infinite_noises_are_independent_normalized_standard_gaussians.2 t).measure_eq hB
  have hsum : (∑' t, infiniteNoiseLaw (events t))=∞ := by
    simp_rw [hprob]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hp
  have hmeasure := measure_limsup_eq_one hm hs hsum
  have hae : ∀ᵐ w ∂infiniteNoiseLaw, w ∈ limsup events atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hmeasure
  filter_upwards [hae] with w hw
  exact mem_limsup_iff_frequently_mem.mp hw

theorem actual_infinite_standard_gaussian_noises_cross_both_thresholds_infinitely_often :
    ∀ᵐ w ∂infiniteNoiseLaw,
      (∃ᶠ t in atTop, (1 : ℝ)<w t) ∧ (∃ᶠ t in atTop, w t<(-1 : ℝ)) := by
  have hp := actual_standard_gaussian_has_positive_probability_of_both_fixed_tail_events
  filter_upwards
    [actual_positive_probability_noise_event_occurs_infinitely_often (Ioi 1) measurableSet_Ioi hp.1,
     actual_positive_probability_noise_event_occurs_infinitely_often (Iio (-1)) measurableSet_Iio hp.2]
    with w hu hl
  exact ⟨hu, hl⟩

theorem actual_infinite_standard_gaussian_noise_has_no_finite_real_limit_almost_surely :
    ∀ᵐ w ∂infiniteNoiseLaw, ∀ L : ℝ, ¬ Tendsto w atTop (𝓝 L) := by
  filter_upwards [actual_infinite_standard_gaussian_noises_cross_both_thresholds_infinitely_often]
    with w hw
  intro L hL
  have hu : (1 : ℝ) ≤ L := ge_of_tendsto_of_frequently hL (hw.1.mono (fun _ h => h.le))
  have hl : L ≤ (-1 : ℝ) := le_of_tendsto_of_frequently hL (hw.2.mono (fun _ h => h.le))
  linarith

/-- A deterministic implication of the actual recurrence; no probability or desired limit is
assumed for the noise. -/
theorem actual_state_path_convergence_would_force_a_finite_noise_limit
    (k goal sigma : ℝ) (hsigma : sigma ≠ 0) (w : ℕ → ℝ) (L : ℝ)
    (hpath : Tendsto (infiniteTrajectory k goal sigma w) atTop (𝓝 L)) :
    Tendsto w atTop (𝓝 (k*(L-goal)/sigma)) := by
  have hshift := hpath.comp (tendsto_add_atTop_nat 1)
  have hlim := ((hshift.sub hpath).add ((hpath.sub_const goal).const_mul k)).div_const sigma
  have he : (fun t => (infiniteTrajectory k goal sigma w (t+1)-
      infiniteTrajectory k goal sigma w t+k*(infiniteTrajectory k goal sigma w t-goal))/sigma)=w := by
    funext t
    rw [infiniteTrajectory]
    field_simp
    <;> ring
  simpa only [Function.comp_def, he, sub_self, zero_add] using hlim

/-- Nonzero Gaussian noise prevents convergence to every finite real value, for every real gain.
The quantifier over limits is inside one almost-sure event, obtained from Borel--Cantelli. -/
theorem actual_noisy_original_state_path_has_no_finite_real_limit_almost_surely
    (k goal sigma : ℝ) (hsigma : sigma ≠ 0) :
    ∀ᵐ w ∂infiniteNoiseLaw, ∀ L : ℝ,
      ¬ Tendsto (infiniteTrajectory k goal sigma w) atTop (𝓝 L) := by
  filter_upwards [actual_infinite_standard_gaussian_noise_has_no_finite_real_limit_almost_surely]
    with w hw
  intro L hL
  exact hw (k*(L-goal)/sigma)
    (actual_state_path_convergence_would_force_a_finite_noise_limit k goal sigma hsigma w L hL)

theorem actual_zero_noise_infinite_state_path_is_the_true_deterministic_mean
    (k goal : ℝ) (w : ℕ → ℝ) : infiniteTrajectory k goal 0 w=trueMean k goal := by
  funext t
  rw [actual_infinite_trajectory_agrees_with_every_existing_finite_horizon_prefix
    k goal 0 w t t le_rfl,
    actual_zero_noise_scale_is_the_deterministic_mean_trajectory]

theorem actual_zero_noise_stable_infinite_state_path_converges_to_the_goal
    (k goal : ℝ) (hk : 0<k) (hk2 : k<2) (w : ℕ → ℝ) :
    Tendsto (infiniteTrajectory k goal 0 w) atTop (𝓝 goal) := by
  rw [actual_zero_noise_infinite_state_path_is_the_true_deterministic_mean]
  exact actual_state_mean_converges_to_the_goal_for_every_stable_source_gain k goal hk hk2

end SafeLearning.CompleteModulesLandscapeARPathFluctuation
