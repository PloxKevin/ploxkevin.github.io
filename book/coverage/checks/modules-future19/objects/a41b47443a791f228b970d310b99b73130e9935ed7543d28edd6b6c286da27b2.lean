import SafeLearning.CompleteModulesLandscapeARViolationCounts
import SafeLearning.CompleteModulesLandscapeARStableMoments
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeIndependentStates
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARGaussianLaw
open CompleteModulesLandscapeARViolationCounts CompleteModulesLandscapeARStableMoments
open CompleteAppliedGaussianCDF

theorem actual_gain_one_replaces_every_positive_time_state_by_the_fresh_noise
    (goal sigma : ℝ) (T : ℕ) (t : Fin T) (w : Fin T → ℝ) :
    stateAt 1 goal sigma t w = goal + sigma*w t := by
  change trajectory 1 goal sigma w (t.val+1) = _
  rw [trajectory,actual_fresh_noise_is_the_corresponding_finite_product_coordinate w t.val t.isLt]
  ring

theorem actual_gain_one_positive_time_states_are_jointly_independent
    (goal sigma : ℝ) (T : ℕ) :
    iIndepFun (fun t : Fin T => stateAt 1 goal sigma t) (noiseLaw T) := by
  have hn := (actual_canonical_noises_are_independent_standard_gaussians T).1
  have h := hn.comp (fun _ : Fin T => fun x : ℝ => goal+sigma*x)
    (by intro i; fun_prop)
  have he : (fun t : Fin T => (fun x : ℝ => goal+sigma*x) ∘ (fun w : Fin T → ℝ => w t)) =
      (fun t : Fin T => stateAt 1 goal sigma t) := by
    funext t w
    exact (actual_gain_one_replaces_every_positive_time_state_by_the_fresh_noise goal sigma T t w).symm
  rw [he] at h
  exact h

theorem actual_gain_one_joint_violation_probability_has_the_source_product_formula
    (goal sigma : ℝ) (T : ℕ) (hsigma : sigma ≠ 0) :
    (noiseLaw T).real {w | ∃ t : Fin T, 1 < stateAt 1 goal sigma t w} =
      1-(1-(1-standardCDF ((1-goal)/|sigma|)))^T := by
  let p : ℝ := 1-standardCDF ((1-goal)/|sigma|)
  have he : ∀ t : Fin T,
      (noiseLaw T).real {w | 1 < stateAt 1 goal sigma t w} = p := by
    intro t
    rw [actual_each_one_based_violation_probability_is_the_printed_piecewise_tail]
    rw [exactTail,if_neg hsigma]
    have hm : trueMean 1 goal (t.val+1) = goal := by simp [trueMean]
    have hv := actual_true_variance_has_the_printed_closed_geometric_formula
      1 sigma (t.val+1) (by norm_num) (by norm_num)
    have hvar : trueVariance 1 sigma (t.val+1) = sigma^2 := by simpa using hv
    rw [hm,hvar,Real.sqrt_sq_eq_abs]
  have hind := actual_gain_one_positive_time_states_are_jointly_independent goal sigma T
  have hprod := hind.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin T))
    (sets := fun _ => Iic (1:ℝ)) (by intro i hi; exact measurableSet_Iic)
  have hsafeSet : (⋂i : Fin T, stateAt 1 goal sigma i ⁻¹' Iic (1:ℝ)) =
      {w | ∀t : Fin T, stateAt 1 goal sigma t w ≤ 1} := by ext w; simp
  have hi : (noiseLaw T) {w | ∀ t : Fin T, stateAt 1 goal sigma t w ≤ 1} =
      ∏t : Fin T, (noiseLaw T) {w | stateAt 1 goal sigma t w ≤ 1} := by
    simpa only [Finset.mem_univ,iInter_true,hsafeSet] using hprod
  have hr := congrArg ENNReal.toReal hi
  simp only [ENNReal.toReal_prod,←measureReal_def] at hr
  have hsafe : ∀t : Fin T, (noiseLaw T).real {w | stateAt 1 goal sigma t w ≤ 1} = 1-p := by
    intro t
    have hm : MeasurableSet {w | 1 < stateAt 1 goal sigma t w} :=
      measurableSet_Ioi.preimage (actual_one_based_state_is_measurable 1 goal sigma T t)
    have hc := probReal_compl_eq_one_sub hm
    have hset : {w | 1 < stateAt 1 goal sigma t w}ᶜ =
        {w | stateAt 1 goal sigma t w ≤ 1} := by ext w; simp
    rw [hset,he t] at hc
    exact hc
  simp_rw [hsafe] at hr
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hr
  have hm : MeasurableSet {w | ∀t : Fin T, stateAt 1 goal sigma t w ≤ 1} := by
    rw [←hsafeSet]
    exact MeasurableSet.iInter (fun t => measurableSet_Iic.preimage
      (actual_one_based_state_is_measurable 1 goal sigma T t))
  have hc := probReal_compl_eq_one_sub hm
  have hset : {w | ∀t : Fin T, stateAt 1 goal sigma t w ≤ 1}ᶜ =
      {w | ∃t : Fin T, 1 < stateAt 1 goal sigma t w} := by ext w; simp
  rw [hset,hr] at hc
  simpa [p] using hc

theorem actual_nonzero_noise_and_gain_not_one_make_the_first_two_states_dependent
    (k goal sigma : ℝ) (T : ℕ) (hT : 2 ≤ T) (hsigma : sigma ≠ 0) (hk : k ≠ 1) :
    ¬IndepFun (fun w : Fin T → ℝ => trajectory k goal sigma w 1)
      (fun w : Fin T → ℝ => trajectory k goal sigma w 2) (noiseLaw T) := by
  intro hind
  let s : Fin (T+1) := ⟨1,by omega⟩
  let t : Fin (T+1) := ⟨2,by omega⟩
  have hg := actual_recursive_trajectory_has_a_genuine_joint_gaussian_law k goal sigma T
  have hz := hind.covariance_eq_zero (hg.eval s).memLp_two (hg.eval t).memLp_two
  have hc := actual_recursive_trajectory_has_the_printed_temporal_covariance
    k goal sigma T s t (by simp [s,t])
  change cov[fun w : Fin T → ℝ => trajectory k goal sigma w 1,
    fun w : Fin T → ℝ => trajectory k goal sigma w 2;noiseLaw T] = _ at hc
  rw [hz] at hc
  norm_num [s,t,trueVariance,Finset.sum_range_succ] at hc
  have ha : 1-k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  rcases hc with hzero | hzero
  · exact hsigma hzero
  · exact ha hzero

theorem actual_zero_noise_makes_the_first_two_states_independent_at_every_gain
    (k goal : ℝ) (T : ℕ) :
    IndepFun (fun w : Fin T → ℝ => trajectory k goal 0 w 1)
      (fun w : Fin T → ℝ => trajectory k goal 0 w 2) (noiseLaw T) := by
  have he1 : (fun w : Fin T → ℝ => trajectory k goal 0 w 1) =
      (fun _ : Fin T → ℝ => trueMean k goal 1) := by
    funext w; exact actual_zero_noise_scale_is_the_deterministic_mean_trajectory k goal w 1
  rw [he1]
  exact indepFun_const_left _ _

theorem actual_sigma_zero_passing_explorer_trajectory_need_not_make_the_whole_safe_set_invariant :
    (∀t : ℕ, trueMean (11/10) (4/5) t ≤ 1) ∧
      (-10:ℝ) ≤ 1 ∧ ((-10)-(11/10)*((-10)-(4/5)):ℝ) = 47/25 ∧
      1 < ((-10)-(11/10)*((-10)-(4/5)):ℝ) := by
  have hp : ∀t : ℕ, |(-1/10:ℝ)^t| ≤ 1 := by
    intro t
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by norm_num)
  refine ⟨?_,by norm_num,by norm_num,by norm_num⟩
  intro t
  cases t with
  | zero => norm_num [trueMean]
  | succ t =>
    have hu := (abs_le.mp (hp t)).2
    norm_num [trueMean,pow_succ]
    nlinarith

end SafeLearning.CompleteModulesLandscapeIndependentStates
