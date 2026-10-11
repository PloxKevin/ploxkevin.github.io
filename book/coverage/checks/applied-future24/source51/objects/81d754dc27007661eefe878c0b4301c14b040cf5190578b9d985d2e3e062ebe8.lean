import SafeLearning.CompleteAppliedPendulumLocalField
import SafeLearning.CompleteBarrierAbsolutelyContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedPendulumStability
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumLocalField
open SafeLearning.CompleteAppliedGlobalLipschitzTrajectory

def auxiliaryPath (initial:ℝ×ℝ) : ℝ→ℝ×ℝ :=
  globalSolution auxiliaryField initial (301/10) actual_auxiliary_field_is_globally_lipschitz

theorem actual_auxiliary_path_has_derived_existence_and_ode (initial:ℝ×ℝ) :
    auxiliaryPath initial 0=initial ∧ ContDiff ℝ 1 (auxiliaryPath initial) ∧
      ∀ t:ℝ,HasDerivAt (auxiliaryPath initial) (auxiliaryField (auxiliaryPath initial t)) t := by
  exact ⟨actual_global_solution_initial_condition _ _ _ _,
    (actual_global_solution_is_c1_and_locally_absolutely_continuous _ _ _ _).1,
    actual_global_solution_has_the_true_ode_at_every_real_time _ _ _ _⟩

theorem actual_path_storage_derivative (initial:ℝ×ℝ) (t:ℝ) :
    HasDerivAt (fun t=>storage (auxiliaryPath initial t))
      (storageRate (auxiliaryPath initial t)) t := by
  have hd:=(actual_auxiliary_path_has_derived_existence_and_ode initial).2.2 t
  have hq := (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (auxiliaryPath initial t)).comp_hasDerivAt t hd
  have hv := (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (auxiliaryPath initial t)).comp_hasDerivAt t hd
  have h:=((hq.pow 2).const_mul 10).add (hv.pow 2) |>.add ((hq.mul hv).div_const 20)
  convert h using 1
  · funext s
    dsimp [storage] <;> ring
  · dsimp [storageRate,auxiliaryField] <;> ring

theorem actual_auxiliary_path_storage_has_true_exponential_decay (initial:ℝ×ℝ)
    (t:ℝ) (ht:0≤ t) :
    storage (auxiliaryPath initial t)≤ storage initial*Real.exp (-(1/1000)*t) := by
  have hp:=actual_auxiliary_path_has_derived_existence_and_ode initial
  have hcq:=hp.2.1.fst
  have hcv:=hp.2.1.snd
  have hc : ContDiff ℝ 1 (fun s=>-(storage (auxiliaryPath initial s))) := by
    unfold storage
    have ha : ContDiff ℝ 1 (fun s=>10*(auxiliaryPath initial s).1^2) := contDiff_const.mul (hcq.pow 2)
    have hb : ContDiff ℝ 1 (fun s=>(auxiliaryPath initial s).1*(auxiliaryPath initial s).2/20) := (hcq.mul hcv).mul contDiff_const
    exact (ha.add (hcv.pow 2) |>.add hb).neg
  have hd : ∀ᵐ s ∂volume,s∈Icc 0 t → HasDerivAt
      (fun s=>-(storage (auxiliaryPath initial s))) (-(storageRate (auxiliaryPath initial s))) s :=
    Eventually.of_forall (fun s _=>(actual_path_storage_derivative initial s).neg)
  have hb : ∀ᵐ s ∂volume,s∈Icc 0 t →
      -(1/1000:ℝ)*(-(storage (auxiliaryPath initial s)))≤-(storageRate (auxiliaryPath initial s)) := by
    apply Eventually.of_forall
    intro s _
    linarith [actual_auxiliary_storage_derivative_has_a_uniform_negative_rate (auxiliaryPath initial s)]
  have h:=CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
    (fun s=>-(storage (auxiliaryPath initial s))) (fun s=>-(storageRate (auxiliaryPath initial s)))
    (1/1000) t ht hc.contDiffOn.absolutelyContinuousOnInterval hd hb t ⟨ht,le_rfl⟩
  rw [hp.1] at h
  linarith

theorem actual_storage_controls_the_true_state_norm (x:ℝ×ℝ) :
    (2/5:ℝ)*‖x‖^2≤ storage x ∧ storage x≤22*‖x‖^2 := by
  have h:=actual_local_storage_has_global_positive_quadratic_bounds x
  have hq : |x.1|≤‖x‖:=by simpa only [Real.norm_eq_abs] using norm_fst_le x
  have hv : |x.2|≤‖x‖:=by simpa only [Real.norm_eq_abs] using norm_snd_le x
  have hq2 : x.1^2≤‖x‖^2:=by nlinarith [sq_abs x.1,abs_nonneg x.1,norm_nonneg x]
  have hv2 : x.2^2≤‖x‖^2:=by nlinarith [sq_abs x.2,abs_nonneg x.2,norm_nonneg x]
  have hnorm : ‖x‖^2≤ x.1^2+x.2^2 := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    rcases le_total |x.1| |x.2| with hs|hs
    · rw [max_eq_right hs,sq_abs];nlinarith [sq_nonneg x.1]
    · rw [max_eq_left hs,sq_abs];nlinarith [sq_nonneg x.2]
  constructor <;> nlinarith

theorem actual_auxiliary_path_has_true_uniform_norm_decay (initial:ℝ×ℝ) (t:ℝ)
    (ht:0≤ t) :
    ‖auxiliaryPath initial t‖≤8*‖initial‖*Real.exp (-(1/2000)*t) := by
  have h:=actual_auxiliary_path_storage_has_true_exponential_decay initial t ht
  have ha:=(actual_storage_controls_the_true_state_norm (auxiliaryPath initial t)).1
  have hb:=(actual_storage_controls_the_true_state_norm initial).2
  have he : Real.exp (-(1/1000)*t)=Real.exp (-(1/2000)*t)^2 := by
    rw [pow_two,←Real.exp_add];congr 1;ring
  rw [he] at h
  have hh:=mul_le_mul_of_nonneg_right hb (sq_nonneg (Real.exp (-(1/2000)*t)))
  have hn:=norm_nonneg (auxiliaryPath initial t)
  have hm:=norm_nonneg initial
  have hp:=Real.exp_pos (-(1/2000)*t)
  let bound : ℝ := ‖initial‖*Real.exp (-(1/2000)*t)
  have hbound : 0≤bound := mul_nonneg hm hp.le
  have hsq : ‖auxiliaryPath initial t‖^2≤55*bound^2 := by
    dsimp [bound]
    nlinarith [h.trans hh]
  calc
    _≤8*bound := by nlinarith only [hsq,hn,hbound]
    _=8*‖initial‖*Real.exp (-(1/2000)*t) := by dsimp [bound];ring

theorem actual_small_initial_auxiliary_path_stays_in_the_source_region (initial:ℝ×ℝ)
    (hi:‖initial‖≤1/80) (t:ℝ) (ht:0≤ t) :
    |(auxiliaryPath initial t).1|≤1/10 := by
  have hb:=actual_auxiliary_path_has_true_uniform_norm_decay initial t ht
  have he : Real.exp (-(1/2000)*t)≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
  have hh:=mul_le_mul_of_nonneg_left he (show 0≤8*‖initial‖ by positivity)
  have hq : |(auxiliaryPath initial t).1|≤‖auxiliaryPath initial t‖:=by
    simpa only [Real.norm_eq_abs] using norm_fst_le (auxiliaryPath initial t)
  nlinarith

theorem actual_nonlinear_hanging_source_has_a_derived_global_small_initial_solution
    (initial:ℝ×ℝ) (hi:‖initial‖≤1/80) :
    auxiliaryPath initial 0=initial ∧
      (∀ a b:ℝ,AbsolutelyContinuousOnInterval (auxiliaryPath initial) a b) ∧
      (∀ t:ℝ,0≤ t → HasDerivAt (auxiliaryPath initial)
        (hangingField (auxiliaryPath initial t)) t) ∧
      (∀ t:ℝ,0≤ t → ‖auxiliaryPath initial t‖≤8*‖initial‖*Real.exp (-(1/2000)*t)) ∧
      Tendsto (auxiliaryPath initial) atTop (nhds 0) := by
  have hp:=actual_auxiliary_path_has_derived_existence_and_ode initial
  refine ⟨hp.1,fun a b=>hp.2.1.contDiffOn.absolutelyContinuousOnInterval,?_,
    fun t ht=>actual_auxiliary_path_has_true_uniform_norm_decay initial t ht,?_⟩
  · intro t ht
    have he:=(actual_auxiliary_field_agrees_with_source_near_hanging
      (auxiliaryPath initial t) (actual_small_initial_auxiliary_path_stays_in_the_source_region initial hi t ht)).1
    rw [←he]
    exact hp.2.2 t
  · have he : Tendsto (fun t:ℝ=>8*‖initial‖*Real.exp (-(1/2000)*t)) atTop (nhds 0) := by
      have hl : Tendsto (fun t:ℝ=>-(1/2000)*t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1/2000):ℝ)<0)
      simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hl)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun t=>norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact actual_auxiliary_path_has_true_uniform_norm_decay initial t ht

end SafeLearning.CompleteAppliedPendulumStability
