import SafeLearning.CompleteAppliedPendulumSourceField
import SafeLearning.CompleteAppliedGlobalLipschitzACVectorUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedPendulumStabilityConsequences
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumLocalField
open SafeLearning.CompleteAppliedPendulumStability
open SafeLearning.CompleteAppliedPendulumSourceField
open SafeLearning.CompleteAppliedGlobalLipschitzACVectorUniqueness

theorem actual_every_finite_ac_hanging_solution_is_the_constructed_small_initial_path
    (x:ℝ→ℝ×ℝ) (initial:ℝ×ℝ) (hi:‖initial‖≤1/80)
    (T:ℝ) (hT:0≤T) (hc:AbsolutelyContinuousOnInterval x 0 T)
    (hd:∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (hangingField (x t)) t)
    (hx:x 0=initial) : EqOn x (auxiliaryPath initial) (Icc 0 T) := by
  have hp:=actual_nonlinear_hanging_source_has_a_derived_global_small_initial_solution initial hi
  exact actual_globally_lipschitz_vector_field_has_unique_existing_ac_a_e_solutions
    hangingField (101/10) actual_both_source_pendulum_coordinate_fields_are_globally_lipschitz.2
    x (auxiliaryPath initial) T hT hc (hp.2.1 0 T) hd
    (Eventually.of_forall (fun t ht=>hp.2.2.1 t ht.1)) (hx.trans hp.1.symm)

theorem actual_every_admitted_small_initial_hanging_solution_has_uniform_exponential_decay
    (x:ℝ→ℝ×ℝ) (initial:ℝ×ℝ) (hi:‖initial‖≤1/80)
    (hc:∀T:ℝ,0≤T → AbsolutelyContinuousOnInterval x 0 T)
    (hd:∀T:ℝ,0≤T → ∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (hangingField (x t)) t)
    (hx:x 0=initial) :
    (∀t:ℝ,0≤t → ‖x t‖≤8*‖initial‖*Real.exp (-(1/2000)*t)) ∧
      Tendsto x atTop (nhds 0) := by
  have he (t:ℝ) (ht:0≤t) : x t=auxiliaryPath initial t :=
    actual_every_finite_ac_hanging_solution_is_the_constructed_small_initial_path
      x initial hi t ht (hc t ht) (hd t ht) hx ⟨ht,le_rfl⟩
  constructor
  · intro t ht
    rw [he t ht]
    exact actual_auxiliary_path_has_true_uniform_norm_decay initial t ht
  · apply Tendsto.congr' _
      (actual_nonlinear_hanging_source_has_a_derived_global_small_initial_solution initial hi).2.2.2.2
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (he t ht).symm

theorem actual_hanging_origin_has_true_epsilon_delta_lyapunov_stability
    (epsilon:ℝ) (hepsilon:0<epsilon) :
    ∃delta:ℝ,0<delta ∧ ∀initial:ℝ×ℝ,‖initial‖<delta →
      ∀x:ℝ→ℝ×ℝ,
        (∀T:ℝ,0≤T → AbsolutelyContinuousOnInterval x 0 T) →
        (∀T:ℝ,0≤T → ∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (hangingField (x t)) t) →
        x 0=initial → ∀t:ℝ,0≤t → ‖x t‖<epsilon := by
  refine ⟨min (1/80) (epsilon/16),lt_min (by norm_num) (by positivity),?_⟩
  intro initial hi x hc hd hx t ht
  have hir : ‖initial‖≤1/80 := (lt_of_lt_of_le hi (min_le_left _ _)).le
  have hie : ‖initial‖<epsilon/16 := lt_of_lt_of_le hi (min_le_right _ _)
  have h:= (actual_every_admitted_small_initial_hanging_solution_has_uniform_exponential_decay
    x initial hir hc hd hx).1 t ht
  have hexp : Real.exp (-(1/2000)*t)≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
  have hb:=mul_le_mul_of_nonneg_left hexp (show 0≤8*‖initial‖ by positivity)
  nlinarith

def originalHangingPath (initial:ℝ×ℝ) (t:ℝ) : ℝ×ℝ :=
  ((auxiliaryPath initial t).1+Real.pi,(auxiliaryPath initial t).2)

theorem actual_hanging_small_initial_solution_is_a_true_original_pendulum_solution
    (initial:ℝ×ℝ) (hi:‖initial‖≤1/80) :
    originalHangingPath initial 0=(initial.1+Real.pi,initial.2) ∧
      (∀t:ℝ,0≤t → HasDerivAt (originalHangingPath initial)
        (field (originalHangingPath initial t)) t) ∧
      ∀t:ℝ,0≤t →
        ‖originalHangingPath initial t-(Real.pi,0)‖≤8*‖initial‖*Real.exp (-(1/2000)*t) := by
  have hp:=actual_nonlinear_hanging_source_has_a_derived_global_small_initial_solution initial hi
  refine ⟨by simp [originalHangingPath,hp.1],?_,?_⟩
  · intro t ht
    have hd:=hp.2.2.1 t ht
    have hq := (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (auxiliaryPath initial t)).comp_hasDerivAt t hd
    have hv := (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (auxiliaryPath initial t)).comp_hasDerivAt t hd
    have h:=(hq.add_const Real.pi).prodMk hv
    convert h using 1
    · funext s;rfl
    · dsimp [originalHangingPath,field,hangingField]
      apply Prod.ext <;> simp [Real.sin_add]
  · intro t ht
    have he : originalHangingPath initial t-(Real.pi,0)=auxiliaryPath initial t := by
      apply Prod.ext <;> simp [originalHangingPath]
    rw [he]
    exact actual_auxiliary_path_has_true_uniform_norm_decay initial t ht

end SafeLearning.CompleteAppliedPendulumStabilityConsequences
