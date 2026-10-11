import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2


set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteCoreMPCLocalBootstrap27

/-- A local quadratic upper bound plus continuity rules out leaving the local
Lyapunov sublevel before the end of a sufficiently short line segment. The
bound is assumed only where the Lyapunov value is already local. -/
theorem continuous_local_quadratic_bound_bootstraps_the_endpoint
    (V : ℝ → ℝ) (delta c : ℝ) (hdelta : 0 < delta) (hc : 0 ≤ c)
    (hsmall : c ≤ delta) (hcontinuous : ContinuousOn V (Icc 0 1))
    (hzero : V 0 = 0)
    (hlocal : ∀ t ∈ Icc 0 1, V t ≤ delta → V t ≤ c * t ^ 2) :
    V 1 ≤ c := by
  have hendpoint : V 1 ≤ delta := by
    by_contra hnot
    have habove : delta < V 1 := lt_of_not_ge hnot
    obtain ⟨t, ht, heq⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num)
      hcontinuous (show delta ∈ Ioo (V 0) (V 1) by simpa [hzero] using And.intro hdelta habove)
    have hbound := hlocal t ⟨ht.1.le, ht.2.le⟩ (by simpa [heq])
    have hsq : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    have hmult : c * t ^ 2 ≤ delta * t ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
    have hstrict : delta * t ^ 2 < delta := by nlinarith
    rw [heq] at hbound
    linarith
  simpa using hlocal 1 (by norm_num) hendpoint

end SafeLearning.CompleteCoreMPCLocalBootstrap27

namespace SafeLearning.CompleteCoreMPCLocalBootstrap27

theorem continuous_local_quadratic_state_bound_bootstraps_small_state_error
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (X : Set S) (hX : Convex ℝ X) (V : S → ℝ) (z x : S)
    (hz : z ∈ X) (hx : x ∈ X) (delta cU : ℝ)
    (hdelta : 0 < delta) (hcU : 0 ≤ cU)
    (hsmall : cU * ‖x - z‖ ^ 2 ≤ delta)
    (hcontinuous : ContinuousOn V X) (hzero : V z = 0)
    (hlocal : ∀ y ∈ X, V y ≤ delta → V y ≤ cU * ‖y - z‖ ^ 2) :
    V x ≤ cU * ‖x - z‖ ^ 2 := by
  let path : ℝ → S := fun t => z + t • (x - z)
  have hpath : ∀ t ∈ Icc 0 1, path t ∈ X := by
    intro t ht
    exact hX.add_smul_sub_mem hz hx ht
  have hpcontinuous : Continuous path :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hvcontinuous : ContinuousOn (fun t => V (path t)) (Icc 0 1) :=
    hcontinuous.comp hpcontinuous.continuousOn hpath
  have hpzero : path 0 = z := by simp [path]
  have hpone : path 1 = x := by simp [path]
  have hbound := continuous_local_quadratic_bound_bootstraps_the_endpoint
    (fun t => V (path t)) delta (cU * ‖x - z‖ ^ 2) hdelta
    (mul_nonneg hcU (sq_nonneg _)) hsmall hvcontinuous (by simpa [hpzero] using hzero)
    (by
      intro t ht hvalue
      have hh := hlocal (path t) (hpath t ht) hvalue
      have hpnorm : ‖path t - z‖ = t * ‖x - z‖ := by
        simp only [path, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht.1]
      rw [hpnorm] at hh
      convert hh using 1 <;> ring)
  simpa [hpone] using hbound

end SafeLearning.CompleteCoreMPCLocalBootstrap27

namespace SafeLearning.CompleteCoreMPCLocalBootstrap27

def polytopicStateSet {S J : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (rows : J → S →L[ℝ] ℝ) (margin : ℝ) : Set S :=
  {state | ∀ j, rows j state ≤ 1 - margin}

theorem actual_linear_constraint_margin_covers_every_bounded_state_perturbation
    {S J : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (rows : J → S →L[ℝ] ℝ) (z x : S) (H radius margin : ℝ)
    (hH : 0 ≤ H) (hrows : ∀ j, ‖rows j‖ ≤ H)
    (hz : z ∈ polytopicStateSet rows margin)
    (herror : ‖x - z‖ ≤ radius) (hmargin : H * radius ≤ margin) :
    x ∈ polytopicStateSet rows 0 := by
  intro j
  have hlinear : rows j x = rows j z + rows j (x - z) := by
    rw [map_sub]
    ring
  have hnorm := (rows j).le_opNorm (x - z)
  have hrowerror : rows j (x - z) ≤ H * radius := by
    calc
      rows j (x - z) ≤ ‖rows j (x - z)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self (rows j (x - z))
      _ ≤ ‖rows j‖ * ‖x - z‖ := hnorm
      _ ≤ H * ‖x - z‖ := mul_le_mul_of_nonneg_right (hrows j) (norm_nonneg _)
      _ ≤ H * radius := mul_le_mul_of_nonneg_left herror hH
  have hnominal := hz j
  rw [hlinear]
  linarith

end SafeLearning.CompleteCoreMPCLocalBootstrap27


set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SafeLearning.CompleteCoreMPCNormBridge27

variable {I J : Type*} [Fintype I] [Fintype J]
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

theorem actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm
    (x : EuclideanSpace ℝ I) : ‖(fun i => x i)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
  intro i
  exact PiLp.norm_apply_le x i

theorem actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error
    (H : Matrix J I ℝ) (x : EuclideanSpace ℝ I) (j : J) :
    |(H *ᵥ (fun i => x i)) j| ≤ ‖H‖ * ‖x‖ := by
  calc
    |(H *ᵥ (fun i => x i)) j| ≤ ‖H *ᵥ (fun i => x i)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (H *ᵥ (fun i => x i)) j
    _ ≤ ‖H‖ * ‖(fun i => x i)‖ := Matrix.linfty_opNorm_mulVec H _
    _ ≤ ‖H‖ * ‖x‖ := mul_le_mul_of_nonneg_left
      (actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm x) (norm_nonneg H)

theorem actual_euclidean_feedback_deviation_implies_the_required_input_infinity_bound
    (u v : EuclideanSpace ℝ I) (k error : ℝ) (hbound : ‖u - v‖ ≤ k * error) :
    ‖(fun i => u i - v i)‖ ≤ k * error := by
  exact (actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm (u-v)).trans hbound

theorem actual_polytopic_tightening_covers_a_euclidean_state_perturbation
    (H : Matrix J I ℝ) (z x : EuclideanSpace ℝ I) (radius margin : ℝ)
    (hnominal : ∀ j, (H *ᵥ (fun i => z i)) j ≤ 1-margin)
    (hdistance : ‖x-z‖ ≤ radius) (hmargin : ‖H‖ * radius ≤ margin) :
    ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1 := by
  intro j
  have hb := actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H (x-z) j
  have hr : (H *ᵥ (fun i => x i-z i)) j ≤ margin := by
    calc
      (H *ᵥ (fun i => x i-z i)) j ≤ |(H *ᵥ (fun i => x i-z i)) j| := le_abs_self _
      _ ≤ ‖H‖ * ‖x-z‖ := hb
      _ ≤ ‖H‖ * radius := mul_le_mul_of_nonneg_left hdistance (norm_nonneg H)
      _ ≤ margin := hmargin
  have hlinear : (H *ᵥ (fun i => x i-z i)) j =
      (H *ᵥ (fun i => x i)) j - (H *ᵥ (fun i => z i)) j := by
    exact congrFun (Matrix.mulVec_sub H (fun i => x i) (fun i => z i)) j
  rw [hlinear] at hr
  linarith [hnominal j]

theorem actual_infinity_bounded_input_error_implies_the_euclidean_successor_radius
    {K : Type*} [Fintype K]
    (f : EuclideanSpace ℝ I → (K → ℝ) → EuclideanSpace ℝ I)
    (X : Set (EuclideanSpace ℝ I)) (U : Set (K → ℝ)) (lambda eta : ℝ)
    (hlambda : 0 ≤ lambda)
    (hLipschitz : ∀ x ∈ X, ∀ u ∈ U, ∀ d : K → ℝ, u+d ∈ U →
      ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖)
    (x : EuclideanSpace ℝ I) (u d : K → ℝ)
    (hx : x ∈ X) (hu : u ∈ U) (hud : u+d ∈ U) (hd : ‖d‖ ≤ eta) :
    ‖f x (u+d)-f x u‖ ≤ lambda * eta := by
  exact (hLipschitz x hx u hu d hud).trans (mul_le_mul_of_nonneg_left hd hlambda)



theorem actual_polytopic_state_constraint_set_is_convex
    (H : Matrix J I ℝ) (margin : ℝ) :
    Convex ℝ {x : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1-margin} := by
  have h : ∀ j, Convex ℝ {x : EuclideanSpace ℝ I |
      (H *ᵥ (fun i => x i)) j ≤ 1-margin} := by
    intro j
    let row : EuclideanSpace ℝ I →ₗ[ℝ] ℝ :=
      (LinearMap.proj j).comp ((Matrix.mulVecLin H).comp
        (WithLp.linearEquiv 2 ℝ (I → ℝ)).toLinearMap)
    exact convex_halfSpace_le (show IsLinearMap ℝ row from ⟨row.map_add, row.map_smul⟩) (1-margin)
  simpa only [← Set.ofPred_forall] using convex_iInter h

theorem actual_positive_lipschitz_assumption_three_implies_the_squared_local_budget
    (lambda eta delta cU : ℝ) (hlambda : 0 < lambda) (heta : 0 ≤ eta)
    (hdelta : 0 < delta) (hcU : 0 < cU)
    (hsmall : eta ≤ lambda⁻¹ * Real.sqrt (delta/cU)) :
    cU * (lambda*eta)^2 ≤ delta := by
  have hratio : 0 ≤ delta/cU := div_nonneg hdelta.le hcU.le
  have hbound : lambda*eta ≤ Real.sqrt (delta/cU) := by
    calc
      lambda*eta ≤ lambda*(lambda⁻¹ * Real.sqrt (delta/cU)) :=
        mul_le_mul_of_nonneg_left hsmall hlambda.le
      _ = Real.sqrt (delta/cU) := by rw [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]
  have hnonneg : 0 ≤ lambda*eta := mul_nonneg hlambda.le heta
  have hsquare : (lambda*eta)^2 ≤ delta/cU := by
    nlinarith [Real.sqrt_nonneg (delta/cU),Real.sq_sqrt hratio]
  have hmul := mul_le_mul_of_nonneg_left hsquare hcU.le
  have hcancel : cU*(delta/cU)=delta := by field_simp
  rw [hcancel] at hmul
  exact hmul

end SafeLearning.CompleteCoreMPCNormBridge27

namespace SafeLearning.CompleteCoreMPCFirstSuccessor27
open SafeLearning.CompleteCoreMPCNormBridge27
open SafeLearning.CompleteCoreMPCLocalBootstrap27
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- Establish domain membership before invoking the conditional local quadratic
bound. The premises are the actual one-step Lipschitz assumption, a tightened
nominal successor, Assumption3, and the original continuity/locality clauses. -/
theorem actual_first_disturbed_successor_is_in_X_and_in_the_local_tracking_sublevel
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (H : Matrix J I ℝ)
    (f : EuclideanSpace ℝ I → (K → ℝ) → EuclideanSpace ℝ I)
    (U : Set (K → ℝ)) (lambda eta delta cU margin : ℝ)
    (hlambda : 0 < lambda) (heta : 0 ≤ eta) (hdelta : 0 < delta)
    (hcU : 0 < cU) (hmargin0 : 0 ≤ margin)
    (hsmall : eta ≤ lambda⁻¹ * Real.sqrt (delta/cU))
    (hmargin : ‖H‖ * (lambda*eta) ≤ margin)
    (hLipschitz : ∀ x ∈ {y : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => y i)) j ≤ 1},
      ∀ u ∈ U, ∀ d : K → ℝ, u+d ∈ U → ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖)
    (x : EuclideanSpace ℝ I) (u d vnext : K → ℝ)
    (hx : ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1)
    (hu : u ∈ U) (hud : u+d ∈ U) (hvnext : vnext ∈ U) (hd : ‖d‖ ≤ eta)
    (hnominal : ∀ j, (H *ᵥ (fun i => f x u i)) j ≤ 1-margin)
    (V : EuclideanSpace ℝ I → EuclideanSpace ℝ I → (K → ℝ) → ℝ)
    (hcontinuous : ∀ z ∈ {y : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => y i)) j ≤ 1},
      ∀ v ∈ U, ContinuousOn (fun y => V y z v)
        {y : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => y i)) j ≤ 1})
    (hzero : ∀ z ∈ {y : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => y i)) j ≤ 1},
      ∀ v ∈ U, V z z v=0)
    (hlocal : ∀ y ∈ {q : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => q i)) j ≤ 1},
      ∀ z ∈ {q : EuclideanSpace ℝ I | ∀ j, (H *ᵥ (fun i => q i)) j ≤ 1},
      ∀ v ∈ U, V y z v ≤ delta → V y z v ≤ cU * ‖y-z‖^2) :
    (∀ j, (H *ᵥ (fun i => f x (u+d) i)) j ≤ 1) ∧
    V (f x (u+d)) (f x u) vnext ≤ cU * (lambda*eta)^2 ∧
    V (f x (u+d)) (f x u) vnext ≤ delta := by
  let X : Set (EuclideanSpace ℝ I) := {y | ∀ j, (H *ᵥ (fun i => y i)) j ≤ 1}
  have herror : ‖f x (u+d)-f x u‖ ≤ lambda*eta :=
    actual_infinity_bounded_input_error_implies_the_euclidean_successor_radius
      f X U lambda eta hlambda.le hLipschitz x u d hx hu hud hd
  have hactual : f x (u+d) ∈ X :=
    actual_polytopic_tightening_covers_a_euclidean_state_perturbation
      H (f x u) (f x (u+d)) (lambda*eta) margin hnominal herror hmargin
  have hnominalX : f x u ∈ X := by
    intro j
    linarith [hnominal j]
  have hX : Convex ℝ X := by
    simpa only [sub_zero] using actual_polytopic_state_constraint_set_is_convex H 0
  have hbudget : cU*(lambda*eta)^2 ≤ delta :=
    actual_positive_lipschitz_assumption_three_implies_the_squared_local_budget
      lambda eta delta cU hlambda heta hdelta hcU hsmall
  have hsquare : ‖f x (u+d)-f x u‖^2 ≤ (lambda*eta)^2 := by
    nlinarith [norm_nonneg (f x (u+d)-f x u),mul_nonneg hlambda.le heta]
  have hquadratic := mul_le_mul_of_nonneg_left hsquare hcU.le
  have hlocalvalue := continuous_local_quadratic_state_bound_bootstraps_small_state_error
    X hX (fun y => V y (f x u) vnext) (f x u) (f x (u+d))
    hnominalX hactual delta cU hdelta hcU.le (hquadratic.trans hbudget)
    (hcontinuous (f x u) hnominalX vnext hvnext)
    (hzero (f x u) hnominalX vnext hvnext)
    (fun y hy hval => hlocal y hy (f x u) hnominalX vnext hvnext hval)
  exact ⟨hactual,hlocalvalue.trans hquadratic,(hlocalvalue.trans hquadratic).trans hbudget⟩
end SafeLearning.CompleteCoreMPCFirstSuccessor27
