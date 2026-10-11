import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

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
