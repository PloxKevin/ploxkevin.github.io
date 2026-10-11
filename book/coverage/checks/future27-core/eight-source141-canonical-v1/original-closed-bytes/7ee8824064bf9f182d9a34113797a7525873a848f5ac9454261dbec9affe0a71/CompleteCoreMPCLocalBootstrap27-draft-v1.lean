import Mathlib.Topology.Order.IntermediateValue
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
