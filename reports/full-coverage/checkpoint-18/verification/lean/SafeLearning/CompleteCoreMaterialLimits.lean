import SafeLearning.CompleteLyapunovCounterexample
import SafeLearning.CoreModules

namespace SafeLearning.CompleteCoreMaterialLimits

noncomputable section
open Set Filter
open scoped Topology

theorem barrier_nominal_objective_minimal (u : ℝ) :
    (1 / 2 : ℝ) * ((-3 : ℝ) + 3)^2 ≤ (1 / 2 : ℝ) * (u + 3)^2 := by
  nlinarith [sq_nonneg (u + 3)]

theorem barrier_nominal_objective_unique (u : ℝ) :
    (1 / 2 : ℝ) * (u + 3)^2 = (1 / 2 : ℝ) * ((-3 : ℝ) + 3)^2 ↔ u = -3 := by
  constructor
  · intro h
    have hz : (u + 3)^2 = 0 := by nlinarith
    have hu : u + 3 = 0 := sq_eq_zero_iff.mp hz
    linarith
  · rintro rfl
    rfl

theorem actual_increment_right_limit_at_one :
    Tendsto SafeLearning.CompleteLyapunovCounterexample.increment
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt (fun x : ℝ => ((1 + x) / 2)^2 - x^2) 1 := by
    fun_prop
  have ht : Tendsto (fun x : ℝ => ((1 + x) / 2)^2 - x^2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < x := hx
  simp only [SafeLearning.CompleteLyapunovCounterexample.increment,
    SafeLearning.CompleteLyapunovCounterexample.badMap, if_neg (not_le.mpr hx')]

end
end SafeLearning.CompleteCoreMaterialLimits
