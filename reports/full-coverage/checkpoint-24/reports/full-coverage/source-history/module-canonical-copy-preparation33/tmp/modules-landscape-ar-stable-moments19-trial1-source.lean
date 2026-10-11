import SafeLearning.CompleteModulesLandscapeARGaussianAlgebra
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesLandscapeARStableMoments
open CompleteModulesLandscapeARGaussianAlgebra

theorem actual_source_stability_range_gives_strict_unit_absolute_multiplier
    (k : ℝ) (hk:0<k) (hk2:k<2) : |1-k|<1 := by
  rw [abs_lt]
  constructor <;> linarith

theorem actual_true_variance_has_the_printed_closed_geometric_formula
    (k sigma : ℝ) (hk:0<k) (hk2:k<2) (t : ℕ) :
    trueVariance k sigma t=sigma^2*(1-(1-k)^(2*t))/(k*(2-k)) := by
  have hd : k*(2-k)≠0 := ne_of_gt (mul_pos hk (by linarith))
  have he : 1-(1-k)^2=k*(2-k) := by ring
  have hs : (∑i∈Finset.range t,(1-k)^(2*i))=∑i∈Finset.range t,((1-k)^2)^i := by
    simp only [pow_mul]
  unfold trueVariance
  apply (eq_div_iff hd).mpr
  rw [hs]
  calc
    sigma^2*(∑i∈Finset.range t,((1-k)^2)^i)*(k*(2-k))=
        sigma^2*((∑i∈Finset.range t,((1-k)^2)^i)*(1-(1-k)^2)) := by rw [he];ring
    _ =sigma^2*(1-((1-k)^2)^t) := by rw [geom_sum_mul_neg]
    _ =sigma^2*(1-(1-k)^(2*t)) := by rw [pow_mul]

theorem actual_state_mean_converges_to_the_goal_for_every_stable_source_gain
    (k goal : ℝ) (hk:0<k) (hk2:k<2) :
    Tendsto (trueMean k goal) atTop (𝓝 goal) := by
  have hp : Tendsto (fun n:ℕ=>(1-k)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr
      (actual_source_stability_range_gives_strict_unit_absolute_multiplier k hk hk2)
  simpa [trueMean] using (tendsto_const_nhds.sub hp).const_mul goal

theorem actual_state_variance_converges_to_the_printed_stationary_variance
    (k sigma : ℝ) (hk:0<k) (hk2:k<2) :
    Tendsto (trueVariance k sigma) atTop (𝓝 (sigma^2/(k*(2-k)))) := by
  have hq : (1-k)^2<1 := by nlinarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (1-k)) hq
  have he : trueVariance k sigma=
      (fun n:ℕ=>sigma^2*(1-((1-k)^2)^n)/(k*(2-k))) := by
    funext n
    rw [actual_true_variance_has_the_printed_closed_geometric_formula k sigma hk hk2 n,pow_mul]
  rw [he]
  simpa using ((tendsto_const_nhds.sub hp).const_mul (sigma^2)).div_const (k*(2-k))

end SafeLearning.CompleteModulesLandscapeARStableMoments
