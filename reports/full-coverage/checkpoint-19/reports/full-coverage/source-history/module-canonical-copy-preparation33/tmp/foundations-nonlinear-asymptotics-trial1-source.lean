import SafeLearning.CompleteFoundationsNonlinearDecreasingModel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace SafeLearning.CompleteFoundationsNonlinearAsymptotics
open CompleteFoundationsNonlinearDecreasingModel

def reciprocalSquare (n : ℕ) : ℝ := 1/(sourceOrbit n)^2

theorem actual_reciprocal_square_recurrence (n : ℕ) :
    reciprocalSquare (n+1)=reciprocalSquare n+2+(sourceOrbit n)^2 := by
  have hx : sourceOrbit n ≠ 0 := (actual_source_orbit_is_positive_at_every_natural_time n).ne'
  have hd : 1+(sourceOrbit n)^2 ≠ 0 := ne_of_gt (by positivity)
  unfold reciprocalSquare
  rw [sourceOrbit,sourceMap]
  field_simp
  <;> ring

theorem actual_reciprocal_square_is_the_true_telescoping_sum (n : ℕ) :
    reciprocalSquare n=1+2*(n:ℝ)+∑ k ∈ Finset.range n, (sourceOrbit k)^2 := by
  induction n with
  | zero => norm_num [reciprocalSquare,sourceOrbit]
  | succ n ih =>
    rw [actual_reciprocal_square_recurrence,ih,Finset.sum_range_succ]
    push_cast
    ring

theorem actual_reciprocal_square_divided_by_time_tends_to_two :
    Tendsto (fun n : ℕ => reciprocalSquare n/(n:ℝ)) atTop (𝓝 2) := by
  have hsq : Tendsto (fun n => (sourceOrbit n)^2) atTop (𝓝 0) := by
    simpa [sourceValue] using actual_source_values_strictly_decrease_and_converge_to_zero.2.2
  have hc := hsq.cesaro
  have hi : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hl := (hi.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2))).add hc
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnon : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [actual_reciprocal_square_is_the_true_telescoping_sum]
  field_simp
  ring

theorem actual_twice_time_square_state_tends_to_one :
    Tendsto (fun n : ℕ => 2*(n:ℝ)*(sourceOrbit n)^2) atTop (𝓝 1) := by
  have hd := actual_reciprocal_square_divided_by_time_tends_to_two
  have hi := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)).div hd (by norm_num)
  have hl : Tendsto (fun n : ℕ => (2:ℝ)/(reciprocalSquare n/(n:ℝ))) atTop (𝓝 1) := by
    simpa using hi
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnon : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hx : sourceOrbit n ≠ 0 := (actual_source_orbit_is_positive_at_every_natural_time n).ne'
  unfold reciprocalSquare
  field_simp
  <;> ring

theorem actual_state_to_inverse_square_root_scale_ratio_tends_to_one :
    Tendsto (fun n : ℕ => sourceOrbit n*Real.sqrt (2*(n:ℝ))) atTop (𝓝 1) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp actual_twice_time_square_state_tends_to_one
  have hl : Tendsto (fun n : ℕ => Real.sqrt (2*(n:ℝ)*(sourceOrbit n)^2)) atTop (𝓝 1) := by
    simpa using hs
  convert hl using 1
  ext n
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2*(n:ℝ)),
    Real.sqrt_sq (actual_source_orbit_is_positive_at_every_natural_time n).le]
  ring

theorem actual_literal_positive_time_asymptotic_ratio :
    Tendsto (fun n : ℕ => sourceOrbit n/(1/Real.sqrt (2*(n:ℝ)))) atTop (𝓝 1) := by
  simpa only [div_one_div] using actual_state_to_inverse_square_root_scale_ratio_tends_to_one

end SafeLearning.CompleteFoundationsNonlinearAsymptotics
