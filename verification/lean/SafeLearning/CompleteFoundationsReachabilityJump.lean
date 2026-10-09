import SafeLearning.CompleteFoundationsFiniteReachability
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteFoundationsReachabilityJump
open SafeLearning.CompleteFoundationsFiniteReachability Filter
open scoped Topology

theorem actual_threshold_first_three :
    sourceGrow (2/5) {0}={0,1} ∧ sourceGrow (2/5) {0,1}={0,1,2} ∧
    sourceGrow (2/5) {0,1,2}={0,1,2,3} := by
  repeat' constructor
  all_goals ext x;fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]

theorem actual_gateway_reachable_at_threshold : (3:Fin 9)∈sourceClosure (2/5) := by
  refine ⟨3,?_⟩
  simp only [sourceIteration,Function.iterate_succ_apply,Function.iterate_zero_apply]
  rw [actual_threshold_first_three.1,actual_threshold_first_three.2.1,actual_threshold_first_three.2.2]
  decide

theorem actual_right_neighborhood_fixed_set (epsilon : ℝ) (hl : 2/5<epsilon) (hu : epsilon≤1/2) :
    sourceGrow epsilon {0,1,2}={0,1,2} := by
  ext x
  fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]
  all_goals try push Not
  all_goals
    constructor
    · linarith
    · constructor <;> linarith

theorem actual_all_time_right_neighborhood_invariant (epsilon : ℝ)
    (hl : 2/5<epsilon) (hu : epsilon≤1/2) (n : ℕ) :
    sourceIteration epsilon n⊆{0,1,2} := by
  induction n with
  | zero => change ({0}:Finset (Fin 9))⊆_;decide
  | succ n ih =>
    rw [actual_iteration_succ]
    have h := actual_grow_monotone fitness distance epsilon ih
    change sourceGrow epsilon (sourceIteration epsilon n)⊆sourceGrow epsilon {0,1,2} at h
    rw [actual_right_neighborhood_fixed_set epsilon hl hu] at h
    exact h

theorem actual_gateway_lost_to_right (epsilon : ℝ) (hl : 2/5<epsilon) (hu : epsilon≤1/2) :
    (3:Fin 9)∉sourceClosure epsilon := by
  rintro ⟨n,hn⟩
  have h := actual_all_time_right_neighborhood_invariant epsilon hl hu n hn
  norm_num at h

def gatewayIndicator (epsilon : ℝ) : ℝ := by
  classical
  exact if (3:Fin 9)∈sourceClosure epsilon then 1 else 0
def nearbyError (n : ℕ) : ℝ := 2/5+(1/10)/(n+1)

theorem actual_nearby_errors (n : ℕ) : 2/5<nearbyError n ∧ nearbyError n≤1/2 := by
  have hn : (1:ℝ)≤n+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : (0:ℝ)<n+1 := by positivity
  have hh : (1/10:ℝ)/(n+1)≤1/10 := (div_le_iff₀ hp).mpr (by nlinarith)
  have hz : (0:ℝ)<(1/10:ℝ)/(n+1) := by positivity
  constructor <;> dsimp [nearbyError] <;> linarith

theorem actual_nearby_error_limit : Tendsto nearbyError atTop (𝓝 (2/5)) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have ht := h.const_mul (1/10:ℝ)
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2/5:ℝ)) atTop (𝓝 (2/5))).add ht using 1
  · funext n;dsimp [nearbyError];ring
  · norm_num

theorem actual_gateway_jump_values : gatewayIndicator (2/5)=1 ∧
    ∀ n,gatewayIndicator (nearbyError n)=0 := by
  constructor
  · simp [gatewayIndicator,actual_gateway_reachable_at_threshold]
  · intro n
    simp [gatewayIndicator,actual_gateway_lost_to_right _ (actual_nearby_errors n).1 (actual_nearby_errors n).2]

theorem actual_reachability_indicator_is_discontinuous : ¬ContinuousAt gatewayIndicator (2/5) := by
  intro hc
  have h := hc.tendsto.comp actual_nearby_error_limit
  have hz : Tendsto (fun n=>gatewayIndicator (nearbyError n)) atTop (𝓝 (0:ℝ)) := by
    simpa only [actual_gateway_jump_values.2] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
  rw [actual_gateway_jump_values.1] at h
  have hh := tendsto_nhds_unique h hz
  norm_num at hh

end SafeLearning.CompleteFoundationsReachabilityJump
