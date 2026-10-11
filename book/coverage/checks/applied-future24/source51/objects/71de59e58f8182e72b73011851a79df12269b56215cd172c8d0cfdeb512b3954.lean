import SafeLearning.CompleteMonitoringTrapping22
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteMonitoringDeficit22

def projectedStep (η price c r : ℝ) : ℝ := max 0 (price+η*(c-r))
def multiplier (η c : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => projectedStep η (multiplier η c r n) c (r n)

theorem actual_projected_dual_step_increases_on_a_visit_deficit
    (η price c r : ℝ) (hη : 0 < η) (hprice : 0 ≤ price) (hdef : r < c) :
    projectedStep η price c r=price+η*(c-r) ∧ price<projectedStep η price c r := by
  have hδ : 0 < η*(c-r) := mul_pos hη (sub_pos.mpr hdef)
  rw [projectedStep,max_eq_right (by linarith)]
  exact ⟨rfl,by linarith⟩

theorem actual_projected_dual_step_decreases_on_surplus_until_zero
    (η price c r : ℝ) (hη : 0 < η) (hprice : 0 ≤ price) (hsur : c < r) :
    0 ≤ projectedStep η price c r ∧ projectedStep η price c r ≤ price ∧
    (0 < price → projectedStep η price c r<price) := by
  have hδ : η*(c-r)<0 := mul_neg_of_pos_of_neg hη (sub_neg.mpr hsur)
  refine ⟨le_max_left _ _,max_le hprice (by linarith),?_⟩
  intro hp
  exact max_lt hp (by linarith)

theorem actual_multiplier_is_nonnegative (η c : ℝ) (r : ℕ → ℝ) (N : ℕ) :
    0 ≤ multiplier η c r N := by cases N <;> simp [multiplier,projectedStep]

theorem actual_dual_memory_telescope_without_active_projection
    (η c : ℝ) (r : ℕ → ℝ)
    (h : ∀ n, 0 ≤ multiplier η c r n+η*(c-r n)) (N : ℕ) :
    multiplier η c r N=η*((N:ℝ)*c-∑ n ∈ Finset.range N, r n) := by
  induction N with
  | zero => simp [multiplier]
  | succ N ih =>
    rw [multiplier,projectedStep,max_eq_right (h N),ih,Finset.sum_range_succ]
    push_cast
    ring

theorem actual_projection_gives_the_cumulative_deficit_lower_bound
    (η c : ℝ) (r : ℕ → ℝ) (hη : 0 ≤ η) (N : ℕ) :
    η*((N:ℝ)*c-∑ n ∈ Finset.range N, r n)  ≤  multiplier η c r N := by
  induction N with
  | zero => simp [multiplier]
  | succ N ih =>
    have h:=le_max_right (0:ℝ) (multiplier η c r N+η*(c-r N))
    change _ ≤ max 0 (multiplier η c r N+η*(c-r N))
    rw [Finset.sum_range_succ]
    push_cast
    linarith

theorem actual_running_average_constraint_from_sublinear_dual_memory
    (η c v : ℝ) (r : ℕ → ℝ) (hη : 0 < η)
    (hmem : Tendsto (fun N => multiplier η c r N/(N:ℝ)) atTop (𝓝 0))
    (havg : Tendsto (fun N => (∑ n ∈ Finset.range N, r n)/(N:ℝ)) atTop (𝓝 v)) : c ≤ v := by
  have hb : (fun N : ℕ => c-(∑ n ∈ Finset.range N, r n)/(N:ℝ))  ≤ᶠ[atTop]
      (fun N => (multiplier η c r N/(N:ℝ))/η) := by
    filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
    have hn : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hh:=actual_projection_gives_the_cumulative_deficit_lower_bound η c r hη.le N
    apply (le_div_iff₀ hη).mpr
    apply (le_div_iff₀ hn).mpr
    nlinarith [div_mul_cancel₀ (∑ n ∈ Finset.range N,r n) (ne_of_gt hn)]
  have hl := (tendsto_const_nhds (x:=c)).sub havg
  have hr := hmem.div_const η
  have hh:=le_of_tendsto_of_tendsto hl hr hb
  have hh2 : c-v ≤ 0 := by simpa using hh
  exact sub_nonpos.mp hh2

def greedyStay (priceown priceother : ℝ) : Bool := decide (max 1 priceother<priceown)

theorem actual_multiplier_augmentation_distinguishes_actions_at_the_same_physical_state :
    greedyStay 2 0=true ∧ greedyStay 0 2=false ∧
    ¬∃ physicalAction : Fin 3 → Bool, physicalAction 1=greedyStay 2 0 ∧ physicalAction 1=greedyStay 0 2 := by
  norm_num [greedyStay]

theorem actual_monitoring_epoch_violation_vector_has_a_uniform_squared_norm_bound
    (s : Fin 3) :
    (if s=1 then (2/3:ℝ) else -1/3)^2+(if s=2 then (2/3:ℝ) else -1/3)^2  ≤  5/9 := by
  fin_cases s <;> norm_num

end SafeLearning.CompleteMonitoringDeficit22
