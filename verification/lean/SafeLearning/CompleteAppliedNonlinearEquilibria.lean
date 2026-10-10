import SafeLearning.CompleteAppliedScalarODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedNonlinearEquilibria

def field (x : ℝ) : ℝ := -x+x^2
def sourceTrajectory (t : ℝ) : ℝ := 1/(1+9*Real.exp t)
def eulerStep (initial period : ℝ) : ℝ := initial+period*field initial

theorem actual_all_equilibria_and_true_derivative (x : ℝ) :
    (field x=0 ↔ x=0∨x=1) ∧ HasDerivAt field (-1+2*x) x := by
  constructor
  · have he : field x=x*(x-1) := by dsimp [field];ring
    rw [he,mul_eq_zero,sub_eq_zero]
  · convert (hasDerivAt_id x).neg.add ((hasDerivAt_id x).pow 2) using 1 <;>
      (try ext y) <;> simp [field] <;> ring

theorem actual_linearizations_and_exact_quadratic_remainders (perturbation : ℝ) :
    HasDerivAt field (-1) 0 ∧ HasDerivAt field 1 1 ∧
      field perturbation= -perturbation+perturbation^2 ∧
      field (1+perturbation)=perturbation+perturbation^2 := by
  refine ⟨?_,?_,rfl,?_⟩
  · simpa using (actual_all_equilibria_and_true_derivative 0).2
  · convert (actual_all_equilibria_and_true_derivative 1).2 using 1 <;> norm_num
  · dsimp [field];ring

theorem actual_zero_equilibrium_linearization_is_stable_and_attractive :
    CompleteAppliedScalarODE.lyapunovStable (-1) ∧
      ∀initial:ℝ,Tendsto (CompleteAppliedScalarODE.solution (-1) initial) atTop (𝓝 0) := by
  exact ⟨CompleteAppliedScalarODE.actual_nonpositive_rate_is_stable (-1) (by norm_num),
    (CompleteAppliedScalarODE.actual_linear_all_initial_attraction_iff (-1)).mpr (by norm_num)⟩

theorem actual_one_equilibrium_linearization_is_unstable :
    ¬CompleteAppliedScalarODE.lyapunovStable 1 :=
  CompleteAppliedScalarODE.actual_positive_rate_is_unstable 1 (by norm_num)

theorem actual_source_trajectory_initial_and_exact_ODE (t : ℝ) :
    sourceTrajectory 0=1/10 ∧ HasDerivAt sourceTrajectory (field (sourceTrajectory t)) t := by
  have hden : 1+9*Real.exp t≠0 := ne_of_gt (by positivity)
  constructor
  · norm_num [sourceTrajectory]
  · have hd := (Real.hasDerivAt_exp t).const_mul 9
    have h := (hasDerivAt_const t (1:ℝ)).div (hd.const_add 1) hden
    convert h using 1
    · rfl
    · dsimp [field,sourceTrajectory]
      field_simp
      ring

theorem actual_source_forward_euler_step : eulerStep (1/10) (1/5)=41/500 := by
  norm_num [eulerStep,field]

theorem actual_exponential_one_fifth_upper_enclosure : Real.exp (1/5:ℝ)<51/41 := by
  have hb := Real.exp_bound (x:=(1/5:ℝ)) (by norm_num) (n:=3) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb
  linarith [(abs_le.mp hb).2]

theorem actual_source_euler_step_is_strictly_below_the_true_solution :
    eulerStep (1/10) (1/5)<sourceTrajectory (1/5) ∧
      eulerStep (1/10) (1/5)≠sourceTrajectory (1/5) := by
  have hden : 0<1+9*Real.exp (1/5:ℝ) := by positivity
  have hlt : (41/500:ℝ)<sourceTrajectory (1/5) := by
    unfold sourceTrajectory
    apply (lt_div_iff₀ hden).mpr
    linarith [actual_exponential_one_fifth_upper_enclosure]
  rw [actual_source_forward_euler_step]
  exact ⟨hlt,ne_of_lt hlt⟩

theorem actual_source_rate_changes_along_the_true_trajectory :
    field (sourceTrajectory 0)≠field (sourceTrajectory (1/5)) := by
  have he := Real.exp_pos (1/5:ℝ)
  have hstrict : 1<Real.exp (1/5:ℝ) := by simpa using Real.exp_lt_exp.mpr (by norm_num : (0:ℝ)<1/5)
  have hxpositive : 0<sourceTrajectory (1/5) := by unfold sourceTrajectory;positivity
  have hxsmall : sourceTrajectory (1/5)<1/10 := by
    unfold sourceTrajectory
    apply (div_lt_iff₀ (by positivity : 0<1+9*Real.exp (1/5:ℝ))).mpr
    linarith
  have hz : sourceTrajectory 0=1/10 := (actual_source_trajectory_initial_and_exact_ODE 0).1
  rw [hz]
  dsimp [field]
  intro h
  nlinarith

theorem actual_source_true_trajectory_tends_to_zero :
    Tendsto sourceTrajectory atTop (𝓝 0) := by
  have hden : Tendsto (fun t:ℝ=>1+9*Real.exp t) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_exp_atTop.const_mul_atTop (by norm_num))
  change Tendsto (fun t:ℝ=>1/(1+9*Real.exp t)) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop hden

end SafeLearning.CompleteAppliedNonlinearEquilibria
