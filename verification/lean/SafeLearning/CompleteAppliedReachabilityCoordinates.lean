import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedReachabilityCoordinates

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def dynamics : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1/2,1/4]
def inputColumn : Fin 2→ℝ := ![1,0]
def step (x : E) (u : ℝ) : E :=
  WithLp.toLp 2 (dynamics*ᵥ (x:Fin 2→ℝ)+u•inputColumn)
def controllability : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j=>if j=0 then inputColumn i else (dynamics*ᵥ inputColumn) i

theorem actual_matrix_input_and_controllability :
    dynamics*ᵥ inputColumn=![1/2,0] ∧
    controllability=!![1,1/2;0,0] := by
  constructor
  · ext i;fin_cases i <;> norm_num [dynamics,inputColumn]
  · ext i j;fin_cases i <;> fin_cases j <;> norm_num [controllability,dynamics,inputColumn]

theorem actual_controllability_matrix_rank_is_one : controllability.rank=1 := by
  let V : Matrix (Fin 2) (Fin 2) ℝ := !![1,1/2;0,1]
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
  have hv : V.det≠0 := by norm_num [V,Matrix.det_fin_two]
  have he : controllability=D*V := by
    rw [actual_matrix_input_and_controllability.2]
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [D,V]
  rw [he,Matrix.rank_mul_eq_left_of_det_ne_zero V D hv]
  norm_num [D,Matrix.rank_diagonal,Fintype.card_subtype,Finset.univ_fin2,Finset.filter_insert]

theorem actual_state_input_update_coordinates (x : E) (u : ℝ) :
    step x u=point (x 0/2+u) (x 1/4) := by
  ext i;fin_cases i <;>
    simp [step,point,dynamics,inputColumn,div_eq_mul_inv,mul_comm]

theorem actual_second_coordinate_for_every_input_sequence
    (x : ℕ→E) (u : ℕ→ℝ) (hnext : ∀n,x (n+1)=step (x n) (u n)) :
    ∀n,x n 1=(1/4:ℝ)^n*x 0 1 := by
  intro n;induction n with
  | zero => simp
  | succ n ih =>
    rw [hnext,actual_state_input_update_coordinates]
    simp only [point,Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [ih,pow_succ]
    ring

def reachableFromZero : Set E :=
  {target | ∃n:ℕ,∃x:ℕ→E,∃u:ℕ→ℝ,x 0=0∧
    (∀t,x (t+1)=step (x t) (u t))∧x n=target}
def constantInputTrajectory (a : ℝ) : ℕ→E := Nat.rec 0 (fun _ x=>step x a)

theorem actual_every_first_axis_point_is_reachable (a : ℝ) : point a 0∈reachableFromZero := by
  refine ⟨1,constantInputTrajectory a,fun _=>a,rfl,fun _=>rfl,?_⟩
  change step 0 a=point a 0
  rw [actual_state_input_update_coordinates]
  simp

theorem actual_reachable_set_is_exactly_the_first_coordinate_axis :
    reachableFromZero={target:E | target 1=0} := by
  ext target
  constructor
  · rintro ⟨n,x,u,h0,hn,ht⟩
    have hs := actual_second_coordinate_for_every_input_sequence x u hn n
    rw [h0,ht] at hs
    simpa using hs
  · intro ht
    have he : target=point (target 0) 0 := by
      ext i;fin_cases i
      · rfl
      · simpa [point] using ht
    rw [he]
    exact actual_every_first_axis_point_is_reachable _

theorem actual_nonzero_second_coordinate_is_unreachable (target : E) (ht : target 1≠0) :
    target∉reachableFromZero := by
  rw [actual_reachable_set_is_exactly_the_first_coordinate_axis]
  exact ht

theorem actual_source_system_is_not_controllable_from_zero :
    ¬∀target:E,target∈reachableFromZero := by
  intro h
  exact actual_nonzero_second_coordinate_is_unreachable (point 0 1) (by norm_num [point])
    (h (point 0 1))

def zeroInputTrajectory (initial : E) (n : ℕ) : E :=
  point ((1/2:ℝ)^n*initial 0) ((1/4:ℝ)^n*initial 1)

theorem actual_zero_input_trajectory_initial_and_recurrence (initial : E) :
    zeroInputTrajectory initial 0=initial ∧
    ∀n,zeroInputTrajectory initial (n+1)=step (zeroInputTrajectory initial n) 0 := by
  constructor
  · ext i;fin_cases i <;> simp [zeroInputTrajectory,point]
  · intro n;rw [actual_state_input_update_coordinates]
    ext i;fin_cases i <;> simp [zeroInputTrajectory,point,pow_succ] <;> ring

theorem actual_stable_unforced_dynamics_have_every_initial_trajectory_converging
    (initial : E) : Tendsto (zeroInputTrajectory initial) atTop (𝓝 0) := by
  have hhalf := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_const (initial 0)
  have hquarter := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4)
    (by norm_num : (1/4:ℝ)<1)).mul_const (initial 1)
  have hp : Tendsto (fun n:ℕ=>![(1/2:ℝ)^n*initial 0,(1/4:ℝ)^n*initial 1])
      atTop (𝓝 (0:Fin 2→ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i;fin_cases i
    · simpa using hhalf
    · simpa using hquarter
  change Tendsto (fun n : ℕ => WithLp.toLp 2 ![(1/2:ℝ)^n*initial 0,(1/4:ℝ)^n*initial 1]) atTop (𝓝 (WithLp.toLp 2 (0:Fin 2→ℝ)))
  exact (PiLp.continuous_toLp (p:=2) (fun _ : Fin 2 => ℝ)).continuousAt.tendsto.comp hp

end SafeLearning.CompleteAppliedReachabilityCoordinates
