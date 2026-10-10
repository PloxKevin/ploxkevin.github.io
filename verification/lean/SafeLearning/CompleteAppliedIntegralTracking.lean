import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedIntegralTracking

abbrev State := Fin 2 → ℝ
def pOnlyInput (x : ℝ) : ℝ := (1/2)*(1-x)
def pOnlyStep (x : ℝ) : ℝ := (4/5)*x+pOnlyInput x+1/2
def pOnlyTrajectory (initial : ℝ) (n : ℕ) : ℝ :=
  10/7+(3/10:ℝ)^n*(initial-10/7)

def piInput (state : State) : ℝ := (7/10)*(1-state 0)+(1/5)*state 1
def piStep (state : State) : State :=
  ![(4/5)*state 0+piInput state+1/2,state 1+1-state 0]
def loopMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1/10,1/5;-1,1]
def equilibrium : State := ![1,-3/2]
def firstMode (initial : State) : ℝ := 5*(initial 1+3/2)-10*(initial 0-1)
def secondMode (initial : State) : ℝ := 10*(initial 0-1)-4*(initial 1+3/2)
def piTrajectory (initial : State) (n : ℕ) : State :=
  ![1+(2/5)*firstMode initial*(3/5:ℝ)^n+(1/2)*secondMode initial*(1/2:ℝ)^n,
    -3/2+firstMode initial*(3/5:ℝ)^n+secondMode initial*(1/2:ℝ)^n]

theorem actual_P_only_equilibrium_and_error (x : ℝ) :
    (pOnlyStep x=x ↔ x=10/7) ∧ 1-(10/7:ℝ)=-3/7 := by
  dsimp [pOnlyStep,pOnlyInput]
  constructor
  · constructor <;> intro h <;> linarith
  · norm_num

theorem actual_P_only_trajectory_initial_recurrence_and_all_initial_limit
    (initial : ℝ) : pOnlyTrajectory initial 0=initial ∧
    (∀n,pOnlyTrajectory initial (n+1)=pOnlyStep (pOnlyTrajectory initial n)) ∧
    Tendsto (pOnlyTrajectory initial) atTop (𝓝 (10/7)) := by
  refine ⟨by simp [pOnlyTrajectory],?_,?_⟩
  · intro n
    dsimp [pOnlyTrajectory,pOnlyStep,pOnlyInput]
    rw [pow_succ]
    ring
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤3/10) (by norm_num : (3/10:ℝ)<1)).mul_const (initial-10/7)
    change Tendsto (fun n : ℕ => 10/7+(3/10:ℝ)^n*(initial-10/7)) atTop (𝓝 (10/7))
    simpa only [zero_mul,add_zero] using (tendsto_const_nhds (x:=(10/7:ℝ))).add ht

theorem actual_every_P_only_recurrence_has_that_trajectory
    (x : ℕ → ℝ) (initial : ℝ) (h0 : x 0=initial)
    (hstep : ∀n,x (n+1)=pOnlyStep (x n)) : ∀n,x n=pOnlyTrajectory initial n := by
  intro n
  induction n with
  | zero => rw [h0,(actual_P_only_trajectory_initial_recurrence_and_all_initial_limit initial).1]
  | succ n ih =>
    rw [hstep,ih,(actual_P_only_trajectory_initial_recurrence_and_all_initial_limit initial).2.1]

theorem actual_PI_input_is_the_source_proportional_plus_updated_integral
    (state : State) :
    (1/2)*(1-state 0)+(1/5)*(state 1+(1-state 0))=piInput state := by
  dsimp [piInput]
  ring

theorem actual_PI_affine_step_and_centered_matrix (state : State) :
    piStep state=loopMatrix*ᵥstate+![6/5,1] ∧
    piStep state-equilibrium=loopMatrix*ᵥ(state-equilibrium) := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [piStep,piInput,loopMatrix,equilibrium,dotProduct,Fin.sum_univ_two,vecHead,vecTail] <;> ring

theorem actual_PI_unique_equilibrium_and_learned_input (state : State) :
    (piStep state=state ↔ state=equilibrium) ∧ piInput equilibrium=-3/10 := by
  constructor
  · constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [piStep,piInput] at h0 h1
      ext i
      fin_cases i <;> simp [equilibrium] <;> linarith
    · intro h
      rw [h]
      ext i
      fin_cases i <;> norm_num [piStep,piInput,equilibrium]
  · norm_num [piInput,equilibrium]

theorem actual_PI_source_trace_determinant_and_official_complex_spectrum (z : ℂ) :
    loopMatrix.trace=11/10 ∧ loopMatrix.det=3/10 ∧
    (z∈spectrum ℂ (loopMatrix.map Complex.ofReal) ↔ z=(3/5:ℂ) ∨ z=(1/2:ℂ)) := by
  refine ⟨by norm_num [loopMatrix,Matrix.trace,Fin.sum_univ_two],
    by norm_num [loopMatrix,Matrix.det_fin_two],?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_fin_two]
  have he : Polynomial.eval z
      (Polynomial.X^2-Polynomial.C ((loopMatrix.map Complex.ofReal).trace)*Polynomial.X+
        Polynomial.C ((loopMatrix.map Complex.ofReal).det))=(z-3/5)*(z-1/2) := by
    simp [loopMatrix,Matrix.trace,Fin.sum_univ_two,Matrix.det_fin_two]
    ring
  change _=0 ↔ _
  rw [he,mul_eq_zero,sub_eq_zero,sub_eq_zero]

theorem actual_PI_trajectory_initial_and_source_recurrence (initial : State) :
    piTrajectory initial 0=initial ∧
    ∀n,piTrajectory initial (n+1)=piStep (piTrajectory initial n) := by
  constructor
  · ext i
    fin_cases i <;> simp [piTrajectory,firstMode,secondMode] <;> ring
  · intro n
    ext i
    fin_cases i <;> simp [piTrajectory,piStep,piInput,pow_succ] <;> ring

theorem actual_every_PI_recurrence_is_the_constructed_trajectory
    (x : ℕ → State) (initial : State) (h0 : x 0=initial)
    (hstep : ∀n,x (n+1)=piStep (x n)) : ∀n,x n=piTrajectory initial n := by
  intro n
  induction n with
  | zero => rw [h0,(actual_PI_trajectory_initial_and_source_recurrence initial).1]
  | succ n ih => rw [hstep,ih,(actual_PI_trajectory_initial_and_source_recurrence initial).2]

theorem actual_PI_every_initial_state_converges_to_zero_error_equilibrium
    (initial : State) : Tendsto (piTrajectory initial) atTop (𝓝 equilibrium) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤3/5) (by norm_num : (3/5:ℝ)<1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · simpa [piTrajectory,equilibrium] using
      ((tendsto_const_nhds (x:=(1:ℝ))).add (h1.const_mul ((2/5)*firstMode initial))).add
        (h2.const_mul ((1/2)*secondMode initial))
  · simpa [piTrajectory,equilibrium] using
      ((tendsto_const_nhds (x:=(-3/2:ℝ))).add (h1.const_mul (firstMode initial))).add
        (h2.const_mul (secondMode initial))

theorem actual_every_source_PI_recurrence_converges
    (x : ℕ → State) (hstep : ∀n,x (n+1)=piStep (x n)) :
    Tendsto x atTop (𝓝 equilibrium) := by
  have he := actual_every_PI_recurrence_is_the_constructed_trajectory x (x 0) rfl hstep
  exact (actual_PI_every_initial_state_converges_to_zero_error_equilibrium (x 0)).congr
    (fun n => (he n).symm)

end SafeLearning.CompleteAppliedIntegralTracking
