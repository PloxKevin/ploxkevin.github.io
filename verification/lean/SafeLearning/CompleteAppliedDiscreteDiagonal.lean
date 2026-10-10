import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedDiscreteDiagonal

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def dynamics : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,0;0,-6/5]
def step (x : E) : E := WithLp.toLp 2 (dynamics *ᵥ (x : Fin 2 → ℝ))
def trajectory (initial : E) (n : ℕ) : E :=
  point ((1/2:ℝ)^n*initial 0) ((-6/5:ℝ)^n*initial 1)

theorem actual_source_matrix_action (x : E) :
    step x=point (x 0/2) (-6/5*x 1) := by
  ext i;fin_cases i <;>
    simp [step,point,dynamics,dotProduct,Fin.sum_univ_two,div_eq_mul_inv,mul_comm]

theorem actual_trajectory_initial_and_recurrence (initial : E) :
    trajectory initial 0=initial ∧
    ∀n,trajectory initial (n+1)=step (trajectory initial n) := by
  constructor
  · ext i;fin_cases i <;> simp [trajectory,point]
  · intro n;rw [actual_source_matrix_action]
    ext i;fin_cases i <;> simp [trajectory,point,pow_succ] <;> ring

theorem actual_every_source_recurrence_is_the_constructed_trajectory
    (initial : E) (x : ℕ→E) (h0 : x 0=initial)
    (hnext : ∀n,x (n+1)=step (x n)) : ∀n,x n=trajectory initial n := by
  intro n;induction n with
  | zero => rw [h0,(actual_trajectory_initial_and_recurrence initial).1]
  | succ n ih => rw [hnext,ih,(actual_trajectory_initial_and_recurrence initial).2]

theorem actual_source_initial_and_first_two_steps :
    trajectory (point 2 1) 0=point 2 1 ∧
    trajectory (point 2 1) 1=point 1 (-6/5) ∧
    trajectory (point 2 1) 2=point (1/2) (36/25) := by
  constructor
  · exact (actual_trajectory_initial_and_recurrence (point 2 1)).1
  constructor <;> ext i <;> fin_cases i <;> norm_num [trajectory,point]

theorem actual_second_coordinate_magnitude (initial : E) (n : ℕ) :
    |trajectory initial n 1|=(6/5:ℝ)^n*|initial 1| := by
  simp only [trajectory,point,Matrix.cons_val_one]
  norm_num

theorem actual_second_coordinate_alternates_for_every_nonzero_initial
    (initial : E) (h : initial 1≠0) (n : ℕ) :
    trajectory initial (n+1) 1*trajectory initial n 1<0 := by
  have hnonzero : trajectory initial n 1≠0 := by
    simp [trajectory,point,h]
  have hs : 0<(trajectory initial n 1)^2 := sq_pos_of_ne_zero hnonzero
  have he : trajectory initial (n+1) 1=(-6/5:ℝ)*trajectory initial n 1 := by
    simp [trajectory,point,pow_succ];ring
  rw [he]
  nlinarith

theorem actual_nonzero_second_coordinate_grows_without_bound
    (initial : E) (h : initial 1≠0) :
    Tendsto (fun n : ℕ=>|trajectory initial n 1|) atTop atTop := by
  simp_rw [actual_second_coordinate_magnitude]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<6/5)).atTop_mul_const
    (abs_pos.mpr h)

theorem actual_zero_is_an_equilibrium : step 0=0 := by
  rw [actual_source_matrix_action]
  ext i;fin_cases i <;> simp [point]

theorem actual_norm_of_second_axis (b : ℝ) : ‖point 0 b‖=|b| := by
  have hs : ‖point 0 b‖^2=b^2 := by
    simpa [point,Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (point 0 b)
  have ha : |b|^2=b^2 := sq_abs b
  nlinarith [norm_nonneg (point 0 b),abs_nonneg b]

def originLyapunovStable : Prop :=
  ∀ε:ℝ,0<ε→∃δ:ℝ,0<δ∧∀initial:E,‖initial‖<δ→∀n:ℕ,‖trajectory initial n‖<ε

theorem actual_arbitrarily_small_initial_states_leave_the_unit_ball
    (δ : ℝ) (hδ : 0<δ) :
    ∃initial:E,‖initial‖<δ∧∃n:ℕ,1<‖trajectory initial n‖ := by
  let initial : E := point 0 (δ/2)
  have hb : 0<δ/2 := by linarith
  refine ⟨initial,?_,?_⟩
  · rw [actual_norm_of_second_axis,abs_of_pos hb];linarith
  · obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2/δ) (by norm_num : (1:ℝ)<6/5)
    refine ⟨n,?_⟩
    have hg : 1<(6/5:ℝ)^n*(δ/2) := by
      have hh := mul_lt_mul_of_pos_right hn hb
      have he : (2/δ)*(δ/2)=1 := by field_simp
      rw [he] at hh
      exact hh
    have hc : |trajectory initial n 1|=(6/5:ℝ)^n*(δ/2) := by
      rw [actual_second_coordinate_magnitude]
      simp [initial,point,abs_of_pos hb]
    have bound : |trajectory initial n 1|≤‖trajectory initial n‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (trajectory initial n) (1:Fin 2)
    rw [hc] at bound
    exact lt_of_lt_of_le hg bound

theorem actual_discrete_source_origin_is_not_lyapunov_stable : ¬originLyapunovStable := by
  intro h
  obtain ⟨δ,hδ,hs⟩ := h 1 (by norm_num)
  obtain ⟨initial,hi,n,hn⟩ := actual_arbitrarily_small_initial_states_leave_the_unit_ball δ hδ
  exact (not_lt.mpr hn.le) (hs initial hi n)

def complexDynamics : Matrix (Fin 2) (Fin 2) ℂ := dynamics.map Complex.ofReal

theorem actual_all_complex_eigenvalues (z : ℂ) :
    z∈spectrum ℂ complexDynamics ↔ z=(1/2:ℂ)∨z=(-6/5:ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_fin_two]
  have he : Polynomial.eval z
      (Polynomial.X^2-Polynomial.C (Matrix.trace complexDynamics)*Polynomial.X+
        Polynomial.C (Matrix.det complexDynamics))=(z-1/2)*(z+6/5) := by
    norm_num [complexDynamics,dynamics,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
    ring
  change Polynomial.eval z _=0 ↔ _
  rw [he]
  simp [mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg,neg_div]

theorem actual_negative_source_eigenvalue_has_magnitude_larger_than_one :
    ‖(-6/5:ℂ)‖=6/5 ∧ (1:ℝ)<6/5 := by norm_num

end SafeLearning.CompleteAppliedDiscreteDiagonal
