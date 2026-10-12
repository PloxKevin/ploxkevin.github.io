import SafeLearning.CompleteModulesDynamics
import SafeLearning.CompleteModulesBook
import SafeLearning.CompleteFoundationsNormDuality
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped BigOperators

namespace SafeLearning.CompleteModulesDelayedSquareWhole30

abbrev State := Fin 2 → ℝ
def controller (previous : ℝ) : ℝ := -(3/2)*previous
def plant (current command : ℝ) : ℝ := (9/10)*current+(1/5)*command
def augmentedMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![9/10, -3/10; 1, 0]
def step (z : State) : State := ![(9/10)*z 0-(3/10)*z 1, z 0]
def trajectory (initial : State) (n : ℕ) : State := step^[n] initial
def square : Set State := {z | |z 0| ≤ 1/2 ∧ |z 1| ≤ 1/2}
def storage (z : State) : ℝ := CompleteModulesDynamics.delayStorage (z 0) (z 1)
def certifiedRegion : Set State := {z | storage z ≤ 1/8}
def euclidean (z : State) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 z
def rootImaginary : ℝ := Real.sqrt 39/20
def rootPlus : ℂ := ⟨9/20, rootImaginary⟩
def rootMinus : ℂ := ⟨9/20, -rootImaginary⟩
def complexMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![9/10, -3/10; 1, 0]

theorem actual_delayed_plant (current previous : ℝ) :
    plant current (controller previous) = (9/10)*current-(3/10)*previous := by
  unfold plant controller
  ring

theorem actual_augmented_matrix_action (z : State) : augmentedMatrix.mulVec z = step z := by
  ext i
  fin_cases i
  · simp [augmentedMatrix, step, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [augmentedMatrix, step, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem trajectory_initial (z : State) : trajectory z 0 = z := rfl

theorem trajectory_successor (z : State) (n : ℕ) :
    trajectory z (n+1) = step (trajectory z n) := by
  exact Function.iterate_succ_apply' step n z

theorem trajectory_actual_recurrence (z : State) (n : ℕ) :
    trajectory z (n+1) 0 = plant (trajectory z n 0) (controller (trajectory z n 1)) ∧
    trajectory z (n+1) 1 = trajectory z n 0 := by
  rw [trajectory_successor, actual_delayed_plant]
  simp [step]

theorem trajectory_initial_coordinates (current previous : ℝ) :
    trajectory ![current, previous] 0 0 = current ∧
    trajectory ![current, previous] 0 1 = previous := by simp [trajectory]

theorem root_imaginary_positive_and_square :
    0 < rootImaginary ∧ rootImaginary^2 = 39/400 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 39)
  have hp := Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 39)
  unfold rootImaginary
  constructor
  · positivity
  · nlinarith

theorem roots_real_and_imaginary_parts :
    rootPlus.re = 9/20 ∧ rootPlus.im = rootImaginary ∧
    rootMinus.re = 9/20 ∧ rootMinus.im = -rootImaginary := by
  simp [rootPlus, rootMinus]

theorem roots_conjugate_and_distinct :
    star rootPlus = rootMinus ∧ rootPlus ≠ rootMinus := by
  constructor
  · rfl
  · intro h
    have hi := congrArg Complex.im h
    have hp := root_imaginary_positive_and_square.1
    change rootImaginary = -rootImaginary at hi
    linarith

theorem roots_sum_and_product :
    rootPlus+rootMinus = (9/10:ℂ) ∧ rootPlus*rootMinus = (3/10:ℂ) := by
  have hs := root_imaginary_positive_and_square.2
  constructor
  · apply Complex.ext <;> norm_num [rootPlus, rootMinus]
  · apply Complex.ext <;> simp [rootPlus, rootMinus, Complex.mul_re, Complex.mul_im]
    · nlinarith
    · ring

theorem actual_characteristic_polynomial :
    complexMatrix.charpoly = Polynomial.X^2-Polynomial.C (9/10:ℂ)*Polynomial.X+
      Polynomial.C (3/10:ℂ) := by
  rw [Matrix.charpoly_fin_two]
  norm_num [complexMatrix, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]

theorem actual_characteristic_factorization :
    complexMatrix.charpoly =
      (Polynomial.X-Polynomial.C rootPlus)*(Polynomial.X-Polynomial.C rootMinus) := by
  rw [actual_characteristic_polynomial]
  have hs := roots_sum_and_product.1
  have hp := roots_sum_and_product.2
  calc
    Polynomial.X^2-Polynomial.C (9/10:ℂ)*Polynomial.X+Polynomial.C (3/10:ℂ)
      = Polynomial.X^2-Polynomial.C (rootPlus+rootMinus)*Polynomial.X+
          Polynomial.C (rootPlus*rootMinus) := by rw [hs,hp]
    _ = (Polynomial.X-Polynomial.C rootPlus)*(Polynomial.X-Polynomial.C rootMinus) := by
      simp only [map_add, map_mul]
      ring

theorem actual_complex_roots_iff (z : ℂ) :
    complexMatrix.charpoly.eval z = 0 ↔ z = rootPlus ∨ z = rootMinus := by
  rw [actual_characteristic_factorization]
  simp [mul_eq_zero, sub_eq_zero]

theorem actual_two_complex_roots :
    complexMatrix.charpoly.IsRoot rootPlus ∧ complexMatrix.charpoly.IsRoot rootMinus := by
  constructor <;> apply (actual_complex_roots_iff _).2 <;> simp

theorem rootPlus_eigenvector :
    complexMatrix.mulVec ![rootPlus, 1] = rootPlus • ![rootPlus, 1] := by
  have hz := (actual_complex_roots_iff rootPlus).2 (Or.inl rfl)
  rw [actual_characteristic_polynomial] at hz
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hz
  ext i
  fin_cases i
  · simp [complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hz
  · simp [complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rootMinus_eigenvector :
    complexMatrix.mulVec ![rootMinus, 1] = rootMinus • ![rootMinus, 1] := by
  have hz := (actual_complex_roots_iff rootMinus).2 (Or.inr rfl)
  rw [actual_characteristic_polynomial] at hz
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hz
  ext i
  fin_cases i
  · simp [complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hz
  · simp [complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exact_root_magnitudes :
    ‖rootPlus‖ = Real.sqrt (3/10) ∧ ‖rootMinus‖ = Real.sqrt (3/10) := by
  have hs := root_imaginary_positive_and_square.2
  have hp : Complex.normSq rootPlus = 3/10 := by
    simp [Complex.normSq_apply, rootPlus]
    nlinarith
  have hm : Complex.normSq rootMinus = 3/10 := by
    simp [Complex.normSq_apply, rootMinus]
    nlinarith
  constructor
  · rw [Complex.norm_def, hp]
  · rw [Complex.norm_def, hm]

theorem both_roots_strictly_inside_unit_circle : ‖rootPlus‖ < 1 ∧ ‖rootMinus‖ < 1 := by
  rw [exact_root_magnitudes.1, exact_root_magnitudes.2]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/10)
  have hn := Real.sqrt_nonneg (3/10:ℝ)
  constructor <;> nlinarith

theorem imaginary_part_six_decimal_rounding :
    624499/2000000 < rootImaginary ∧ rootImaginary < 624501/2000000 := by
  have hs := root_imaginary_positive_and_square.2
  have hp := root_imaginary_positive_and_square.1
  constructor <;> nlinarith

theorem root_magnitude_six_decimal_rounding :
    1095445/2000000 < Real.sqrt (3/10) ∧ Real.sqrt (3/10) < 1095447/2000000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/10)
  have hn := Real.sqrt_nonneg (3/10:ℝ)
  constructor <;> nlinarith

theorem all_initialized_trajectory_energy (z : State) (n : ℕ) :
    (trajectory z n 0)^2+(trajectory z n 1)^2 ≤ 2*(5/6)^n*storage z := by
  change _ ≤ 2*(5/6)^n*CompleteModulesDynamics.delayStorage (trajectory z 0 0) (trajectory z 0 1)
  apply CompleteModulesDynamics.delayed_trajectory_energy (fun k => trajectory z k 0) (fun k => trajectory z k 1)
  · intro k
    rw [trajectory_successor]
    simp [step]
  · intro k
    rw [trajectory_successor]
    simp [step]

theorem all_initialized_trajectory_energy_tends_zero (z : State) :
    Tendsto (fun n => (trajectory z n 0)^2+(trajectory z n 1)^2) atTop (nhds 0) := by
  apply CompleteModulesDynamics.delayed_trajectory_energy_tends_zero
  · intro k
    rw [trajectory_successor]
    simp [step]
  · intro k
    rw [trajectory_successor]
    simp [step]

theorem actual_euclidean_norm_squared (z : State) : ‖euclidean z‖^2=(z 0)^2+(z 1)^2 := by
  simpa [euclidean, CompleteFoundationsNormDuality.l2Norm,
    CompleteFoundationsNormDuality.euclidean, Fin.sum_univ_two] using
    CompleteFoundationsNormDuality.actual_l2_norm_squared z

theorem all_initialized_augmented_trajectories_tend_zero (z : State) :
    Tendsto (fun n => euclidean (trajectory z n)) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (all_initialized_trajectory_energy_tends_zero z)
  convert h using 1
  · ext n
    simp only [Function.comp_apply]
    rw [← actual_euclidean_norm_squared, Real.sqrt_sq (norm_nonneg _)]
  · simp

theorem uniform_trajectory_energy_bound (z : State) (n : ℕ) :
    ‖euclidean (trajectory z n)‖^2 ≤ 12*‖euclidean z‖^2 := by
  have h := all_initialized_trajectory_energy z n
  have hp : (5/6:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := (CompleteModulesDynamics.delayed_storage_bounds (z 0) (z 1)).2
  have hn : 0 ≤ storage z := by
    have hl := (CompleteModulesDynamics.delayed_storage_bounds (z 0) (z 1)).1
    exact le_trans (by positivity) hl
  have hmul := mul_le_mul_of_nonneg_right hp hn
  rw [actual_euclidean_norm_squared, actual_euclidean_norm_squared]
  change storage z ≤ 6*((z 0)^2+(z 1)^2) at hs
  nlinarith

theorem augmented_origin_lyapunov_stable :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : State,
      ‖euclidean z‖ < δ → ∀ n : ℕ, ‖euclidean (trajectory z n)‖ < ε := by
  intro ε hε
  refine ⟨ε/4, by positivity, ?_⟩
  intro z hz n
  have hb := uniform_trajectory_energy_bound z n
  have hn := norm_nonneg (euclidean z)
  have hnn := norm_nonneg (euclidean (trajectory z n))
  nlinarith

theorem square_escape_initial_and_command :
    (![1/2,-1/2] : State) ∈ square ∧
    step ![1/2,-1/2] 0 = 3/5 ∧ controller (-1/2) = 3/4 ∧
    |controller (-1/2)| ≤ 4/5 ∧ 1/2 < |step ![1/2,-1/2] 0| := by
  norm_num [square, step, controller]

theorem requested_square_is_not_invariant : ¬MapsTo step square square := by
  intro h
  have hi := h square_escape_initial_and_command.1
  have hbound := hi.1
  have hescape := square_escape_initial_and_command.2.2.2.2
  exact (not_lt_of_ge hbound) hescape

theorem escaping_trajectory_still_converges :
    Tendsto (fun n => euclidean (trajectory ![1/2,-1/2] n)) atTop (nhds 0) ∧
    trajectory ![1/2,-1/2] 1 ∉ square := by
  constructor
  · exact all_initialized_augmented_trajectories_tend_zero _
  · intro h
    have he := square_escape_initial_and_command.2.2.2.2
    have hb := h.1
    rw [trajectory_successor, trajectory_initial] at hb
    exact (not_lt_of_ge hb) he

theorem storage_nonnegative (z : State) : 0 ≤ storage z := by
  have h := (CompleteModulesDynamics.delayed_storage_bounds (z 0) (z 1)).1
  exact le_trans (by positivity) h

theorem actual_storage_contraction (z : State) : storage (step z) ≤ (5/6)*storage z := by
  exact CompleteModulesDynamics.delayed_storage_contraction (z 0) (z 1)

theorem certified_region_invariant : MapsTo step certifiedRegion certifiedRegion := by
  intro z hz
  change storage z ≤ 1/8 at hz
  change storage (step z) ≤ 1/8
  have hc := actual_storage_contraction z
  nlinarith [storage_nonnegative z]

theorem certified_region_both_coordinates_contained : certifiedRegion ⊆ square := by
  intro z hz
  have h := (CompleteModulesDynamics.delayed_storage_bounds (z 0) (z 1)).1
  change storage z ≤ 1/8 at hz
  change (1/2)*((z 0)^2+(z 1)^2) ≤ storage z at h
  change |z 0| ≤ 1/2 ∧ |z 1| ≤ 1/2
  have hx := sq_abs (z 0)
  have hy := sq_abs (z 1)
  constructor <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), abs_nonneg (z 0), abs_nonneg (z 1)]

theorem all_certified_trajectories_contained (z : State) (hz : z ∈ certifiedRegion) (n : ℕ) :
    trajectory z n ∈ certifiedRegion ∧ trajectory z n ∈ square := by
  have h : trajectory z n ∈ certifiedRegion := by
    induction n with
    | zero => exact hz
    | succ n ih => rw [trajectory_successor]; exact certified_region_invariant ih
  exact ⟨h, certified_region_both_coordinates_contained h⟩

theorem certified_region_actuator_and_temperature (z : State) (hz : z ∈ certifiedRegion) :
    |controller (z 1)| ≤ 4/5 ∧ 35 ≤ 40+10*z 0 ∧ 40+10*z 0 ≤ 45 := by
  have hc := certified_region_both_coordinates_contained hz
  have h0 := (abs_le.1 hc.1)
  have h1 := (abs_le.1 hc.2)
  constructor
  · unfold controller
    rw [abs_mul]
    norm_num
    linarith [hc.2]
  · constructor <;> linarith

theorem certified_region_contains_origin : (0 : State) ∈ certifiedRegion := by
  norm_num [certifiedRegion, storage, CompleteModulesDynamics.delayStorage]

theorem certified_region_contains_nonzero_neighborhood :
    {z : State | ‖euclidean z‖ ≤ 1/8} ⊆ certifiedRegion := by
  intro z hz
  have hs := (CompleteModulesDynamics.delayed_storage_bounds (z 0) (z 1)).2
  rw [← actual_euclidean_norm_squared] at hs
  change storage z ≤ 6*‖euclidean z‖^2 at hs
  change storage z ≤ 1/8
  have hn := norm_nonneg (euclidean z)
  change ‖euclidean z‖ ≤ 1/8 at hz
  nlinarith

theorem augmented_origin_is_fixed : step (0 : State) = 0 := by
  ext i
  fin_cases i <;> norm_num [step]

theorem every_square_initial_command_is_hardware_feasible (z : State) (hz : z ∈ square) :
    |controller (z 1)| ≤ 3/4 ∧ |controller (z 1)| ≤ 4/5 := by
  have hp := hz.2
  have h : |controller (z 1)| ≤ 3/4 := by
    unfold controller
    rw [abs_mul]
    norm_num
    linarith
  exact ⟨h, by linarith⟩

theorem exact_square_next_error_bound (z : State) (hz : z ∈ square) :
    |step z 0| ≤ 3/5 := by
  change |(9/10)*z 0-(3/10)*z 1| ≤ 3/5
  calc
    _ ≤ |(9/10)*z 0|+|(3/10)*z 1| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((9/10)*z 0) (-((3/10)*z 1))
    _ = (9/10)*|z 0|+(3/10)*|z 1| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 3/5 := by have h0 := hz.1; have h1 := hz.2; linarith

theorem both_square_error_extrema_attained :
    (![1/2,-1/2] : State) ∈ square ∧ step ![1/2,-1/2] 0 = 3/5 ∧
    (![-1/2,1/2] : State) ∈ square ∧ step ![-1/2,1/2] 0 = -3/5 := by
  norm_num [square, step]

theorem rounded_imaginary_decimal_is_not_exact : rootImaginary ≠ 6245/20000 := by
  intro h
  have hs := root_imaginary_positive_and_square.2
  rw [h] at hs
  norm_num at hs

end SafeLearning.CompleteModulesDelayedSquareWhole30
