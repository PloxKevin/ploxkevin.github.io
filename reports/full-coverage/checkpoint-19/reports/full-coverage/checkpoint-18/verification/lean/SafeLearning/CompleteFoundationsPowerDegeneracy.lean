import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsPowerDegeneracy

abbrev E := EuclideanSpace ℝ (Fin 3)
def repeatedA : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![3,3,1]
def axis (i : Fin 3) : E := EuclideanSpace.single i 1
def action (A : Matrix (Fin 3) (Fin 3) ℝ) : E →L[ℝ] E :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A
def powerStep (x : E) : E := ‖action (repeatedAᵀ*repeatedA) x‖⁻¹ • action (repeatedAᵀ*repeatedA) x
def trajectory (k : ℕ) : E := (powerStep^[k]) (axis 2)

theorem actual_action_coordinate (A : Matrix (Fin 3) (Fin 3) ℝ) (x : E) (i : Fin 3) :
    action A x i=(A *ᵥ (x : Fin 3 → ℝ)) i := rfl

theorem actual_repeated_gram : repeatedAᵀ*repeatedA=Matrix.diagonal ![9,9,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [repeatedA,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_axis_unit (i : Fin 3) : ‖axis i‖=1 := by simp [axis]

theorem actual_repeated_top_directions :
    action repeatedA (axis 0)=(3 : ℝ) • axis 0 ∧
    action repeatedA (axis 1)=(3 : ℝ) • axis 1 ∧
    inner ℝ (axis 0) (axis 1)=0 := by
  constructor
  · ext i
    fin_cases i <;> simp [actual_action_coordinate,repeatedA,Matrix.mulVec_diagonal,axis]
  constructor
  · ext i
    fin_cases i <;> simp [actual_action_coordinate,repeatedA,Matrix.mulVec_diagonal,axis]
  · simp [axis,EuclideanSpace.inner_single_left]

theorem actual_repeated_spectral_norm : ‖repeatedA‖=3 := by
  rw [repeatedA,Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
    intro i
    fin_cases i <;> norm_num
  · have hb := norm_le_pi_norm (![3,3,1] : Fin 3 → ℝ) (0 : Fin 3)
    simpa using hb

theorem actual_lower_axis_and_gram_action :
    action repeatedA (axis 2)=axis 2 ∧ action (repeatedAᵀ*repeatedA) (axis 2)=axis 2 := by
  constructor
  · ext i
    fin_cases i <;> simp [actual_action_coordinate,repeatedA,Matrix.mulVec_diagonal,axis]
  · rw [actual_repeated_gram]
    ext i
    fin_cases i <;> simp [actual_action_coordinate,Matrix.mulVec_diagonal,axis]

theorem actual_power_step_fixed : powerStep (axis 2)=axis 2 := by
  rw [powerStep,actual_lower_axis_and_gram_action.2,actual_axis_unit]
  simp

theorem actual_all_iterates_and_estimates (k : ℕ) :
    trajectory k=axis 2 ∧ ‖action repeatedA (trajectory k)‖=1 := by
  have ht : trajectory k=axis 2 := Function.iterate_fixed actual_power_step_fixed k
  exact ⟨ht,by rw [ht,actual_lower_axis_and_gram_action.1,actual_axis_unit]⟩

theorem actual_initial_dominant_projection_zero :
    inner ℝ (axis 0) (axis 2)=0 ∧ inner ℝ (axis 1) (axis 2)=0 := by
  simp [axis,EuclideanSpace.inner_single_left]

theorem actual_estimates_do_not_reach_top :
    ¬Filter.Tendsto (fun k : ℕ => ‖action repeatedA (trajectory k)‖) Filter.atTop (nhds ‖repeatedA‖) := by
  have he : (fun k : ℕ => ‖action repeatedA (trajectory k)‖)=fun _ : ℕ => (1 : ℝ) := by
    funext k
    exact (actual_all_iterates_and_estimates k).2
  rw [he,actual_repeated_spectral_norm]
  intro h
  have hh : (1 : ℝ)=3 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at hh

end SafeLearning.CompleteFoundationsPowerDegeneracy
