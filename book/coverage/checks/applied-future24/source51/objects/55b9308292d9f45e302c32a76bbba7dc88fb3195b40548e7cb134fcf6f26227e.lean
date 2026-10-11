import SafeLearning.CompleteModulesGoSafeToyFeasibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyGridCosines

def exactColumnCos (n : ℕ) : ℝ :=
  match n%12 with
  | 0 => 1 | 1 => Real.sqrt 3/2 | 2 => 1/2 | 3 => 0 | 4 => -1/2
  | 5 => -Real.sqrt 3/2 | 6 => -1 | 7 => -Real.sqrt 3/2 | 8 => -1/2
  | 9 => 0 | 10 => 1/2 | _ => Real.sqrt 3/2

def exactColumnSin (n : ℕ) : ℝ :=
  match n%12 with
  | 0 => 0 | 1 => 1/2 | 2 => Real.sqrt 3/2 | 3 => 1 | 4 => Real.sqrt 3/2
  | 5 => 1/2 | 6 => 0 | 7 => -1/2 | 8 => -Real.sqrt 3/2
  | 9 => -1 | 10 => -Real.sqrt 3/2 | _ => -1/2

theorem actual_exact_column_table_obeys_the_true_cosine_sine_addition_step (i : Fin 24) :
    exactColumnCos (i.val+1)=exactColumnCos i.val*(Real.sqrt 3/2)-exactColumnSin i.val*(1/2) ∧
      exactColumnSin (i.val+1)=exactColumnSin i.val*(Real.sqrt 3/2)+exactColumnCos i.val*(1/2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  fin_cases i <;> norm_num [exactColumnCos,exactColumnSin] <;> (try constructor) <;> nlinarith

theorem actual_source_cosine_and_sine_grid_columns_equal_the_exact_table (i : Fin 25) :
    Real.cos (4*Real.pi*((i.val:ℝ)/24))=exactColumnCos i.val ∧
      Real.sin (4*Real.pi*((i.val:ℝ)/24))=exactColumnSin i.val := by
  induction i using Fin.induction with
  | zero => norm_num [exactColumnCos,exactColumnSin]
  | succ i ih =>
    have hangle : 4*Real.pi*(((i.succ).val:ℝ)/24)=
        4*Real.pi*(((i.castSucc).val:ℝ)/24)+Real.pi/6 := by
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    have hstep := actual_exact_column_table_obeys_the_true_cosine_sine_addition_step i
    simp only [Fin.val_succ,Fin.val_castSucc] at hangle
    simp only [Fin.val_succ,Fin.val_castSucc] at ih ⊢
    constructor
    · rw [hangle,Real.cos_add,ih.1,ih.2,Real.cos_pi_div_six,Real.sin_pi_div_six]
      exact hstep.1.symm
    · rw [hangle,Real.sin_add,ih.1,ih.2,Real.cos_pi_div_six,Real.sin_pi_div_six]
      exact hstep.2.symm

theorem actual_source_grid_cosine_difference_is_at_most_twelve_times_parameter_distance
    (i j : Fin 25) :
    |Real.cos (4*Real.pi*((i.val:ℝ)/24))-Real.cos (4*Real.pi*((j.val:ℝ)/24))| ≤
      12 * |(i.val:ℝ)/24-(j.val:ℝ)/24| := by
  rw [(actual_source_cosine_and_sine_grid_columns_equal_the_exact_table i).1,
    (actual_source_cosine_and_sine_grid_columns_equal_the_exact_table j).1]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hlow : 1 ≤ Real.sqrt (3:ℝ) := by nlinarith
  have hupp : Real.sqrt (3:ℝ) ≤ 7/4 := by nlinarith
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [exactColumnCos]
  all_goals try rw [abs_le]
  all_goals try constructor
  all_goals nlinarith

theorem actual_source_grid_columns_at_least_three_steps_apart_have_cosine_slope_at_most_eleven_and_one_quarter
    (i j : Fin 25) (hdist : 3 ≤ max (i.val-j.val) (j.val-i.val)) :
    |Real.cos (4*Real.pi*((i.val:ℝ)/24))-Real.cos (4*Real.pi*((j.val:ℝ)/24))| ≤
      (45/4) * |(i.val:ℝ)/24-(j.val:ℝ)/24| := by
  rw [(actual_source_cosine_and_sine_grid_columns_equal_the_exact_table i).1,
    (actual_source_cosine_and_sine_grid_columns_equal_the_exact_table j).1]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hlow : 1 ≤ Real.sqrt (3:ℝ) := by nlinarith
  have hupp : Real.sqrt (3:ℝ) ≤ 7/4 := by nlinarith
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num at hdist
  all_goals norm_num [exactColumnCos]
  all_goals try rw [abs_le]
  all_goals try constructor
  all_goals nlinarith

end SafeLearning.CompleteModulesGoSafeToyGridCosines
