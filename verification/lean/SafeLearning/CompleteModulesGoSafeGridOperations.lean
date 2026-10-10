import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set BigOperators
namespace SafeLearning.CompleteModulesGoSafeGridOperations

/-- Actual evaluation and arithmetic counts, with a shared difference register per coordinate. -/
def actualSquaredDistanceProgram : List (ℝ × ℝ) → ℝ × (ℕ × (ℕ × ℕ))
  | [] => (0,(0,(0,0)))
  | (x,y)::rest =>
    let difference := x-y
    let square := difference*difference
    match rest with
    | [] => (square,(1,(1,0)))
    | q::tail =>
      let result := actualSquaredDistanceProgram (q::tail)
      (square+result.1,(1+result.2.1,(1+result.2.2.1,1+result.2.2.2)))
termination_by xs => xs.length

theorem actual_program_evaluates_the_literal_sum_of_squared_coordinate_differences
    (coordinates : List (ℝ × ℝ)) :
    (actualSquaredDistanceProgram coordinates).1=
      (coordinates.map (fun p => (p.1-p.2)^2)).sum := by
  induction coordinates with
  | nil => simp [actualSquaredDistanceProgram]
  | cons p rest ih =>
    obtain ⟨x,y⟩ := p
    cases rest with
    | nil => simp [actualSquaredDistanceProgram,pow_two]
    | cons q tail => simpa [actualSquaredDistanceProgram,pow_two] using congrArg (fun value => (x-y)*(x-y)+value) ih

theorem actual_program_uses_s_subtractions_s_multiplications_and_s_minus_one_additions
    (coordinates : List (ℝ × ℝ)) :
    (actualSquaredDistanceProgram coordinates).2.1=coordinates.length ∧
      (actualSquaredDistanceProgram coordinates).2.2.1=coordinates.length ∧
      (actualSquaredDistanceProgram coordinates).2.2.2=coordinates.length-1 := by
  induction coordinates with
  | nil => simp [actualSquaredDistanceProgram]
  | cons p rest ih =>
    obtain ⟨x,y⟩ := p
    cases rest with
    | nil => simp [actualSquaredDistanceProgram]
    | cons q tail =>
      simp only [actualSquaredDistanceProgram,List.length_cons,ih.1,ih.2.1,ih.2.2]
      omega

theorem actual_euclidean_squared_distance_is_the_programs_coordinate_sum
    (s : ℕ) (x y : EuclideanSpace ℝ (Fin s)) :
    dist x y^2=∑ i, (x i-y i)^2 := by
  simp [EuclideanSpace.dist_sq_eq,Real.dist_eq,sq_abs]

theorem actual_euclidean_closed_ball_membership_can_be_checked_without_a_square_root
    (s : ℕ) (x y : EuclideanSpace ℝ (Fin s)) (radius : ℝ) (hr : 0 ≤ radius) :
    x ∈ Metric.closedBall y radius ↔ (∑ i, (x i-y i)^2) ≤ radius^2 := by
  rw [Metric.mem_closedBall,← actual_euclidean_squared_distance_is_the_programs_coordinate_sum]
  have hn := dist_nonneg (x:=x) (y:=y)
  constructor <;> intro h <;> nlinarith

theorem actual_operation_indices_for_any_finite_backup_database
    (backupCount s : ℕ) :
    Fintype.card (Fin backupCount × Fin s)=backupCount*s ∧
      Fintype.card (Fin backupCount × Fin (s-1))=backupCount*(s-1) := by simp

theorem actual_six_coordinate_program_at_five_hundred_backups_and_one_hundred_measurements_per_second
    (coordinates : List (ℝ × ℝ)) (hlen : coordinates.length=6) :
    500*(actualSquaredDistanceProgram coordinates).2.1=3000 ∧
      500*(actualSquaredDistanceProgram coordinates).2.2.1=3000 ∧
      500*(actualSquaredDistanceProgram coordinates).2.2.2=2500 ∧
      100*(500*(actualSquaredDistanceProgram coordinates).2.2.1)=300000 := by
  have h := actual_program_uses_s_subtractions_s_multiplications_and_s_minus_one_additions coordinates
  rcases h with ⟨hsub,hmul,hadd⟩
  simp only [hsub,hmul,hadd,hlen]
  norm_num

theorem actual_shared_tolerance_spacing_gets_strictly_finer_as_positive_dimension_increases
    (mu : ℝ) (hm : 0 < mu) (s t : ℕ) (hs : 0 < s) (hst : s < t) :
    2*mu/(t:ℝ)<2*mu/(s:ℝ) := by
  have hsreal : 0 < (s:ℝ) := by exact_mod_cast hs
  have hstreal : (s:ℝ)<(t:ℝ) := by exact_mod_cast hst
  exact div_lt_div_of_pos_left (by positivity) hsreal hstreal

end SafeLearning.CompleteModulesGoSafeGridOperations
