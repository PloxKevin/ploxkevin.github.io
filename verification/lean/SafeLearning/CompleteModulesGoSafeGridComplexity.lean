import SafeLearning.CompleteModulesGoSafeGridOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set BigOperators Filter Asymptotics
namespace SafeLearning.CompleteModulesGoSafeGridComplexity
open SafeLearning.CompleteModulesGoSafeGridOperations

/-- Count the three actual arithmetic instructions in every evaluated distance program. -/
def actualDatabaseArithmeticCost {b : ℕ} (database : Fin b → List (ℝ × ℝ)) : ℕ :=
  ∑ i, ((actualSquaredDistanceProgram (database i)).2.1+
    (actualSquaredDistanceProgram (database i)).2.2.1+
    (actualSquaredDistanceProgram (database i)).2.2.2)

def dimensionArithmeticCost (b s : ℕ) : ℕ := b*(s+s+(s-1))

theorem actual_evaluated_database_cost_is_the_dimension_formula
    (b s : ℕ) (database : Fin b → List (ℝ × ℝ))
    (hlen : ∀ i, (database i).length=s) :
    actualDatabaseArithmeticCost database=dimensionArithmeticCost b s := by
  unfold actualDatabaseArithmeticCost dimensionArithmeticCost
  have heach : ∀ i, (actualSquaredDistanceProgram (database i)).2.1+
      (actualSquaredDistanceProgram (database i)).2.2.1+
      (actualSquaredDistanceProgram (database i)).2.2.2=s+s+(s-1) := by
    intro i
    obtain ⟨hsub,hmul,hadd⟩ :=
      actual_program_uses_s_subtractions_s_multiplications_and_s_minus_one_additions (database i)
    simp [hsub,hmul,hadd,hlen]
  simp_rw [heach]
  simp

theorem actual_total_arithmetic_cost_is_at_most_three_times_backup_count_times_dimension
    (b s : ℕ) : dimensionArithmeticCost b s ≤ 3*(b*s) := by
  unfold dimensionArithmeticCost
  have h : s+s+(s-1) ≤ 3*s := by omega
  calc
    b*(s+s+(s-1)) ≤ b*(3*s) := Nat.mul_le_mul_left b h
    _ = 3*(b*s) := by ring

theorem actual_combined_arithmetic_cost_is_big_O_of_dimension_times_database_size
    (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ => (dimensionArithmeticCost p.1 p.2 : ℝ)) =O[l]
      (fun p : ℕ × ℕ => ((p.1*p.2 : ℕ) : ℝ)) := by
  apply IsBigO.of_bound 3
  apply Eventually.of_forall
  intro p
  have h := actual_total_arithmetic_cost_is_at_most_three_times_backup_count_times_dimension p.1 p.2
  have hreal : (dimensionArithmeticCost p.1 p.2 : ℝ) ≤
      3*((p.1*p.2 : ℕ) : ℝ) := by exact_mod_cast h
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (dimensionArithmeticCost p.1 p.2 : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (show 0 ≤ ((p.1*p.2 : ℕ) : ℝ) from Nat.cast_nonneg _)] using hreal

theorem adding_one_comparison_per_backup_preserves_the_same_order_bound
    (b s : ℕ) (hs : 0 < s) :
    dimensionArithmeticCost b s+b ≤ 4*(b*s) := by
  have h := actual_total_arithmetic_cost_is_at_most_three_times_backup_count_times_dimension b s
  have hb : b ≤ b*s := by
    calc
      b = b*1 := by simp
      _ ≤ b*s := Nat.mul_le_mul_left b hs
  omega

theorem actual_source_database_has_eight_thousand_five_hundred_arithmetic_operations :
    dimensionArithmeticCost 500 6=8500 ∧
      dimensionArithmeticCost 500 6+500=9000 := by
  norm_num [dimensionArithmeticCost]

/-- A throughput model states its rate as a premise; it makes no hardware measurement. -/
def modelElapsedSeconds (operations : ℕ) (operationsPerSecond : ℝ) : ℝ :=
  (operations:ℝ)/operationsPerSecond

theorem literal_multiplication_deadline_requires_three_hundred_thousand_per_second
    (rate : ℝ) (hr : 0 < rate) :
    modelElapsedSeconds 3000 rate ≤ 1/100 ↔ 300000 ≤ rate := by
  unfold modelElapsedSeconds
  rw [div_le_iff₀ hr]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem counting_all_arithmetic_and_comparisons_requires_nine_hundred_thousand_per_second
    (rate : ℝ) (hr : 0 < rate) :
    modelElapsedSeconds 9000 rate ≤ 1/100 ↔ 900000 ≤ rate := by
  unfold modelElapsedSeconds
  rw [div_le_iff₀ hr]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem positive_processing_rate_alone_does_not_imply_the_literal_realtime_deadline :
    0 < (1:ℝ) ∧ modelElapsedSeconds 3000 1 > 1/100 := by
  norm_num [modelElapsedSeconds]

end SafeLearning.CompleteModulesGoSafeGridComplexity
