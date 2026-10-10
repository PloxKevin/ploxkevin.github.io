import SafeLearning.CompleteFoundationsCholeskyRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace SafeLearning.CompleteFoundationsCholeskyCost

-- Reads have zero arithmetic cost. Every arithmetic operation, including a
-- square root or division, has unit cost in this exact-arithmetic model.
inductive Expression where
  | read (value : ℝ)
  | multiply (left right : Expression)
  | subtract (left right : Expression)
  | squareRoot (argument : Expression)
  | divide (numerator denominator : Expression)

def evaluate : Expression → ℝ
  | .read x => x
  | .multiply x y => evaluate x*evaluate y
  | .subtract x y => evaluate x-evaluate y
  | .squareRoot x => Real.sqrt (evaluate x)
  | .divide x y => evaluate x/evaluate y

def arithmeticCost : Expression → ℕ
  | .read _ => 0
  | .multiply x y => arithmeticCost x+arithmeticCost y+1
  | .subtract x y => arithmeticCost x+arithmeticCost y+1
  | .squareRoot x => arithmeticCost x+1
  | .divide x y => arithmeticCost x+arithmeticCost y+1

def subtractProducts {N : Type*} (P L : Matrix N N ℝ) (i j : N) : List N → Expression
  | [] => .read (P i j)
  | k::ks => .subtract (subtractProducts P L i j ks)
      (.multiply (.read (L i k)) (.read (L j k)))

theorem actual_accumulator_evaluation {N : Type*} (P L : Matrix N N ℝ) (i j : N) (ks : List N) :
    evaluate (subtractProducts P L i j ks)=P i j-(ks.map (fun k => L i k*L j k)).sum := by
  induction ks with
  | nil => simp [subtractProducts,evaluate]
  | cons k ks ih => simp only [subtractProducts,evaluate,List.map_cons,List.sum_cons,ih];ring

theorem actual_accumulator_operation_count {N : Type*} (P L : Matrix N N ℝ) (i j : N) (ks : List N) :
    arithmeticCost (subtractProducts P L i j ks)=2*ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [subtractProducts,arithmeticCost,List.length_cons,ih];omega

def sourceCell {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Expression :=
  let accumulator := subtractProducts P L i j (Finset.Iio j).toList
  if i = j then .squareRoot accumulator else .divide accumulator (.read (L j j))

theorem actual_cell_evaluation {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    evaluate (sourceCell P L i j)=
      if i = j then Real.sqrt (SafeLearning.CompleteFoundationsCholeskyRecursion.pivotArgument P L j)
      else (P i j-SafeLearning.CompleteFoundationsCholeskyRecursion.priorProduct L i j)/L j j := by
  by_cases hij : i = j
  · subst i
    simp [sourceCell,evaluate,actual_accumulator_evaluation,Finset.sum_map_toList,
      SafeLearning.CompleteFoundationsCholeskyRecursion.pivotArgument,pow_two]
  · simp only [sourceCell,if_neg hij,evaluate]
    rw [actual_accumulator_evaluation,Finset.sum_map_toList]
    rfl

theorem actual_positive_recursion_cell_is_factor_entry {n : ℕ}
    (P L : Matrix (Fin n) (Fin n) ℝ)
    (h : SafeLearning.CompleteFoundationsCholeskyRecursion.positiveRecursion P L)
    (i j : Fin n) (hij : j ≤ i) : evaluate (sourceCell P L i j)=L i j := by
  rw [actual_cell_evaluation]
  rcases lt_or_eq_of_le hij with hij|hij
  · rw [if_neg (ne_of_gt hij),← h.2.2 i j hij]
  · subst i
    simp only [if_pos rfl]
    exact (h.2.1 j).2.symm

theorem actual_cell_operation_count {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    arithmeticCost (sourceCell P L i j)=2*j.val+1 := by
  unfold sourceCell
  split <;> simp [arithmeticCost,actual_accumulator_operation_count,Fin.card_Iio]

-- Every lower-triangular entry is evaluated once. The dependent row index
-- includes exactly columns0,...,i, so this counts the source cell expressions.
def sourceProgramCost {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  ∑ i : Fin n,∑ j : Fin (i.val+1),
    arithmeticCost (sourceCell P L i (j.castLE (by omega)))

theorem actual_row_operation_count (k : ℕ) : (∑ j : Fin k,(2*j.val+1))=k^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    ring

theorem actual_program_cost_as_squares {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) :
    sourceProgramCost P L=∑ i ∈ Finset.range n,(i+1)^2 := by
  simp only [sourceProgramCost,actual_cell_operation_count,Fin.coe_castLE]
  simp_rw [actual_row_operation_count]
  exact (Finset.sum_range (n := n) (fun i : ℕ => (i+1)^2)).symm

theorem actual_program_cost_polynomial {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) :
    6*sourceProgramCost P L=n*(n+1)*(2*n+1) := by
  rw [actual_program_cost_as_squares]
  have h : ∀ k : ℕ,6*(∑ i ∈ Finset.range k,(i+1)^2)=k*(k+1)*(2*k+1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      nlinarith
  exact h n

def dimensionCost (n : ℕ) : ℕ :=
  sourceProgramCost (0 : Matrix (Fin n) (Fin n) ℝ) 0

theorem actual_cost_independent_of_entries {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) :
    sourceProgramCost P L=dimensionCost n := by
  rw [dimensionCost,actual_program_cost_as_squares,actual_program_cost_as_squares]

theorem actual_cubic_leading_term :
    Tendsto (fun n : ℕ => (dimensionCost n : ℝ)/(n : ℝ)^3) atTop (𝓝 (1/3 : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => (1/3 : ℝ)+(1/2 : ℝ)*(n : ℝ)⁻¹+
      (1/6 : ℝ)*((n : ℝ)⁻¹)^2) atTop (𝓝 (1/3 : ℝ)) := by
    simpa using ((tendsto_const_nhds.add (hi.const_mul (1/2 : ℝ))).add ((hi.pow 2).const_mul (1/6 : ℝ)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hp := actual_program_cost_polynomial (0 : Matrix (Fin n) (Fin n) ℝ) 0
  change 6*dimensionCost n=n*(n+1)*(2*n+1) at hp
  have hpr : (6 : ℝ)*(dimensionCost n : ℝ)=(n : ℝ)*((n : ℝ)+1)*(2*(n : ℝ)+1) := by exact_mod_cast hp
  have hc : (dimensionCost n : ℝ)=(n : ℝ)*((n : ℝ)+1)*(2*(n : ℝ)+1)/6 := by linarith
  rw [hc]
  field_simp
  <;> ring

end SafeLearning.CompleteFoundationsCholeskyCost
