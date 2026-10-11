import SafeLearning.CompleteFoundationsFiniteReachability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsReachabilitySourceBridges
open CompleteFoundationsFiniteReachability

theorem actual_consecutive_triangle_sum_bounds_every_finite_segment
    (f : ℕ → ℝ) (start length : ℕ) :
    |f (start+length)-f start| ≤
      ∑ k ∈ Finset.range length, |f (start+k+1)-f (start+k)| := by
  induction length with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ |f (start+n+1)-f (start+n)|+|f (start+n)-f start| := by
        simpa [Nat.add_assoc] using abs_sub_le (f (start+n+1)) (f (start+n)) (f start)
      _ ≤ |f (start+n+1)-f (start+n)|+
          ∑ k ∈ Finset.range n, |f (start+k+1)-f (start+k)| := add_le_add le_rfl ih
      _ = _ := by ring

theorem actual_consecutive_bounds_imply_the_literal_length_bound
    (f : ℕ → ℝ) (start length : ℕ) (bound : ℝ)
    (hedge : ∀ k < length, |f (start+k+1)-f (start+k)| ≤ bound) :
    |f (start+length)-f start| ≤ (length:ℝ)*bound := by
  have hs := Finset.sum_le_sum (fun k hk => hedge k (Finset.mem_range.mp hk))
  exact (actual_consecutive_triangle_sum_bounds_every_finite_segment f start length).trans
    (by simpa using hs)

def sourceSequence (n : ℕ) : ℝ := if hn : n < 9 then fitness ⟨n,hn⟩ else 0

theorem actual_eight_consecutive_differences_and_bounds :
    (fun i : Fin 8 => |fitness i.succ-fitness i.castSucc|)=
      ![(1/2:ℝ),9/10,1,1,1,1,1,1] ∧
      ∀ i : Fin 8, |fitness i.succ-fitness i.castSucc| ≤ 1 := by
  constructor
  · ext i;fin_cases i <;> norm_num [fitness]
  · intro i;fin_cases i <;> norm_num [fitness]

theorem actual_all_grid_pairs_follow_from_the_consecutive_bound
    (i j : Fin 9) : |fitness i-fitness j| ≤ distance i j := by
  have hforward (a b : Fin 9) (hab : a.val ≤ b.val) :
      |fitness b-fitness a| ≤ (b.val:ℝ)-(a.val:ℝ) := by
    have hs := actual_consecutive_bounds_imply_the_literal_length_bound sourceSequence
      a.val (b.val-a.val) 1 (by
        intro k hk
        have hn : a.val+k+1 < 9 := by omega
        have hn0 : a.val+k < 9 := by omega
        let edge : Fin 8 := ⟨a.val+k,by omega⟩
        simpa [sourceSequence,edge,hn,hn0] using actual_eight_consecutive_differences_and_bounds.2 edge)
    simpa [sourceSequence,Nat.add_sub_of_le hab,b.isLt,a.isLt,Nat.cast_sub hab] using hs
  rcases le_total i.val j.val with hij | hji
  · have hd : distance i j=(j.val:ℝ)-(i.val:ℝ) := by
      unfold distance
      have hcast : (i.val:ℝ) ≤ (j.val:ℝ) := Nat.cast_le.mpr hij
      rw [abs_of_nonpos (sub_nonpos.mpr hcast)]
      ring
    rw [hd,abs_sub_comm]
    exact hforward i j hij
  · have hd : distance i j=(i.val:ℝ)-(j.val:ℝ) := by
      unfold distance
      have hcast : (j.val:ℝ) ≤ (i.val:ℝ) := Nat.cast_le.mpr hji
      rw [abs_of_nonneg (sub_nonneg.mpr hcast)]
    rw [hd]
    exact hforward j i hji

theorem actual_source_table_has_all_five_iterates :
    sourceIteration 0 1={0,1} ∧ sourceIteration 0 2={0,1,2,3} ∧
      sourceIteration 0 3={0,1,2,3,4,5} ∧
      sourceIteration 0 4={0,1,2,3,4,5,6,7} ∧
      sourceIteration 0 5={0,1,2,3,4,5,6,7} := by
  have h1 : sourceIteration 0 1={0,1} := actual_zero_error_iterates.1
  have h2 : sourceIteration 0 2={0,1,2,3} := by
    rw [actual_iteration_succ, h1,actual_zero_error_iterates.2.1]
  have h3 : sourceIteration 0 3={0,1,2,3,4,5} := by
    rw [actual_iteration_succ,h2,actual_zero_error_iterates.2.2.1]
  exact ⟨h1,h2,h3,actual_zero_error_stabilized 0,actual_zero_error_stabilized 1⟩

theorem actual_source_table_witness_values :
    fitness 0-distance 1 0=4/5 ∧ fitness 1-distance 3 1=3/10 ∧
      fitness 3-distance 5 3=2/5 ∧ fitness 5-distance 7 5=2/5 ∧
      fitness 7-distance 8 7= -3/5 ∧ fitness 5-distance 8 5= -3/5 := by
  norm_num [fitness,distance]

theorem actual_source_has_exactly_four_strict_increases_within_the_budget :
    (∀ n < 4, sourceIteration 0 n ⊂ sourceIteration 0 (n+1)) ∧
      (Fintype.card (Fin 9)-(sourceIteration 0 0).card)=8 ∧ (4:ℕ)≤8 := by
  have h0 : sourceIteration 0 0={0} := rfl
  rcases actual_source_table_has_all_five_iterates with ⟨h1,h2,h3,h4,h5⟩
  refine ⟨?_,?_,by norm_num⟩
  · intro n hn
    interval_cases n <;> simp only [h0,h1,h2,h3,h4] <;> decide
  · rw [h0]
    decide

theorem actual_point_eight_safe_but_every_reachable_witness_fails :
    fitness 8=7/5 ∧ 0 < fitness 8 ∧ 8 ∉ sourceClosure 0 ∧
      ∀ y ∈ sourceClosure 0, fitness y-distance 8 y < 0 := by
  refine ⟨by norm_num [fitness],by norm_num [fitness],actual_gateway_and_dip.2.2.2.2.2,?_⟩
  intro y hy
  rw [actual_zero_error_closure] at hy
  fin_cases y <;> norm_num [fitness,distance] at *

end SafeLearning.CompleteFoundationsReachabilitySourceBridges
