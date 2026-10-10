import SafeLearning.CompleteModulesSafeOptEightPointReachability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesSafeOptEightPointConsequences
open SafeLearning.CompleteModulesSafeOptEightPointReachability

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

def sourceSequence (n : ℕ) : ℝ := if hn : n < 8 then actualValue ⟨n,hn⟩ else 0

theorem actual_source_seven_consecutive_differences_are_the_printed_tuple :
    (fun i : Fin 7 => |actualValue i.succ-actualValue i.castSucc|)=
      ![(7/10:ℝ),4/5,3/5,1,1/5,9/10,1] ∧
      ∀ i : Fin 7, |actualValue i.succ-actualValue i.castSucc| ≤ 1 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [actualValue]
  · intro i
    fin_cases i <;> norm_num [actualValue]

theorem actual_source_all_pairs_follow_from_the_consecutive_triangle_sum_route
    (i j : Fin 8) : |actualValue i-actualValue j| ≤ actualDistance i j := by
  have hforward (a b : Fin 8) (hab : a.val ≤ b.val) :
      |actualValue b-actualValue a| ≤ (b.val:ℝ)-(a.val:ℝ) := by
    have hs := actual_consecutive_bounds_imply_the_literal_length_bound sourceSequence
      a.val (b.val-a.val) 1 (by
        intro k hk
        have hn : a.val+k+1 < 8 := by omega
        have hn0 : a.val+k < 8 := by omega
        have he : |sourceSequence (a.val+k+1)-sourceSequence (a.val+k)| ≤ 1 := by
          let edge : Fin 7 := ⟨a.val+k,by omega⟩
          simpa [sourceSequence,edge,hn,hn0] using
            actual_source_seven_consecutive_differences_are_the_printed_tuple.2 edge
        exact he)
    simpa [sourceSequence,Nat.add_sub_of_le hab,b.isLt,a.isLt,
      Nat.cast_sub hab] using hs
  rcases le_total i.val j.val with hij | hji
  · have hd : actualDistance i j=(j.val:ℝ)-(i.val:ℝ) := by
      unfold actualDistance
      have hcast : (i.val:ℝ) ≤ (j.val:ℝ) := Nat.cast_le.mpr hij
      rw [abs_of_nonpos (sub_nonpos.mpr hcast)]
      ring
    rw [hd,abs_sub_comm]
    exact hforward i j hij
  · have hd : actualDistance i j=(i.val:ℝ)-(j.val:ℝ) := by
      unfold actualDistance
      have hcast : (j.val:ℝ) ≤ (i.val:ℝ) := Nat.cast_le.mpr hji
      rw [abs_of_nonneg (sub_nonneg.mpr hcast)]
    rw [hd]
    exact hforward j i hji

end SafeLearning.CompleteModulesSafeOptEightPointConsequences
