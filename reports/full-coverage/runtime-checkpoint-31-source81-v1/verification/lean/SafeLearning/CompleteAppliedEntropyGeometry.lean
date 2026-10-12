import SafeLearning.CompleteAppliedFiniteBregman
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyGeometry
open SafeLearning.CompleteAppliedFiniteBregman
open scoped BigOperators

def nonnegativeOrthant (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i,0 ≤ x i}

theorem actual_nonnegative_entropy_domain_convex (n : ℕ) :
    Convex ℝ (nonnegativeOrthant n) := by
  intro x hx y hy a b ha hb hab i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem actual_negative_entropy_convex (n : ℕ) :
    ConvexOn ℝ (nonnegativeOrthant n) negativeEntropy := by
  refine ⟨actual_nonnegative_entropy_domain_convex n,?_⟩
  intro x hx y hy a b ha hb hab
  have hi (i : Fin n) := Real.convexOn_mul_log.2 (hx i) (hy i) ha hb hab
  calc
    _ ≤ ∑ i,(a*(x i*Real.log (x i))+b*(y i*Real.log (y i))) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hi i
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,negativeEntropy,smul_eq_mul]

theorem actual_negative_entropy_strictly_convex (n : ℕ) :
    StrictConvexOn ℝ (nonnegativeOrthant n) negativeEntropy := by
  refine ⟨actual_nonnegative_entropy_domain_convex n,?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hne : ∃ i,x i≠y i := by by_contra h;push_neg at h;exact hxy (funext h)
  obtain ⟨j,hj⟩:=hne
  have hlt := Real.strictConvexOn_mul_log.2 (hx j) (hy j) hj ha hb hab
  have hle (i : Fin n) := Real.convexOn_mul_log.2 (hx i) (hy i) ha.le hb.le hab
  calc
    _ < ∑ i,(a*(x i*Real.log (x i))+b*(y i*Real.log (y i))) := by
      apply Finset.sum_lt_sum
      · intro i _
        simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hle i
      · exact ⟨j,Finset.mem_univ j,by
          simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hlt⟩
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,negativeEntropy,smul_eq_mul]

end SafeLearning.CompleteAppliedEntropyGeometry
