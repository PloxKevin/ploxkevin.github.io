import SafeLearning.CompleteAppliedFiniteEntropy
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyChain
open MeasureTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy
open scoped ENNReal NNReal Classical

def conditionalJoint {n m : ℕ} (p : PMF (Fin n)) (kernel : Fin n → PMF (Fin m)) :
    PMF (Fin n × Fin m) := PMF.ofFintype (fun ij => p ij.1 * kernel ij.1 ij.2) (by
  rw [Fintype.sum_prod_type]
  have hk (i : Fin n) : (∑ j,kernel i j)=1 := by simpa [tsum_fintype] using (kernel i).tsum_coe
  simp only [← Finset.mul_sum,hk,mul_one]
  simpa [tsum_fintype] using p.tsum_coe)

def actualJointEntropy {n m : ℕ} (law : PMF (Fin n × Fin m)) : ℝ :=
  -(∫ ij,Real.log (law ij).toReal ∂law.toMeasure)

def actualConditionalEntropy {n m : ℕ} (p : PMF (Fin n)) (kernel : Fin n → PMF (Fin m)) : ℝ :=
  ∫ i,shannonEntropy (kernel i) ∂p.toMeasure

theorem actual_conditional_joint_atom {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) (i : Fin n) (j : Fin m) :
    conditionalJoint p kernel (i,j)=p i * kernel i j := by rfl

theorem actual_joint_first_marginal {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) : (conditionalJoint p kernel).map Prod.fst=p := by
  classical
  ext i
  rw [PMF.map_apply,tsum_fintype,Fintype.sum_prod_type]
  simp only [conditionalJoint,PMF.ofFintype_apply]
  have hk (a : Fin n) : (∑ j,kernel a j)=1 := by simpa [tsum_fintype] using (kernel a).tsum_coe
  calc
    _ = (∑ a,if i=a then p a else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hi : i=a
      · simp [hi,← Finset.mul_sum,hk]
      · simp [hi]
    _ = p i := by simp

theorem actual_joint_entropy_sum {n m : ℕ} (law : PMF (Fin n × Fin m)) :
    actualJointEntropy law=∑ i,∑ j,-(law (i,j)).toReal*Real.log (law (i,j)).toReal := by
  rw [actualJointEntropy,PMF.integral_eq_sum,Fintype.sum_prod_type]
  simp only [smul_eq_mul,Finset.sum_neg_distrib,neg_mul]

theorem actual_conditional_entropy_sum {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) :
    actualConditionalEntropy p kernel=∑ i,(p i).toReal*shannonEntropy (kernel i) := by
  rw [actualConditionalEntropy,PMF.integral_eq_sum]
  simp only [smul_eq_mul]

theorem actual_entropy_product_weight_identity (a b : ℝ) :
    -(a*b)*Real.log (a*b)=(-a*Real.log a)*b+a*(-b*Real.log b) := by
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

theorem actual_conditional_entropy_chain_rule {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) :
    actualJointEntropy (conditionalJoint p kernel)=shannonEntropy p+actualConditionalEntropy p kernel := by
  rw [actual_joint_entropy_sum,actual_entropy_sum,actual_conditional_entropy_sum]
  simp only [conditionalJoint,PMF.ofFintype_apply,ENNReal.toReal_mul,
    actual_entropy_product_weight_identity]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    actual_finite_weights_sum,mul_one,actual_entropy_sum]

end SafeLearning.CompleteAppliedEntropyChain
