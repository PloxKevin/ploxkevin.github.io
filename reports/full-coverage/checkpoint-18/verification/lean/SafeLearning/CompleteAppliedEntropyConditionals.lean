import SafeLearning.CompleteAppliedEntropyChain
import Mathlib.Probability.ConditionalProbability
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyConditionals
open MeasureTheory ProbabilityTheory Set
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedEntropyChain
open scoped ENNReal NNReal Classical

def firstAtom {n m : ℕ} (i : Fin n) : Set (Fin n × Fin m) := {ij | ij.1=i}

def actualConditionalSecond {n m : ℕ} (law : PMF (Fin n × Fin m)) (i : Fin n) :
    Measure (Fin m) := (cond law.toMeasure (firstAtom i)).map Prod.snd

def conditionalMeasureEntropy {m : ℕ} (μ : Measure (Fin m)) : ℝ :=
  ∑ j,-(μ {j}).toReal*Real.log (μ {j}).toReal

def genuineConditionalEntropy {n m : ℕ} (law : PMF (Fin n × Fin m)) : ℝ :=
  ∫ i,conditionalMeasureEntropy (actualConditionalSecond law i) ∂(law.map Prod.fst).toMeasure

theorem actual_first_event_mass {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) (i : Fin n) :
    (conditionalJoint p kernel).toMeasure (firstAtom i)=p i := by
  have h := congrArg (fun q : PMF (Fin n) => q.toMeasure {i})
    (actual_joint_first_marginal p kernel)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_fst (MeasurableSet.singleton i),
    PMF.toMeasure_apply_singleton p i (MeasurableSet.singleton i)] at h
  exact h

theorem actual_second_conditional_law {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) (i : Fin n) (hi : p i≠0) :
    actualConditionalSecond (conditionalJoint p kernel) i=(kernel i).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [actualConditionalSecond,Measure.map_apply measurable_snd (MeasurableSet.singleton j),
    cond_apply (show MeasurableSet (firstAtom i) from MeasurableSet.of_discrete),
    actual_first_event_mass]
  have he : firstAtom i ∩ Prod.snd ⁻¹' {j}=({(i,j)} : Set (Fin n × Fin m)) := by
    ext ij
    simp only [firstAtom,mem_inter_iff,mem_ofPred_eq,mem_preimage,mem_singleton_iff]
    constructor
    · intro h
      exact Prod.ext h.1 h.2
    · intro h
      cases h
      exact ⟨rfl,rfl⟩
  rw [he,PMF.toMeasure_apply_singleton,actual_conditional_joint_atom,
    PMF.toMeasure_apply_singleton]
  · rw [← mul_assoc,ENNReal.inv_mul_cancel hi (p.apply_ne_top i),one_mul]
  all_goals exact MeasurableSet.singleton _

theorem actual_conditional_measure_entropy {m : ℕ} (p : PMF (Fin m)) :
    conditionalMeasureEntropy p.toMeasure=shannonEntropy p := by
  rw [conditionalMeasureEntropy,actual_entropy_sum]
  simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

theorem actual_kernel_entropy_is_true_conditional_entropy {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) :
    genuineConditionalEntropy (conditionalJoint p kernel)=actualConditionalEntropy p kernel := by
  rw [genuineConditionalEntropy,actual_joint_first_marginal,PMF.integral_eq_sum,
    actual_conditional_entropy_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i=0
  · simp [hi]
  · rw [actual_second_conditional_law p kernel i hi,actual_conditional_measure_entropy]
    rfl

theorem actual_measure_conditioned_entropy_chain_rule {n m : ℕ} (p : PMF (Fin n))
    (kernel : Fin n → PMF (Fin m)) :
    actualJointEntropy (conditionalJoint p kernel)=
      shannonEntropy ((conditionalJoint p kernel).map Prod.fst)+
        genuineConditionalEntropy (conditionalJoint p kernel) := by
  rw [actual_joint_first_marginal,actual_kernel_entropy_is_true_conditional_entropy]
  exact actual_conditional_entropy_chain_rule p kernel

end SafeLearning.CompleteAppliedEntropyConditionals
