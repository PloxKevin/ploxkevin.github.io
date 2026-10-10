import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConformalSubgroups
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

def subgroupLaw : Measure (Fin 20) := (PMF.uniformOfFintype (Fin 20)).toMeasure
instance : IsProbabilityMeasure subgroupLaw := by unfold subgroupLaw;infer_instance

def accepted : Set (Fin 20) := {i | i.val<18}
def groupA : Set (Fin 20) := {i | i.val<8 ∨ 18 ≤ i.val}
def groupB : Set (Fin 20) := {i | 8 ≤ i.val ∧ i.val<18}

theorem actual_subgroups_are_disjoint_and_exhaust_the_population :
    Disjoint groupA groupB ∧ groupA ∪ groupB=univ := by
  constructor
  · apply Set.disjoint_left.mpr
    intro i ha hb
    change i.val<8 ∨ 18 ≤ i.val at ha
    change 8 ≤ i.val ∧ i.val<18 at hb
    omega
  · ext i
    simp only [groupA,groupB,Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    omega

theorem actual_marginal_and_subgroup_event_probabilities :
    subgroupLaw.real accepted=(0.9:ℝ) ∧
    subgroupLaw.real groupA=(0.5:ℝ) ∧ subgroupLaw.real groupB=(0.5:ℝ) ∧
    subgroupLaw.real (accepted ∩ groupA)=(0.4:ℝ) ∧
    subgroupLaw.real (accepted ∩ groupB)=(0.5:ℝ) := by
  simp only [Measure.real,subgroupLaw,PMF.toMeasure_apply_fintype,
    accepted,groupA,groupB,Set.inter_def]
  norm_num [Set.indicator,Fin.sum_univ_succ,ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_mul,two_mul]

theorem actual_subgroup_conditional_coverages_are_point_eight_and_one :
    (cond subgroupLaw groupA).real accepted=(0.8:ℝ) ∧
      (cond subgroupLaw groupB).real accepted=1 := by
  have hma : MeasurableSet groupA := by measurability
  have hmb : MeasurableSet groupB := by measurability
  have hp := actual_marginal_and_subgroup_event_probabilities
  constructor
  · change ((cond subgroupLaw groupA) accepted).toReal=(0.8:ℝ)
    rw [cond_apply hma,ENNReal.toReal_mul,ENNReal.toReal_inv]
    change (subgroupLaw.real groupA)⁻¹*subgroupLaw.real (groupA ∩ accepted)=(0.8:ℝ)
    rw [Set.inter_comm,hp.2.1,hp.2.2.2.1]
    norm_num
  · change ((cond subgroupLaw groupB) accepted).toReal=1
    rw [cond_apply hmb,ENNReal.toReal_mul,ENNReal.toReal_inv]
    change (subgroupLaw.real groupB)⁻¹*subgroupLaw.real (groupB ∩ accepted)=1
    rw [Set.inter_comm,hp.2.2.1,hp.2.2.2.2]
    norm_num

theorem actual_marginal_target_does_not_imply_each_subgroup_target :
    subgroupLaw.real accepted=(0.9:ℝ) ∧
      (cond subgroupLaw groupA).real accepted<(0.9:ℝ) ∧
      (0.5:ℝ)*(0.8:ℝ)+(0.5:ℝ)*1=(0.9:ℝ) := by
  refine ⟨actual_marginal_and_subgroup_event_probabilities.1,?_,by norm_num⟩
  rw [actual_subgroup_conditional_coverages_are_point_eight_and_one.1]
  norm_num

end SafeLearning.CompleteAppliedConformalSubgroups
