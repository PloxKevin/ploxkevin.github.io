import SafeLearning.CompleteFiniteControlledPathFlow

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SafeLearning.CompleteFiniteControlledPathMeasure

open SafeLearning.CompleteFiniteCMDPOccupancy

variable {S A : Type*} [Fintype S] [Fintype A]

/-- A nonanticipative randomized action law may depend on the entire finite
past and the current state. -/
structure HistoryPolicy (S A : Type*) [Fintype S] [Fintype A] where
  action : (n : ℕ) → (Fin n → S × A) → S → A → ℝ
  action_nonneg : ∀ n history s a, 0 ≤ action n history s a
  action_sum : ∀ n history s, ∑ a, action n history s a = 1

def initialJoint (M : Model S A) (π : HistoryPolicy S A) (z : S × A) : ℝ :=
  M.initial z.1 * π.action 0 (fun i => Fin.elim0 i) z.1 z.2

theorem actual_initial_joint_nonnegative (M : Model S A) (π : HistoryPolicy S A)
    (z : S × A) : 0 ≤ initialJoint M π z :=
  mul_nonneg (M.initial_nonneg z.1) (π.action_nonneg 0 _ z.1 z.2)

theorem actual_initial_joint_normalized (M : Model S A) (π : HistoryPolicy S A) :
    ∑ z, initialJoint M π z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [initialJoint, ← Finset.mul_sum, π.action_sum, mul_one, M.initial_sum]

def initialPMF (M : Model S A) (π : HistoryPolicy S A) : PMF (S × A) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (initialJoint M π z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => actual_initial_joint_nonnegative M π z),
      actual_initial_joint_normalized M π]
    simp)

def stepJoint (M : Model S A) (π : HistoryPolicy S A) (n : ℕ)
    (history : (i : Finset.Iic n) → S × A) (z : S × A) : ℝ :=
  M.transition (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1
    (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 z.1 *
      π.action (n + 1)
        (fun i => history ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩) z.1 z.2

theorem actual_step_joint_nonnegative (M : Model S A) (π : HistoryPolicy S A)
    (n : ℕ) (history : (i : Finset.Iic n) → S × A) (z : S × A) :
    0 ≤ stepJoint M π n history z :=
  mul_nonneg (M.transition_nonneg _ _ _) (π.action_nonneg _ _ _ _)

theorem actual_step_joint_normalized (M : Model S A) (π : HistoryPolicy S A)
    (n : ℕ) (history : (i : Finset.Iic n) → S × A) :
    ∑ z, stepJoint M π n history z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [stepJoint, ← Finset.mul_sum, π.action_sum, mul_one, M.transition_sum]

def stepPMF (M : Model S A) (π : HistoryPolicy S A) (n : ℕ)
    (history : (i : Finset.Iic n) → S × A) : PMF (S × A) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (stepJoint M π n history z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => actual_step_joint_nonnegative M π n history z),
      actual_step_joint_normalized M π]
    simp)

variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

def historyKernel (M : Model S A) (π : HistoryPolicy S A) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S × A) (S × A) :=
  Kernel.ofFunOfCountable (fun history => (stepPMF M π n history).toMeasure)

instance historyKernel_markov (M : Model S A) (π : HistoryPolicy S A) (n : ℕ) :
    IsMarkovKernel (historyKernel M π n) :=
  ⟨fun history => by change IsProbabilityMeasure (stepPMF M π n history).toMeasure; infer_instance⟩

/-- The genuine infinite controlled path measure, constructed by Ionescu-Tulcea
from the initial probability law and the entire-history action kernels. -/
def controlledPathMeasure (M : Model S A) (π : HistoryPolicy S A) :
    Measure (ℕ → S × A) :=
  Kernel.trajMeasure (initialPMF M π).toMeasure (historyKernel M π)

instance controlledPathMeasure_probability (M : Model S A) (π : HistoryPolicy S A) :
    IsProbabilityMeasure (controlledPathMeasure M π) := by
  unfold controlledPathMeasure
  infer_instance

theorem actual_history_kernel_singleton_probability (M : Model S A)
    (π : HistoryPolicy S A) (n : ℕ) (history : (i : Finset.Iic n) → S × A)
    (z : S × A) :
    (historyKernel M π n history).real {z} = stepJoint M π n history z := by
  change ((stepPMF M π n history).toMeasure {z}).toReal = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  exact ENNReal.toReal_ofReal (actual_step_joint_nonnegative M π n history z)

theorem actual_full_history_successor_joint_law (M : Model S A)
    (π : HistoryPolicy S A) (n : ℕ) :
    (controlledPathMeasure M π).map (Preorder.frestrictLe n) ⊗ₘ historyKernel M π n =
      (controlledPathMeasure M π).map (fun path => (Preorder.frestrictLe n path, path (n + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end SafeLearning.CompleteFiniteControlledPathMeasure
