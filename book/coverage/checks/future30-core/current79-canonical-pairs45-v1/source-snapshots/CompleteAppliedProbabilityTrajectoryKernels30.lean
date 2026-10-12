import SafeLearning.CompleteFiniteMarkovPathCorrespondence

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SafeLearning.CompleteAppliedProbabilityTrajectoryKernels30

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- The next state is sampled from P and the next action from the policy at that state. -/
def nextPairKernel (π : Kernel S A) (P : Kernel (S × A) S) : Kernel (S × A) (S × A) :=
  P ⊗ₖ π.comap (fun z : (S × A) × S => z.2) measurable_snd

instance nextPairKernel_markov (π : Kernel S A) (P : Kernel (S × A) S)
    [IsMarkovKernel π] [IsMarkovKernel P] : IsMarkovKernel (nextPairKernel π P) := by
  unfold nextPairKernel
  infer_instance

/-- The actual five-coordinate prefix law obtained by successively sampling the kernels. -/
def prefixFiveLaw (μ : Measure S) (π : Kernel S A) (P : Kernel (S × A) S) :
    Measure (((S × A) × (S × A)) × S) :=
  ((μ ⊗ₘ π) ⊗ₘ nextPairKernel π P) ⊗ₘ
    P.comap (fun z : (S × A) × (S × A) => z.2) measurable_snd

instance prefixFiveLaw_probability (μ : Measure S) (π : Kernel S A)
    (P : Kernel (S × A) S) [IsProbabilityMeasure μ] [IsMarkovKernel π]
    [IsMarkovKernel P] : IsProbabilityMeasure (prefixFiveLaw μ π P) := by
  unfold prefixFiveLaw
  infer_instance

theorem actual_joint_kernel_atom_probability
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (κ : Kernel X Y) [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (x : X) (y : Y) :
    (μ ⊗ₘ κ) {(x, y)} = μ {x} * κ x {y} := by
  have hset : ({(x, y)} : Set (X × Y)) = {x} ×ˢ {y} := by
    ext z
    simp [Prod.ext_iff]
  rw [hset, Measure.compProd_apply_prod (measurableSet_singleton x)
    (measurableSet_singleton y), lintegral_singleton]
  exact mul_comm _ _

theorem actual_next_pair_kernel_atom_probability (π : Kernel S A)
    (P : Kernel (S × A) S) [IsMarkovKernel π] [IsMarkovKernel P]
    (z : S × A) (s : S) (a : A) :
    nextPairKernel π P z {(s, a)} = P z {s} * π s {a} := by
  have hset : ({(s, a)} : Set (S × A)) = {s} ×ˢ {a} := by
    ext w
    simp [Prod.ext_iff]
  rw [nextPairKernel, hset, Kernel.compProd_apply_prod (measurableSet_singleton s)
    (measurableSet_singleton a), lintegral_singleton]
  simp only [Kernel.comap_apply']
  exact mul_comm _ _

theorem actual_five_coordinate_trajectory_product (μ : Measure S) (π : Kernel S A)
    (P : Kernel (S × A) S) [IsProbabilityMeasure μ] [IsMarkovKernel π]
    [IsMarkovKernel P] (s0 s1 s2 : S) (a0 a1 : A) :
    prefixFiveLaw μ π P {(((s0, a0), (s1, a1)), s2)} =
      μ {s0} * π s0 {a0} * P (s0, a0) {s1} * π s1 {a1} * P (s1, a1) {s2} := by
  unfold prefixFiveLaw
  rw [actual_joint_kernel_atom_probability, actual_joint_kernel_atom_probability,
    actual_joint_kernel_atom_probability, actual_next_pair_kernel_atom_probability]
  simp only [Kernel.comap_apply']
  ring

/-- The first next-state marginal of the same initial/policy/transition experiment. -/
def nextStateLaw (μ : Measure S) (π : Kernel S A) (P : Kernel (S × A) S) : Measure S :=
  ((μ ⊗ₘ π) ⊗ₘ P).map Prod.snd

instance nextStateLaw_probability (μ : Measure S) (π : Kernel S A)
    (P : Kernel (S × A) S) [IsProbabilityMeasure μ] [IsMarkovKernel π]
    [IsMarkovKernel P] : IsProbabilityMeasure (nextStateLaw μ π P) := by
  unfold nextStateLaw
  infer_instance

theorem actual_countable_first_state_marginal [Countable S] [Countable A]
    (μ : Measure S) (π : Kernel S A) (P : Kernel (S × A) S)
    [IsProbabilityMeasure μ] [IsMarkovKernel π] [IsMarkovKernel P] (t : S) :
    nextStateLaw μ π P {t} = ∑' s : S, ∑' a : A, μ {s} * π s {a} * P (s, a) {t} := by
  unfold nextStateLaw
  rw [Measure.map_apply measurable_snd (measurableSet_singleton t)]
  have hset : Prod.snd ⁻¹' ({t} : Set S) = (Set.univ : Set (S × A)) ×ˢ {t} := by
    ext z
    simp
  rw [hset, Measure.compProd_apply_prod MeasurableSet.univ
    (measurableSet_singleton t), setLIntegral_univ, lintegral_countable']
  rw [ENNReal.tsum_prod']
  simp_rw [actual_joint_kernel_atom_probability]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro a
  ring

def fairActionPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1/2 : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun (_ : Fin 2) _ => by norm_num)]
    norm_num [Fin.sum_univ_two])

def unsafeNextStatePMF (a : Fin 2) : PMF (Fin 2) :=
  PMF.ofFintype
    (fun s => ENNReal.ofReal
      (if s = 1 then (if a = 0 then (1/5 : ℝ) else 3/5)
              else (if a = 0 then (4/5 : ℝ) else 2/5))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro s _; split_ifs <;> norm_num)]
    by_cases ha : a = 0 <;> norm_num [Fin.sum_univ_two, ha])

def exampleInitial : Measure (Fin 2) := Measure.dirac 0
def fairPolicyKernel : Kernel (Fin 2) (Fin 2) := Kernel.const _ fairActionPMF.toMeasure
def unsafeTransitionKernel : Kernel (Fin 2 × Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable (fun z => (unsafeNextStatePMF z.2).toMeasure)

instance exampleInitial_probability : IsProbabilityMeasure exampleInitial := by
  unfold exampleInitial
  infer_instance
instance fairPolicyKernel_markov : IsMarkovKernel fairPolicyKernel := by
  unfold fairPolicyKernel
  infer_instance
instance unsafeTransitionKernel_markov : IsMarkovKernel unsafeTransitionKernel :=
  ⟨fun z => by change IsProbabilityMeasure (unsafeNextStatePMF z.2).toMeasure; infer_instance⟩

theorem actual_example_initial_is_a_point_mass (s : Fin 2) :
    exampleInitial {s} = if s = 0 then 1 else 0 := by
  simp [exampleInitial, Measure.dirac_apply', Pi.single_apply, eq_comm]

theorem actual_example_action_probabilities_are_one_half (s a : Fin 2) :
    fairPolicyKernel s {a} = ENNReal.ofReal (1/2 : ℝ) := by
  change fairActionPMF.toMeasure {a} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  simp [fairActionPMF]

theorem actual_example_conditional_unsafe_probabilities (s a : Fin 2) :
    unsafeTransitionKernel (s, a) {1} = ENNReal.ofReal (if a = 0 then (1/5 : ℝ) else 3/5) := by
  change (unsafeNextStatePMF a).toMeasure {1} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1 : Fin 2))]
  simp [unsafeNextStatePMF]

theorem actual_two_action_unsafe_state_probability_is_two_fifths :
    nextStateLaw exampleInitial fairPolicyKernel unsafeTransitionKernel {1} =
      ENNReal.ofReal (2/5 : ℝ) := by
  rw [actual_countable_first_state_marginal]
  simp_rw [actual_example_initial_is_a_point_mass, actual_example_action_probabilities_are_one_half,
    actual_example_conditional_unsafe_probabilities]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [tsum_fintype, Fin.sum_univ_two, h10, if_true, if_false,
    one_mul, zero_mul, zero_add, add_zero]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem actual_real_two_action_unsafe_state_probability_is_two_fifths :
    (nextStateLaw exampleInitial fairPolicyKernel unsafeTransitionKernel).real {1} = 2/5 := by
  change (nextStateLaw exampleInitial fairPolicyKernel unsafeTransitionKernel {1}).toReal = _
  rw [actual_two_action_unsafe_state_probability_is_two_fifths, ENNReal.toReal_ofReal (by norm_num)]

def deterministicPolicyKernel (a : Fin 2) : Kernel (Fin 2) (Fin 2) :=
  Kernel.const _ (Measure.dirac a)

instance deterministicPolicyKernel_markov (a : Fin 2) :
    IsMarkovKernel (deterministicPolicyKernel a) := by
  unfold deterministicPolicyKernel
  infer_instance

theorem actual_changing_the_policy_changes_the_next_state_law :
    nextStateLaw exampleInitial (deterministicPolicyKernel 0) unsafeTransitionKernel {1} =
      ENNReal.ofReal (1/5 : ℝ) ∧
    nextStateLaw exampleInitial (deterministicPolicyKernel 1) unsafeTransitionKernel {1} =
      ENNReal.ofReal (3/5 : ℝ) := by
  constructor <;> rw [actual_countable_first_state_marginal]
  all_goals
    simp_rw [actual_example_initial_is_a_point_mass, actual_example_conditional_unsafe_probabilities]
    norm_num [deterministicPolicyKernel, tsum_fintype, Fin.sum_univ_two,
      Measure.dirac_apply', Pi.single_apply]

end SafeLearning.CompleteAppliedProbabilityTrajectoryKernels30
