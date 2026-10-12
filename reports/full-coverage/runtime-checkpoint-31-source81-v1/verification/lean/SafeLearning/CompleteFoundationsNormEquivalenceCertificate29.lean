import SafeLearning.CompleteFoundationsNormExercises
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SafeLearning.CompleteFoundationsNormEquivalenceCertificate29

open Set
open scoped BoundedContinuousFunction
open CompleteFoundationsNormDuality

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_infinity_ball_has_the_dimension_scaled_euclidean_certificate
    (ε : ℝ) (hε : 0 ≤ ε) :
    {x : I → ℝ | ‖x‖ ≤ ε} ⊆
      {x | l2Norm x ≤ Real.sqrt (Fintype.card I) * ε} := by
  intro x hx
  exact actual_infinity_ball_in_euclidean_ball x ε hε hx

theorem actual_dimension_scaled_certificate_transfers_every_property
    (P : (I → ℝ) → Prop) (center : I → ℝ) (ε r : ℝ) (hε : 0 ≤ ε)
    (hr : Real.sqrt (Fintype.card I) * ε ≤ r)
    (hcertificate : ∀ x, l2Norm (x - center) ≤ r → P x) :
    ∀ x, ‖x - center‖ ≤ ε → P x := by
  intro x hx
  exact hcertificate x ((actual_infinity_ball_in_euclidean_ball (x-center) ε hε hx).trans hr)

theorem actual_constant_corner_is_inside_the_original_infinity_ball
    (ε : ℝ) (hε : 0 ≤ ε) : ‖(fun _ : I => ε)‖ ≤ ε := by
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro i
  simp [Real.norm_eq_abs,abs_of_nonneg hε]

theorem actual_euclidean_covering_radius_is_exactly_the_dimension_factor
    (ε r : ℝ) (hε : 0 ≤ ε) :
    ({x : I → ℝ | ‖x‖ ≤ ε} ⊆ {x | l2Norm x ≤ r}) ↔
      Real.sqrt (Fintype.card I) * ε ≤ r := by
  constructor
  · intro h
    have hc := h (actual_constant_corner_is_inside_the_original_infinity_ball (I:=I) ε hε)
    change l2Norm (fun _ : I => ε) ≤ r at hc
    rwa [actual_constant_vector_attains_dimension_conversion ε hε] at hc
  · intro h x hx
    exact (actual_infinity_ball_in_euclidean_ball x ε hε hx).trans h

theorem actual_positive_radius_in_dimension_at_least_two_needs_a_larger_cover
    (ε : ℝ) (hε : 0 < ε) (hd : 2 ≤ Fintype.card I) :
    ∃ x : I → ℝ, ‖x‖ ≤ ε ∧ ε < l2Norm x := by
  refine ⟨fun _ => ε,actual_constant_corner_is_inside_the_original_infinity_ball ε hε.le,?_⟩
  rw [actual_constant_vector_attains_dimension_conversion ε hε.le]
  have hd' : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hd
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card I from Nat.cast_nonneg _)
  have hn := Real.sqrt_nonneg (Fintype.card I : ℝ)
  have ht : 1 < Real.sqrt (Fintype.card I : ℝ) := by nlinarith
  nlinarith

theorem actual_one_dimensional_conversion_has_no_strict_radius_loss
    (ε : ℝ) (hε : 0 ≤ ε) (hd : Fintype.card I = 1) :
    {x : I → ℝ | ‖x‖ ≤ ε} ⊆ {x | l2Norm x ≤ ε} := by
  apply (actual_euclidean_covering_radius_is_exactly_the_dimension_factor ε ε hε).mpr
  simp [hd]

theorem actual_arbitrary_finite_dimensional_norms_are_equivalent
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    (e : E ≃ₗ[ℝ] F) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E, c * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ C * ‖x‖ := by
  letI : FiniteDimensional ℝ F := e.finiteDimensional
  let ec : E ≃L[ℝ] F := e.toContinuousLinearEquiv
  let K : ℝ := max ‖ec.symm.toContinuousLinearMap‖ 1
  let C : ℝ := max ‖ec.toContinuousLinearMap‖ 1
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨1/K,C,one_div_pos.mpr hK,hC,?_⟩
  intro x
  have hl : ‖x‖ ≤ K * ‖e x‖ := by
    calc
      ‖x‖ = ‖ec.symm (ec x)‖ := by simp
      _ ≤ ‖ec.symm.toContinuousLinearMap‖ * ‖ec x‖ := ec.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K * ‖e x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hu : ‖e x‖ ≤ C * ‖x‖ :=
    (ec.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨?_,hu⟩
  rw [one_div_mul_eq_div,div_le_iff₀ hK]
  simpa [mul_comm] using hl

abbrev Sequence := ℕ →ᵇ ℝ

def coordinateWeight (k : ℕ) : ℝ := 1 / ((k : ℝ)+1)

theorem actual_coordinate_weights_are_strictly_positive_and_at_most_one (k : ℕ) :
    0 < coordinateWeight k ∧ coordinateWeight k ≤ 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  constructor
  · exact one_div_pos.mpr (by positivity)
  · dsimp [coordinateWeight]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ)+1)).mpr
    linarith

def weightSequence : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete coordinateWeight 1 (by
    intro k
    rw [Real.norm_eq_abs,abs_of_pos (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1]
    exact (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).2)

def diagonalWeight : Sequence →ₗ[ℝ] Sequence where
  toFun x := weightSequence * x
  map_add' x y := by ext k; simp [mul_add]
  map_smul' a x := by ext k; simp [mul_comm,mul_left_comm]

theorem actual_diagonal_weight_is_injective : Function.Injective diagonalWeight := by
  intro x y h
  ext k
  have hh := congrArg (fun z : Sequence => z k) h
  change coordinateWeight k * x k = coordinateWeight k * y k at hh
  exact mul_left_cancel₀ (ne_of_gt (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1) hh

def spike (k : ℕ) : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun j => if j=k then 1 else 0) 1 (by
    intro j
    split_ifs <;> norm_num)

theorem actual_coordinate_spikes_have_supremum_norm_one (k : ℕ) : ‖spike k‖ = 1 := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro j
    change ‖if j=k then (1:ℝ) else 0‖ ≤ 1
    split_ifs <;> norm_num
  · simpa [spike] using (spike k).norm_coe_le_norm k

theorem actual_weighted_spike_norm_is_its_shrinking_coordinate_weight (k : ℕ) :
    ‖diagonalWeight (spike k)‖ = coordinateWeight k := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1.le).mpr
    intro j
    change ‖coordinateWeight j * (if j=k then (1:ℝ) else 0)‖ ≤ coordinateWeight k
    by_cases h : j=k
    · subst j; simp [abs_of_pos (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1]
    · simp [h,(actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1.le]
  · have h := (diagonalWeight (spike k)).norm_coe_le_norm k
    simpa [diagonalWeight,weightSequence,spike,Real.norm_eq_abs,abs_of_pos (actual_coordinate_weights_are_strictly_positive_and_at_most_one k).1] using h

theorem actual_two_sequence_norms_have_no_uniform_reverse_constant :
    ¬ ∃ C : ℝ, ∀ x : Sequence, ‖x‖ ≤ C * ‖diagonalWeight x‖ := by
  rintro ⟨C,hC⟩
  obtain ⟨k,hk⟩ := exists_nat_gt C
  have h := hC (spike k)
  rw [actual_coordinate_spikes_have_supremum_norm_one,
    actual_weighted_spike_norm_is_its_shrinking_coordinate_weight] at h
  have hp : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hh : C * coordinateWeight k < 1 := by
    dsimp [coordinateWeight]
    rw [mul_one_div,div_lt_iff₀ hp]
    linarith
  linarith

def WeightedSequence : Type := ULift Sequence

instance : AddCommGroup WeightedSequence := inferInstanceAs (AddCommGroup (ULift Sequence))
instance : Module ℝ WeightedSequence := inferInstanceAs (Module ℝ (ULift Sequence))

def downLinear : WeightedSequence →ₗ[ℝ] Sequence := ULift.moduleEquiv.toLinearMap
def weightedCopyMap : WeightedSequence →ₗ[ℝ] Sequence := diagonalWeight.comp downLinear

private theorem weightedCopy_injective : Function.Injective weightedCopyMap :=
  actual_diagonal_weight_is_injective.comp ULift.down_injective

instance : NormedAddCommGroup WeightedSequence :=
  NormedAddCommGroup.induced WeightedSequence Sequence weightedCopyMap.toAddMonoidHom weightedCopy_injective
instance : NormedSpace ℝ WeightedSequence :=
  NormedSpace.induced ℝ WeightedSequence Sequence weightedCopyMap

def rawEquivalence : Sequence ≃ₗ[ℝ] WeightedSequence := ULift.moduleEquiv.symm

theorem actual_weighted_copy_norm_is_the_second_genuine_norm (x : Sequence) :
    ‖rawEquivalence x‖ = ‖diagonalWeight x‖ := rfl

theorem actual_infinite_dimensional_normed_copies_are_not_equivalent :
    ¬ ∃ C : ℝ, ∀ x : Sequence, ‖x‖ ≤ C * ‖rawEquivalence x‖ := by
  simpa only [actual_weighted_copy_norm_is_the_second_genuine_norm] using
    actual_two_sequence_norms_have_no_uniform_reverse_constant

theorem actual_sequence_space_is_not_finite_dimensional : ¬ FiniteDimensional ℝ Sequence := by
  intro h
  letI : FiniteDimensional ℝ Sequence := h
  obtain ⟨c,C,hc,hC,hbounds⟩ := actual_arbitrary_finite_dimensional_norms_are_equivalent rawEquivalence
  apply actual_infinite_dimensional_normed_copies_are_not_equivalent
  refine ⟨1/c,?_⟩
  intro x
  rw [one_div_mul_eq_div,le_div_iff₀ hc]
  simpa [mul_comm] using (hbounds x).1

end SafeLearning.CompleteFoundationsNormEquivalenceCertificate29
