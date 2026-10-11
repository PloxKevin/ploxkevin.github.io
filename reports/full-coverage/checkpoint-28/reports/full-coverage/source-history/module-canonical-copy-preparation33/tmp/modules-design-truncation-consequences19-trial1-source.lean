import SafeLearning.CompleteModulesDesignTruncation

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignTruncationConsequences
open CompleteModulesDesignTruncation

theorem actual_rational_remainder_has_the_printed_rounding_and_is_not_equal :
    |(1/5:ℝ)^3/6-133333/100000000|<1/200000000 ∧
      (1/5:ℝ)^3/6>133333/100000000 := by norm_num

theorem actual_zero_activations_really_reduce_the_stack_gain
    (n : ℕ) (x y : EuclideanSpace ℝ (Fin 2)) :
    sourceStack (fun _ _=>0) (n+1) x=0 ∧
      sourceStack (fun _ _=>0) (n+1) y=0 ∧
      ‖sourceStack (fun _ _=>0) (n+1) x-sourceStack (fun _ _=>0) (n+1) y‖=0 := by
  simp [sourceStack]

theorem actual_identity_activation_ten_stack_is_not_one_lipschitz :
    ¬ ∀ x y : EuclideanSpace ℝ (Fin 2),
      ‖sourceStack (fun _ x=>x) 10 x-sourceStack (fun _ x=>x) 10 y‖≤‖x-y‖ := by
  intro h
  let linear : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Matrix.toEuclideanCLM (sourceTaylor^10)
  have hb : ‖linear‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound (by norm_num)
    intro x
    have hx:=h x 0
    rw [actual_identity_activation_stack_is_the_true_taylor_power,
      actual_identity_activation_stack_is_the_true_taylor_power] at hx
    simpa only [Matrix.mulVec_zero,WithLp.toLp_zero,sub_zero,one_mul] using hx
  have hn : ‖linear‖=‖sourceTaylor^10‖ := Matrix.l2_opNorm_toEuclideanCLM _
  rw [hn] at hb
  exact not_le_of_gt actual_identity_activation_ten_matrix_gain_is_strictly_greater_than_one.2 hb

end SafeLearning.CompleteModulesDesignTruncationConsequences
