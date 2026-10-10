import SafeLearning.CompleteModulesKernel

set_option autoImplicit false
noncomputable section
open SafeLearning.CompleteModulesKernel
open scoped BigOperators
namespace SafeLearning.CompleteModulesPosterior

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]

def residualObjective (feature : I → H) (target : H) (regularizer : ℝ) (weight : I → ℝ) : ℝ :=
  ‖target-combination feature weight‖^2+regularizer*∑ i, (weight i)^2

theorem residual_objective_at_solution (feature : I → H) (target : H)
    (regularizer : ℝ) (weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    residualObjective feature target regularizer weight=posteriorVariance feature target weight := by
  rw [residualObjective,posterior_residual_norm_identity feature target weight regularizer hsystem]
  ring

theorem residual_objective_gap (feature : I → H) (target : H)
    (regularizer : ℝ) (weight other : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    residualObjective feature target regularizer other=
      residualObjective feature target regularizer weight+
      ‖combination feature (other-weight)‖^2+
      regularizer*∑ i, (other i-weight i)^2 := by
  have hcomb : combination feature other=combination feature weight+combination feature (other-weight) := by
    unfold combination
    simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
    abel
  have hnormal : ∀ i, inner ℝ (target-combination feature weight) (feature i)=regularizer*weight i := by
    intro i
    have h := normal_system_combination_inner feature target weight regularizer hsystem i
    rw [real_inner_comm (combination feature weight) (feature i),
      real_inner_comm target (feature i)] at h
    rw [inner_sub_left,h]
    ring
  have hcross : inner ℝ (target-combination feature weight) (combination feature (other-weight))=
      regularizer*∑ i, (weight i*(other i-weight i)) := by
    rw [inner_combination]
    simp only [Pi.sub_apply,hnormal,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsum : (∑ i, (other i)^2)=(∑ i, (weight i)^2)+
      2*(∑ i, weight i*(other i-weight i))+(∑ i, (other i-weight i)^2) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold residualObjective
  rw [hcomb,show target-(combination feature weight+combination feature (other-weight))=
      (target-combination feature weight)-combination feature (other-weight) by abel,
    norm_sub_sq_real,hcross,hsum]
  ring

theorem residual_objective_global_minimum (feature : I → H) (target : H)
    (regularizer : ℝ) (hl : 0 ≤ regularizer) (weight other : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    posteriorVariance feature target weight ≤ residualObjective feature target regularizer other := by
  rw [residual_objective_gap feature target regularizer weight other hsystem,
    residual_objective_at_solution feature target regularizer weight hsystem]
  have hn := sq_nonneg ‖combination feature (other-weight)‖
  have hs : 0 ≤ ∑ i, (other i-weight i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (other i-weight i))
  have hp := mul_nonneg hl hs
  linarith

theorem posterior_variance_regularization_monotone (feature : I → H) (target : H)
    (lower upper : ℝ) (hl : 0 ≤ lower) (horder : lower ≤ upper)
    (weightLower weightUpper : I → ℝ)
    (hLower : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weightLower j)+
      lower*weightLower i=inner ℝ (feature i) target)
    (hUpper : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weightUpper j)+
      upper*weightUpper i=inner ℝ (feature i) target) :
    posteriorVariance feature target weightLower ≤ posteriorVariance feature target weightUpper := by
  have hmin := residual_objective_global_minimum feature target lower hl weightLower weightUpper hLower
  have hs : 0 ≤ ∑ i, (weightUpper i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (weightUpper i))
  have hinc := mul_le_mul_of_nonneg_right horder hs
  have he := residual_objective_at_solution feature target upper weightUpper hUpper
  unfold residualObjective at hmin he
  linarith

theorem actual_posterior_regularization_monotone (feature : I → H) (target : H)
    (lower upper : ℝ) (hl : 0 < lower) (hu : 0 < upper) (horder : lower ≤ upper) :
    posteriorVariance feature target (posteriorWeights feature target lower hl) ≤
      posteriorVariance feature target (posteriorWeights feature target upper hu) := by
  exact posterior_variance_regularization_monotone feature target lower upper (le_of_lt hl)
    horder _ _ (posterior_weights_solve_system feature target lower hl)
    (posterior_weights_solve_system feature target upper hu)

end SafeLearning.CompleteModulesPosterior
