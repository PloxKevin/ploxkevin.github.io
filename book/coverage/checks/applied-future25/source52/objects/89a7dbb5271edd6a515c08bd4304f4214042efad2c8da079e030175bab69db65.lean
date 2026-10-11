import SafeLearning.Modules
import SafeLearning.BookApplications

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesKernel

variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]

def featureKernel (feature : X → H) (x y : X) : ℝ := inner ℝ (feature x) (feature y)

def combination (feature : I → H) (weight : I → ℝ) : H := ∑ i, weight i • feature i

theorem combination_inner (feature : I → H) (weight : I → ℝ) (target : H) :
    inner ℝ (combination feature weight) target = ∑ i, weight i*inner ℝ (feature i) target := by
  simp [combination,sum_inner,real_inner_smul_left]

theorem inner_combination (feature : I → H) (weight : I → ℝ) (target : H) :
    inner ℝ target (combination feature weight) = ∑ i, weight i*inner ℝ target (feature i) := by
  simp [combination,inner_sum,real_inner_smul_right]

theorem gram_quadratic_eq_norm (feature : I → H) (weight : I → ℝ) :
    (∑ i, ∑ j, weight i*weight j*inner ℝ (feature i) (feature j)) =
      ‖combination feature weight‖^2 := by
  rw [← real_inner_self_eq_norm_sq,combination_inner]
  simp_rw [inner_combination,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem feature_kernel_gram_nonnegative (feature : X → H) (input : I → X) (weight : I → ℝ) :
    0 ≤ ∑ i, ∑ j, weight i*weight j*featureKernel feature (input i) (input j) := by
  change 0 ≤ ∑ i, ∑ j, weight i*weight j*inner ℝ (feature (input i)) (feature (input j))
  rw [gram_quadratic_eq_norm]
  exact sq_nonneg _

theorem kernel_distance_identity (feature : X → H) (x y : X) :
    ‖feature x-feature y‖^2 = featureKernel feature x x+featureKernel feature y y-
      2*featureKernel feature x y := by
  simp only [featureKernel,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  ring

theorem kernel_distance_is_feature_distance (feature : X → H) (x y : X) :
    Real.sqrt (featureKernel feature x x+featureKernel feature y y-
      2*featureKernel feature x y) = ‖feature x-feature y‖ := by
  rw [← kernel_distance_identity,Real.sqrt_sq (norm_nonneg _)]

theorem actual_feature_function_kernel_bound (feature : X → H) (coefficient : H) (x y : X) :
    |inner ℝ coefficient (feature x)-inner ℝ coefficient (feature y)| ≤
      ‖coefficient‖*Real.sqrt (featureKernel feature x x+featureKernel feature y y-
        2*featureKernel feature x y) := by
  rw [kernel_distance_is_feature_distance,← inner_sub_right]
  exact abs_real_inner_le_norm _ _

def posteriorVariance (feature : I → H) (target : H) (weight : I → ℝ) : ℝ :=
  ‖target‖^2-∑ i, weight i*inner ℝ (feature i) target

theorem normal_system_combination_inner (feature : I → H) (target : H)
    (weight : I → ℝ) (regularizer : ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) (i : I) :
    inner ℝ (feature i) (combination feature weight) =
      inner ℝ (feature i) target-regularizer*weight i := by
  rw [inner_combination]
  have h := hsystem i
  simp_rw [mul_comm (inner ℝ (feature i) (feature _))] at h
  linarith

theorem posterior_residual_norm_identity (feature : I → H) (target : H)
    (weight : I → ℝ) (regularizer : ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    ‖target-combination feature weight‖^2 = posteriorVariance feature target weight-
      regularizer*∑ i, (weight i)^2 := by
  have hnorm : ‖combination feature weight‖^2 =
      (∑ i, weight i*inner ℝ (feature i) target)-regularizer*∑ i, (weight i)^2 := by
    rw [← real_inner_self_eq_norm_sq,combination_inner]
    simp_rw [normal_system_combination_inner feature target weight regularizer hsystem]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcross : inner ℝ target (combination feature weight) =
      ∑ i, weight i*inner ℝ (feature i) target := by
    rw [real_inner_comm,combination_inner]
  rw [norm_sub_sq_real,hcross,hnorm]
  unfold posteriorVariance
  ring

theorem posterior_variance_nonnegative (feature : I → H) (target : H)
    (weight : I → ℝ) (regularizer : ℝ) (hl : 0 ≤ regularizer)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    0 ≤ posteriorVariance feature target weight := by
  have h := posterior_residual_norm_identity feature target weight regularizer hsystem
  have hs : 0 ≤ ∑ i, (weight i)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hp := mul_nonneg hl hs
  nlinarith [sq_nonneg ‖target-combination feature weight‖]

theorem posterior_residual_norm_bound (feature : I → H) (target : H)
    (weight : I → ℝ) (regularizer : ℝ) (hl : 0 ≤ regularizer)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    ‖target-combination feature weight‖ ≤ Real.sqrt (posteriorVariance feature target weight) := by
  have h := posterior_residual_norm_identity feature target weight regularizer hsystem
  have hs : 0 ≤ ∑ i, (weight i)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hp := mul_nonneg hl hs
  have hv := posterior_variance_nonnegative feature target weight regularizer hl hsystem
  have hsq := Real.sq_sqrt hv
  nlinarith [norm_nonneg (target-combination feature weight),
    Real.sqrt_nonneg (posteriorVariance feature target weight)]

theorem noiseless_posterior_error (feature : I → H) (target coefficient : H)
    (weight : I → ℝ) (regularizer B : ℝ) (hl : 0 ≤ regularizer) (hB : ‖coefficient‖ ≤ B)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=inner ℝ (feature i) target) :
    |inner ℝ coefficient target-∑ i, weight i*inner ℝ coefficient (feature i)| ≤
      B*Real.sqrt (posteriorVariance feature target weight) := by
  rw [← inner_combination,← inner_sub_right]
  calc
    _ ≤ ‖coefficient‖*‖target-combination feature weight‖ := abs_real_inner_le_norm _ _
    _ ≤ B*Real.sqrt (posteriorVariance feature target weight) :=
      mul_le_mul hB (posterior_residual_norm_bound feature target weight regularizer hl hsystem)
        (norm_nonneg _) (le_trans (norm_nonneg _) hB)

def normalOperator (feature : I → H) (regularizer : ℝ) : (I → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun weight i := (∑ j, inner ℝ (feature i) (feature j)*weight j)+regularizer*weight i
  map_add' := by
    intro a b
    ext i
    simp [mul_add,Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro scalar a
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (inner ℝ (feature i) (feature _)) scalar,mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem normal_operator_quadratic_identity (feature : I → H) (regularizer : ℝ)
    (weight : I → ℝ) :
    (∑ i, weight i*(normalOperator feature regularizer weight) i) =
      ‖combination feature weight‖^2+regularizer*∑ i, (weight i)^2 := by
  simp only [normalOperator,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  rw [← gram_quadratic_eq_norm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

theorem positive_normal_operator_injective (feature : I → H) (regularizer : ℝ)
    (hl : 0 < regularizer) : Function.Injective (normalOperator feature regularizer) := by
  have hz : ∀ weight, normalOperator feature regularizer weight=0 → weight=0 := by
    intro weight he
    have hq := normal_operator_quadratic_identity feature regularizer weight
    rw [he] at hq
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hq
    have hs : 0 ≤ ∑ i, (weight i)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hzero : (∑ i, (weight i)^2)=0 := by
      have hn := sq_nonneg ‖combination feature weight‖
      nlinarith
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (weight j))).mp hzero
    exact sq_eq_zero_iff.mp (hi i (Finset.mem_univ i))
  intro a b hab
  have he : normalOperator feature regularizer (a-b)=0 := by
    rw [map_sub,hab,sub_self]
  exact sub_eq_zero.mp (hz (a-b) he)

theorem regularized_normal_system_exists_unique (feature : I → H) (regularizer : ℝ)
    (hl : 0 < regularizer) (rhs : I → ℝ) :
    ∃! weight : I → ℝ, ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=rhs i := by
  have hinj := positive_normal_operator_injective feature regularizer hl
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨weight,hweight⟩ := hsurj rhs
  refine ⟨weight,?_,?_⟩
  · intro i
    exact congrFun hweight i
  · intro other hother
    apply hinj
    ext i
    exact (hother i).trans (congrFun hweight i).symm

def posteriorWeights (feature : I → H) (target : H) (regularizer : ℝ)
    (hl : 0 < regularizer) : I → ℝ :=
  Classical.choose (regularized_normal_system_exists_unique feature regularizer hl
    (fun i => inner ℝ (feature i) target)).exists

theorem posterior_weights_solve_system (feature : I → H) (target : H) (regularizer : ℝ)
    (hl : 0 < regularizer) :
    ∀ i, (∑ j, inner ℝ (feature i) (feature j)*posteriorWeights feature target regularizer hl j)+
      regularizer*posteriorWeights feature target regularizer hl i=inner ℝ (feature i) target :=
  Classical.choose_spec (regularized_normal_system_exists_unique feature regularizer hl
    (fun i => inner ℝ (feature i) target)).exists

theorem actual_regularized_noiseless_error (feature : I → H) (target coefficient : H)
    (regularizer B : ℝ) (hl : 0 < regularizer) (hB : ‖coefficient‖ ≤ B) :
    |inner ℝ coefficient target-∑ i, posteriorWeights feature target regularizer hl i*
      inner ℝ coefficient (feature i)| ≤
      B*Real.sqrt (posteriorVariance feature target (posteriorWeights feature target regularizer hl)) := by
  apply noiseless_posterior_error feature target coefficient _ regularizer B (le_of_lt hl) hB
  exact posterior_weights_solve_system feature target regularizer hl

def ridgeObjective (feature : I → H) (labels : I → ℝ) (regularizer : ℝ) (function : H) : ℝ :=
  (∑ i, (inner ℝ function (feature i)-labels i)^2)+regularizer*‖function‖^2

theorem normal_system_fit_residual (feature : I → H) (labels weight : I → ℝ)
    (regularizer : ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=labels i) (i : I) :
    inner ℝ (combination feature weight) (feature i)-labels i = -regularizer*weight i := by
  rw [real_inner_comm,inner_combination]
  have h := hsystem i
  simp_rw [mul_comm (inner ℝ (feature i) (feature _))] at h
  linarith

theorem ridge_objective_gap_identity (feature : I → H) (labels weight : I → ℝ)
    (regularizer : ℝ) (increment : H)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=labels i) :
    ridgeObjective feature labels regularizer (combination feature weight+increment) =
      ridgeObjective feature labels regularizer (combination feature weight)+
      (∑ i, (inner ℝ increment (feature i))^2)+regularizer*‖increment‖^2 := by
  have heach : ∀ i, (inner ℝ (combination feature weight+increment) (feature i)-labels i)^2-
      (inner ℝ (combination feature weight) (feature i)-labels i)^2-
      (inner ℝ increment (feature i))^2 =
      -2*regularizer*(weight i*inner ℝ increment (feature i)) := by
    intro i
    rw [inner_add_left]
    have h := normal_system_fit_residual feature labels weight regularizer hsystem i
    linear_combination 2*(inner ℝ increment (feature i))*h
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _ => heach i)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hs
  have hcross : (∑ i, weight i*inner ℝ increment (feature i)) =
      inner ℝ (combination feature weight) increment := by
    rw [combination_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  rw [hcross] at hs
  simp only [ridgeObjective,norm_add_sq_real]
  linarith

theorem ridge_objective_global_minimum (feature : I → H) (labels weight : I → ℝ)
    (regularizer : ℝ) (hl : 0 ≤ regularizer)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=labels i) (competitor : H) :
    ridgeObjective feature labels regularizer (combination feature weight) ≤
      ridgeObjective feature labels regularizer competitor := by
  have hg := ridge_objective_gap_identity feature labels weight regularizer
    (competitor-combination feature weight) hsystem
  rw [add_sub_cancel] at hg
  have hs : 0 ≤ ∑ i, (inner ℝ (competitor-combination feature weight) (feature i))^2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hn := mul_nonneg hl (sq_nonneg ‖competitor-combination feature weight‖)
  linarith

theorem ridge_objective_minimum_unique (feature : I → H) (labels weight : I → ℝ)
    (regularizer : ℝ) (hl : 0 < regularizer)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)+
      regularizer*weight i=labels i) (competitor : H)
    (hequal : ridgeObjective feature labels regularizer competitor =
      ridgeObjective feature labels regularizer (combination feature weight)) :
    competitor=combination feature weight := by
  have hg := ridge_objective_gap_identity feature labels weight regularizer
    (competitor-combination feature weight) hsystem
  rw [add_sub_cancel,hequal] at hg
  have hs : 0 ≤ ∑ i, (inner ℝ (competitor-combination feature weight) (feature i))^2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hn := sq_nonneg ‖competitor-combination feature weight‖
  have hzsq : ‖competitor-combination feature weight‖^2=0 := by
    have hprod : regularizer*‖competitor-combination feature weight‖^2 ≤ 0 := by linarith
    exact le_antisymm ((mul_le_mul_iff_of_pos_left hl).mp (by simpa only [mul_zero] using hprod)) hn
  have hz : ‖competitor-combination feature weight‖=0 := by
    exact sq_eq_zero_iff.mp hzsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem ridge_minimizer_exists_unique (feature : I → H) (labels : I → ℝ)
    (regularizer : ℝ) (hl : 0 < regularizer) :
    ∃! function : H, ∀ competitor, ridgeObjective feature labels regularizer function ≤
      ridgeObjective feature labels regularizer competitor := by
  obtain ⟨weight,hweight,hunique⟩ := regularized_normal_system_exists_unique feature regularizer hl labels
  refine ⟨combination feature weight,?_,?_⟩
  · exact ridge_objective_global_minimum feature labels weight regularizer (le_of_lt hl) hweight
  · intro other hother
    apply ridge_objective_minimum_unique feature labels weight regularizer hl hweight other
    exact le_antisymm (hother _) (ridge_objective_global_minimum feature labels weight
      regularizer (le_of_lt hl) hweight other)

theorem squared_exponential_kernel_distance (radius lengthscale : ℝ)
    (hr : 0 ≤ radius) (hl : 0 < lengthscale) :
    Real.sqrt (2*(1-Real.exp (-(radius^2/(2*lengthscale^2))))) ≤ radius/lengthscale := by
  have hden : 0 < 2*lengthscale^2 := by positivity
  have ha : 0 ≤ radius^2/(2*lengthscale^2) := div_nonneg (sq_nonneg _) (le_of_lt hden)
  have he := Real.add_one_le_exp (-(radius^2/(2*lengthscale^2)))
  have he1 : Real.exp (-(radius^2/(2*lengthscale^2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hv : 0 ≤ 2*(1-Real.exp (-(radius^2/(2*lengthscale^2)))) := by linarith
  have hs := Real.sq_sqrt hv
  have heq : 2*(radius^2/(2*lengthscale^2))=(radius/lengthscale)^2 := by
    field_simp
    <;> ring
  have hratio := div_nonneg hr (le_of_lt hl)
  nlinarith [Real.sqrt_nonneg (2*(1-Real.exp (-(radius^2/(2*lengthscale^2)))))]

theorem squared_exponential_function_lipschitz [PseudoMetricSpace X]
    (feature : X → H) (coefficient : H) (lengthscale B : ℝ)
    (hl : 0 < lengthscale) (hB : ‖coefficient‖ ≤ B)
    (hkernel : ∀ x y, featureKernel feature x y=
      Real.exp (-((dist x y)^2/(2*lengthscale^2)))) :
    ∀ x y, |inner ℝ coefficient (feature x)-inner ℝ coefficient (feature y)| ≤
      (B/lengthscale)*dist x y := by
  intro x y
  have hbound := actual_feature_function_kernel_bound feature coefficient x y
  rw [hkernel x x,hkernel y y,hkernel x y,dist_self] at hbound
  norm_num at hbound
  have hs := squared_exponential_kernel_distance (dist x y) lengthscale (dist_nonneg) hl
  have hsame : (1+1-2*Real.exp (-((dist x y)^2/(2*lengthscale^2)))) =
      2*(1-Real.exp (-((dist x y)^2/(2*lengthscale^2)))) := by ring
  rw [← hsame] at hs
  calc
    _ ≤ ‖coefficient‖*Real.sqrt (1+1-2*Real.exp (-((dist x y)^2/(2*lengthscale^2)))) := by
      simpa only [one_add_one_eq_two] using hbound
    _ ≤ B*(dist x y/lengthscale) := mul_le_mul hB hs (Real.sqrt_nonneg _)
      (le_trans (norm_nonneg _) hB)
    _ = (B/lengthscale)*dist x y := by ring

theorem kernel_bound_equality_iff (feature : X → H) (coefficient : H) (x y : X) :
    |inner ℝ coefficient (feature x)-inner ℝ coefficient (feature y)| =
      ‖coefficient‖*Real.sqrt (featureKernel feature x x+featureKernel feature y y-
        2*featureKernel feature x y) ↔
      feature x=feature y ∨ ∃ scalar : ℝ, coefficient=scalar • (feature x-feature y) := by
  rw [kernel_distance_is_feature_distance,← inner_sub_right,real_inner_comm,
    mul_comm ‖coefficient‖]
  have hCS : ‖inner ℝ (feature x-feature y) coefficient‖ =
      ‖feature x-feature y‖*‖coefficient‖ ↔
      feature x-feature y=0 ∨ ∃ scalar : ℝ, coefficient=scalar • (feature x-feature y) :=
    (norm_inner_eq_norm_tfae ℝ (feature x-feature y) coefficient).out 1 3
  simpa only [Real.norm_eq_abs,sub_eq_zero] using hCS

theorem independent_gram_system_exists_unique (feature : I → H)
    (hfeature : LinearIndependent ℝ feature) (labels : I → ℝ) :
    ∃! weight : I → ℝ, ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=labels i := by
  have hinj : Function.Injective (normalOperator feature 0) := by
    have hz : ∀ weight, normalOperator feature 0 weight=0 → weight=0 := by
      intro weight he
      have hq := normal_operator_quadratic_identity feature 0 weight
      rw [he] at hq
      simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_mul,add_zero] at hq
      have hcomb : combination feature weight=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hq.symm)
      exact funext ((Fintype.linearIndependent_iff.mp hfeature) weight hcomb)
    intro a b hab
    have he : normalOperator feature 0 (a-b)=0 := by rw [map_sub,hab,sub_self]
    exact sub_eq_zero.mp (hz (a-b) he)
  obtain ⟨weight,hweight⟩ := (LinearMap.injective_iff_surjective.mp hinj) labels
  refine ⟨weight,?_,?_⟩
  · intro i
    simpa only [normalOperator,LinearMap.coe_mk,AddHom.coe_mk,zero_mul,add_zero] using congrFun hweight i
  · intro other hother
    apply hinj
    ext i
    simp only [normalOperator,LinearMap.coe_mk,AddHom.coe_mk,zero_mul,add_zero]
    have hw : (∑ j, inner ℝ (feature i) (feature j)*weight j)=labels i := by
      simpa only [normalOperator,LinearMap.coe_mk,AddHom.coe_mk,zero_mul,add_zero] using congrFun hweight i
    exact (hother i).trans hw.symm

theorem interpolant_norm_gap (feature : I → H) (labels weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=labels i)
    (candidate : H) (hdata : ∀ i, inner ℝ candidate (feature i)=labels i) :
    ‖candidate‖^2 = ‖combination feature weight‖^2+
      ‖candidate-combination feature weight‖^2 := by
  have hf : ∀ i, inner ℝ (combination feature weight) (feature i)=labels i := by
    intro i
    rw [real_inner_comm,inner_combination]
    simpa only [mul_comm] using hsystem i
  have ho : inner ℝ (combination feature weight) (candidate-combination feature weight)=0 := by
    rw [combination_inner]
    apply Finset.sum_eq_zero
    intro i hi
    rw [real_inner_comm,inner_sub_left,hdata i,hf i,sub_self,mul_zero]
  have hn := norm_add_sq_real (combination feature weight) (candidate-combination feature weight)
  rw [add_sub_cancel,ho,mul_zero,add_zero] at hn
  exact hn

theorem interpolant_minimum_norm (feature : I → H) (labels weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=labels i)
    (candidate : H) (hdata : ∀ i, inner ℝ candidate (feature i)=labels i) :
    ‖combination feature weight‖ ≤ ‖candidate‖ := by
  have h := interpolant_norm_gap feature labels weight hsystem candidate hdata
  nlinarith [sq_nonneg ‖candidate-combination feature weight‖,
    norm_nonneg candidate,norm_nonneg (combination feature weight)]

theorem interpolant_minimum_unique (feature : I → H) (labels weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=labels i)
    (candidate : H) (hdata : ∀ i, inner ℝ candidate (feature i)=labels i)
    (hequal : ‖candidate‖=‖combination feature weight‖) :
    candidate=combination feature weight := by
  have h := interpolant_norm_gap feature labels weight hsystem candidate hdata
  rw [hequal] at h
  have hz : ‖candidate-combination feature weight‖^2=0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

section ActualRKHS
variable [CompleteSpace H] [RKHS ℝ H X ℝ]

def scalarSection (x : X) : H := RKHS.kerFun H x 1
def scalarKernel (x y : X) : ℝ := featureKernel (scalarSection (H:=H)) x y

theorem scalar_section_reproduces (function : H) (x : X) :
    inner ℝ function (scalarSection x)=function x := by
  simp [scalarSection]

theorem scalar_kernel_is_actual_kernel (x y : X) :
    scalarKernel (H:=H) x y=(RKHS.kernel H x y) 1 := by
  unfold scalarKernel featureKernel
  rw [real_inner_comm]
  simp [scalarSection]

theorem actual_rkhs_kernel_bound (function : H) (x y : X) :
    |function x-function y| ≤ ‖function‖*Real.sqrt
      (scalarKernel (H:=H) x x+scalarKernel (H:=H) y y-2*scalarKernel (H:=H) x y) := by
  simpa only [scalarKernel,scalar_section_reproduces] using
    actual_feature_function_kernel_bound (scalarSection (H:=H)) function x y

theorem actual_rkhs_kernel_equality (function : H) (x y : X) :
    |function x-function y| = ‖function‖*Real.sqrt
      (scalarKernel (H:=H) x x+scalarKernel (H:=H) y y-2*scalarKernel (H:=H) x y) ↔
      scalarSection (H:=H) x=scalarSection (H:=H) y ∨
        ∃ scalar : ℝ, function=scalar • (scalarSection x-scalarSection y) := by
  simpa only [scalarKernel,scalar_section_reproduces] using
    kernel_bound_equality_iff (scalarSection (H:=H)) function x y

theorem actual_rkhs_se_lipschitz [PseudoMetricSpace X]
    (function : H) (lengthscale B : ℝ) (hl : 0 < lengthscale) (hB : ‖function‖ ≤ B)
    (hkernel : ∀ x y, scalarKernel (H:=H) x y=
      Real.exp (-((dist x y)^2/(2*lengthscale^2)))) :
    ∀ x y, |function x-function y| ≤ (B/lengthscale)*dist x y := by
  simpa only [scalar_section_reproduces] using
    squared_exponential_function_lipschitz (scalarSection (H:=H)) function lengthscale B hl hB hkernel

def actualRidgeObjective (input : I → X) (labels : I → ℝ) (regularizer : ℝ) (function : H) : ℝ :=
  (∑ i, (function (input i)-labels i)^2)+regularizer*‖function‖^2

theorem actual_ridge_objective_is_feature_objective (input : I → X) (labels : I → ℝ)
    (regularizer : ℝ) (function : H) :
    actualRidgeObjective input labels regularizer function=
      ridgeObjective (fun i => scalarSection (H:=H) (input i)) labels regularizer function := by
  simp only [actualRidgeObjective,ridgeObjective,scalar_section_reproduces]

theorem actual_rkhs_ridge_minimizer_exists_unique (input : I → X) (labels : I → ℝ)
    (regularizer : ℝ) (hl : 0 < regularizer) :
    ∃! function : H, ∀ competitor : H, actualRidgeObjective input labels regularizer function ≤
      actualRidgeObjective input labels regularizer competitor := by
  simpa only [← actual_ridge_objective_is_feature_objective] using
    ridge_minimizer_exists_unique (fun i => scalarSection (H:=H) (input i)) labels regularizer hl

theorem actual_rkhs_ridge_solution (input : I → X) (labels weight : I → ℝ)
    (regularizer : ℝ) (hl : 0 < regularizer)
    (hsystem : ∀ i, (∑ j, scalarKernel (H:=H) (input i) (input j)*weight j)+
      regularizer*weight i=labels i) :
    (∀ x, (combination (fun i => scalarSection (H:=H) (input i)) weight) x=
      ∑ i, weight i*scalarKernel (H:=H) x (input i)) ∧
    (∀ competitor : H, actualRidgeObjective input labels regularizer
      (combination (fun i => scalarSection (H:=H) (input i)) weight) ≤
      actualRidgeObjective input labels regularizer competitor) := by
  constructor
  · intro x
    rw [← scalar_section_reproduces,combination_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    rfl
  · intro competitor
    simp only [actual_ridge_objective_is_feature_objective]
    exact ridge_objective_global_minimum _ labels weight regularizer (le_of_lt hl) hsystem competitor

end ActualRKHS
end SafeLearning.CompleteModulesKernel
