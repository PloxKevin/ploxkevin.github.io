import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSplitRelu
open Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
open SafeLearning.CompleteModulesLipSDP SafeLearning.CompleteModulesLipSDPProduct
  SafeLearning.CompleteModulesLipSDPWalkthrough

def actualFirstWeight : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => (![1,-1] : Fin 2 → ℝ) i
def actualLastWeight : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1,-1]
def actualNetwork (input : ℝ) : ℝ :=
  (actualLastWeight *ᵥ (fun i => max ((actualFirstWeight *ᵥ (fun _ => input)) i) 0)) 0

theorem actual_first_weight_coordinate_energy (input : Fin 1 → ℝ) :
    (∑ i : Fin 2,((actualFirstWeight *ᵥ input) i)^2)=2*(input 0)^2 := by
  norm_num [actualFirstWeight,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_first_weight_has_true_spectral_norm_sqrt_two : ‖actualFirstWeight‖=Real.sqrt 2 := by
  have hu : ‖actualFirstWeight‖ ≤ Real.sqrt 2 := by
    apply actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
    intro input
    rw [actual_first_weight_coordinate_energy]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    exact le_refl _
  have hl := actual_spectral_matrix_gain actualFirstWeight (fun _ : Fin 1 => (1:ℝ))
  have hi : ‖WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))‖^2=1 := by
    rw [squared_norm_of_coordinates];norm_num [Fin.sum_univ_succ]
  have ho : ‖WithLp.toLp 2 (actualFirstWeight *ᵥ (fun _ : Fin 1 => (1:ℝ)))‖^2=2 := by
    rw [squared_norm_of_coordinates,actual_first_weight_coordinate_energy]
    norm_num
  have hn : ‖WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))‖=1 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))]
  rw [hn,mul_one] at hl
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [norm_nonneg actualFirstWeight,Real.sqrt_nonneg (2:ℝ),
    norm_nonneg (WithLp.toLp 2 (actualFirstWeight *ᵥ (fun _ : Fin 1 => (1:ℝ))))]

theorem actual_second_weight_and_product_have_true_spectral_norms :
    ‖actualLastWeight‖=Real.sqrt 2 ∧ ‖actualLastWeight‖*‖actualFirstWeight‖=2 := by
  have he : actualLastWeight=actualFirstWeightᵀ := by
    ext i j;fin_cases i;fin_cases j <;> norm_num [actualLastWeight,actualFirstWeight]
  have hn : ‖actualLastWeight‖=‖actualFirstWeight‖ := by
    rw [he];exact Matrix.l2_opNorm_conjTranspose actualFirstWeight
  refine ⟨hn.trans actual_first_weight_has_true_spectral_norm_sqrt_two,?_⟩
  rw [hn,actual_first_weight_has_true_spectral_norm_sqrt_two]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem actual_bias_free_two_layer_relu_network_is_the_identity (input : ℝ) :
    actualNetwork input=max input 0-max (-input) 0 ∧ actualNetwork input=input := by
  have he : actualNetwork input=max input 0-max (-input) 0 := by
    norm_num [actualNetwork,actualFirstWeight,actualLastWeight,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ]
    by_cases hp : 0 ≤ input
    · rw [max_eq_left hp,max_eq_right (by linarith : -input ≤ 0)];ring
    · rw [max_eq_right (le_of_not_ge hp),max_eq_left (by linarith : 0 ≤ -input)];ring
  refine ⟨he,?_⟩
  rw [he]
  by_cases hp : 0 ≤ input
  · rw [max_eq_left hp,max_eq_right (by linarith : -input ≤ 0)];ring
  · rw [max_eq_right (le_of_not_ge hp),max_eq_left (by linarith : 0 ≤ -input)];ring

theorem actual_global_lipschitz_constant_is_exactly_one :
    IsLeast {constant : ℝ≥0 | LipschitzWith constant actualNetwork} 1 := by
  have he : actualNetwork=id := funext (fun input =>
    (actual_bias_free_two_layer_relu_network_is_the_identity input).2)
  refine ⟨?_,?_⟩
  · rw [he];exact LipschitzWith.id
  · intro constant hc
    have h := hc.dist_le_mul (1:ℝ) 0
    rw [(actual_bias_free_two_layer_relu_network_is_the_identity 1).2,
      (actual_bias_free_two_layer_relu_network_is_the_identity 0).2] at h
    norm_num [Real.dist_eq] at h
    exact_mod_cast h

theorem actual_source_certificate_thresholds_and_class_boundary
    (radius : ℝ) (hr : 0 ≤ radius) :
    actualNetwork 2=2 ∧
      (0 < actualNetwork 2-(‖actualLastWeight‖*‖actualFirstWeight‖)*radius ↔ radius<1) ∧
      (0 < actualNetwork 2-radius ↔ radius<2) ∧
      ((∀ error : ℝ, |error| ≤ radius → 0 < actualNetwork (2+error)) ↔ radius<2) ∧
      actualNetwork 0=0 ∧ |(2:ℝ)-0|=2 := by
  have hn := actual_bias_free_two_layer_relu_network_is_the_identity
  have hp := actual_second_weight_and_product_have_true_spectral_norms.2
  refine ⟨(hn 2).2,?_,?_,?_,(hn 0).2,by norm_num⟩
  · rw [(hn 2).2,hp];constructor <;> intro h <;> linarith
  · rw [(hn 2).2];constructor <;> intro h <;> linarith
  · constructor
    · intro h
      have hx := h (-radius) (by rw [abs_neg,abs_of_nonneg hr])
      rw [(hn (2+-radius)).2] at hx
      linarith
    · intro h error he
      rw [(hn (2+error)).2]
      linarith [(abs_le.mp he).1]

end SafeLearning.CompleteAppliedSplitRelu
