import SafeLearning.CompleteModulesSafeOptEightPointPosteriors

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptCosineGap
open CompleteModulesSafeOptEightPointPosteriors

def sourceCoordinate (i : Fin 3) : ℝ := (i.val:ℝ)
def actualCosineValue (i : Fin 3) : ℝ := Real.cos (Real.pi*sourceCoordinate i)
def actualCosineKernel (i j : Fin 3) : ℝ :=
  Real.cos (Real.pi*(sourceCoordinate i-sourceCoordinate j))

theorem actual_cosine_gap_values_are_one_minus_one_one :
    actualCosineValue=(![1,-1,1] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> norm_num [actualCosineValue,sourceCoordinate]
  rw [mul_comm,Real.cos_two_pi]

theorem actual_cosine_kernel_is_exactly_the_source_rank_one_matrix (i j : Fin 3) :
    actualCosineKernel i j=actualCosineValue i*actualCosineValue j := by
  have hi : Real.sin (Real.pi*sourceCoordinate i)=0 := by
    simpa [sourceCoordinate,mul_comm] using Real.sin_nat_mul_pi i.val
  have hj : Real.sin (Real.pi*sourceCoordinate j)=0 := by
    simpa [sourceCoordinate,mul_comm] using Real.sin_nat_mul_pi j.val
  simp [actualCosineKernel,mul_sub,Real.cos_sub,hi,hj,actualCosineValue]

theorem actual_cosine_gap_kernel_is_genuinely_positive_semidefinite :
    (Matrix.of actualCosineKernel).PosSemidef := by
  have he : Matrix.of actualCosineKernel=Matrix.vecMulVec actualCosineValue (star actualCosineValue) := by
    ext i j
    simp [actual_cosine_kernel_is_exactly_the_source_rank_one_matrix,Matrix.vecMulVec]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_self_star actualCosineValue

@[instance_reducible]
def actualCosineRKHS : RKHS ℝ ℝ (Fin 3) ℝ where
  coeCLM := ContinuousLinearMap.pi (fun i => actualCosineValue i • ContinuousLinearMap.id ℝ ℝ)
  coeCLM_injective := by
    intro a b he
    have h := congrFun he 0
    simpa [actualCosineValue,sourceCoordinate] using h

theorem actual_constructed_rkhs_has_the_literal_cosine_kernel_and_source_function_norm_one :
    letI : RKHS ℝ ℝ (Fin 3) ℝ := actualCosineRKHS
    (∀ i j, (RKHS.kernel ℝ i j) 1=actualCosineKernel i j) ∧
      (∀ i, (RKHS.coeCLM ℝ) (1:ℝ) i=actualCosineValue i) ∧ ‖(1:ℝ)‖=1 := by
  letI : RKHS ℝ ℝ (Fin 3) ℝ := actualCosineRKHS
  have heval (a : ℝ) (i : Fin 3) : (RKHS.coeCLM ℝ) a i=actualCosineValue i*a := by rfl
  have hker (i : Fin 3) : RKHS.kerFun ℝ i 1=actualCosineValue i := by
    have h := RKHS.inner_kerFun (H:=ℝ) i (1:ℝ) (1:ℝ)
    simp only [RCLike.inner_apply,conj_trivial,one_mul,mul_one] at h
    change RKHS.kerFun ℝ i 1=(RKHS.coeCLM ℝ) (1:ℝ) i at h
    simpa [heval] using h
  refine ⟨?_,?_,by norm_num⟩
  · intro i j
    have h := RKHS.kernel_inner (H:=ℝ) i j (1:ℝ) (1:ℝ)
    rw [hker i,hker j] at h
    simpa [RCLike.inner_apply,conj_trivial,mul_comm,
      actual_cosine_kernel_is_exactly_the_source_rank_one_matrix] using h
  · intro i
    rw [heval,mul_one]

theorem actual_noiseless_observation_at_zero_determines_every_source_rkhs_function_value
    (coefficient : ℝ) :
    (∀ i, coefficient*actualCosineValue i=actualCosineValue i) ↔
      coefficient*actualCosineValue 0=1 := by
  have h0 : actualCosineValue 0=1 := by norm_num [actualCosineValue,sourceCoordinate]
  rw [h0]
  constructor
  · intro h
    simpa [h0] using h 0
  · intro h i
    have hc : coefficient=1 := by simpa using h
    rw [hc,one_mul]

theorem actual_noiseless_gp_posterior_from_zero_is_exact_at_all_three_points
    (i : Fin 3) :
    actualGPMean actualCosineKernel (fun _ : Fin 1 => 0) 0 (fun _ => 1) i=actualCosineValue i ∧
      actualGPVariance actualCosineKernel (fun _ : Fin 1 => 0) 0 i=0 := by
  have hp := actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
    actualCosineKernel 0 i 0 1
  simp_rw [actual_cosine_kernel_is_exactly_the_source_rank_one_matrix] at hp
  have hi : (actualCosineValue i)^2=1 := by
    rw [actual_cosine_gap_values_are_one_minus_one_one]
    fin_cases i <;> norm_num
  have h0 : actualCosineValue 0=1 := by norm_num [actualCosineValue,sourceCoordinate]
  simpa [h0,← pow_two,hi] using hp

theorem actual_gp_lower_bound_certifies_the_other_island_and_correctly_excludes_the_unsafe_middle
    (beta : ℝ) :
    {i : Fin 3 | (0:ℝ)≤actualGPMean actualCosineKernel (fun _ : Fin 1 => 0) 0
      (fun _ => 1) i-beta*Real.sqrt
        (actualGPVariance actualCosineKernel (fun _ : Fin 1 => 0) 0 i)}={0,2} ∧
      actualCosineValue 0≥0 ∧ actualCosineValue 2≥0 ∧ actualCosineValue 1<0 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i
    simp only [mem_setOf_eq]
    rw [(actual_noiseless_gp_posterior_from_zero_is_exact_at_all_three_points i).1,
      (actual_noiseless_gp_posterior_from_zero_is_exact_at_all_three_points i).2]
    rw [actual_cosine_gap_values_are_one_minus_one_one]
    fin_cases i <;> norm_num
  all_goals rw [actual_cosine_gap_values_are_one_minus_one_one];norm_num

end SafeLearning.CompleteModulesSafeOptCosineGap
