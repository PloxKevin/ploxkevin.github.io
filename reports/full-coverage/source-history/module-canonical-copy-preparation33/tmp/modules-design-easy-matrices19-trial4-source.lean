import SafeLearning.CompleteModulesCayley

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
namespace SafeLearning.CompleteModulesDesignEasyMatrices

def sourceWeight : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![3,1]
def sourceSkew : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-1,0]
def sourceRotation : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;1,0]
def sourceEmbedding : Matrix (Fin 2) (Fin 1) ℝ := !![1;0]

theorem actual_positive_diagonal_operator_norm_is_the_largest_entry
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(diagonal ![a,b] : Matrix (Fin 2) (Fin 2) ℝ)‖=max a b := by
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans ha (le_max_left _ _))).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
  · apply max_le
    · simpa [Real.norm_eq_abs,abs_of_nonneg ha] using norm_le_pi_norm ![a,b] 0
    · simpa [Real.norm_eq_abs,abs_of_nonneg hb] using norm_le_pi_norm ![a,b] 1

theorem actual_source_spectral_and_frobenius_norms :
    ‖sourceWeight‖=3 ∧
      Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, (sourceWeight i j)^2)=Real.sqrt 10 ∧
      3 ≤ Real.sqrt 10 := by
  refine ⟨?_,?_,?_⟩
  · simpa [sourceWeight] using (actual_positive_diagonal_operator_norm_is_the_largest_entry
      3 1 (by norm_num) (by norm_num))
  · norm_num [sourceWeight,Fin.sum_univ_two,diagonal_apply]
  · have hs := Real.sq_sqrt (show (0:ℝ)≤10 by norm_num)
    nlinarith [Real.sqrt_nonneg (10:ℝ)]

theorem actual_normalizing_by_the_lower_estimate_is_expansive :
    ‖((1/(5/2:ℝ)) • sourceWeight)‖=6/5 ∧ 1 < ‖((1/(5/2:ℝ)) • sourceWeight)‖ := by
  rw [norm_smul,actual_source_spectral_and_frobenius_norms.1]
  norm_num

theorem actual_frobenius_normalization_is_nonexpansive_and_rounded :
    ‖((1/Real.sqrt 10) • sourceWeight)‖=3/Real.sqrt 10 ∧
      ‖((1/Real.sqrt 10) • sourceWeight)‖≤1 ∧
      |3/Real.sqrt 10-948683/1000000|<1/2000000 := by
  have hp : 0 < Real.sqrt (10:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (show (0:ℝ)≤10 by norm_num)
  have hn : ‖((1/Real.sqrt 10) • sourceWeight)‖=3/Real.sqrt 10 := by
    rw [norm_smul,actual_source_spectral_and_frobenius_norms.1,Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hp)]
    ring
  refine ⟨hn,?_,?_⟩
  · rw [hn]
    exact (div_le_one hp).mpr actual_source_spectral_and_frobenius_norms.2.2
  · rw [abs_lt]
    constructor
    · have hlo : (948683/1000000-1/2000000:ℝ)*Real.sqrt 10<3 := by nlinarith
      have hd : (948683/1000000-1/2000000:ℝ)<3/Real.sqrt 10 := (lt_div_iff₀ hp).mpr hlo
      linarith
    · have hhi : (3:ℝ)<(948683/1000000+1/2000000)*Real.sqrt 10 := by nlinarith
      have hd : (3:ℝ)/Real.sqrt 10<(948683/1000000+1/2000000) := (div_lt_iff₀ hp).mpr hhi
      linarith

theorem actual_positive_normalizer_requires_an_upper_bound
    {rows cols : Type*} [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
    (W : Matrix rows cols ℝ) (denominator : ℝ) (hden : 0 < denominator) :
    ‖((1/denominator) • W)‖≤1 ↔ ‖W‖≤denominator := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hden)]
  simpa [div_eq_mul_inv,mul_comm] using (div_le_one hden : ‖W‖/denominator≤1 ↔ _)

open scoped Matrix.Norms.Frobenius in
theorem actual_source_genuine_frobenius_norm : ‖sourceWeight‖=Real.sqrt 10 := by
  rw [sourceWeight,Matrix.frobenius_norm_diagonal]
  have h:=EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 ![(3:ℝ),1])
  norm_num [Fin.sum_univ_two] at h
  have hs:=Real.sq_sqrt (show (0:ℝ)≤10 by norm_num)
  nlinarith [norm_nonneg (WithLp.toLp 2 ![(3:ℝ),1]),Real.sqrt_nonneg (10:ℝ)]

theorem actual_source_skew_and_inverse :
    sourceSkewᵀ = -sourceSkew ∧
      (1+sourceSkew)⁻¹=(1/2:ℝ) • !![1,-1;1,1] := by
  constructor
  · ext i j;fin_cases i <;> fin_cases j <;> norm_num [sourceSkew,transpose_apply]
  · norm_num [sourceSkew,Matrix.inv_def,Matrix.det_fin_two,Matrix.adjugate_fin_two,
      Matrix.one_fin_two]

theorem actual_source_cayley_is_the_right_angle_rotation :
    CompleteModulesCayley.actualCayley sourceSkew=sourceRotation ∧
      sourceRotationᵀ*sourceRotation=1 ∧
      sourceRotation *ᵥ ![(3:ℝ),-4]=![4,3] := by
  have hq : CompleteModulesCayley.actualCayley sourceSkew=sourceRotation := by
    rw [CompleteModulesCayley.actualCayley,actual_source_skew_and_inverse.2]
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [sourceSkew,sourceRotation,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  refine ⟨hq,?_,?_⟩
  · rw [←hq]
    exact CompleteModulesCayley.actual_cayley_is_orthogonal _ actual_source_skew_and_inverse.1
  · ext i;fin_cases i <;> norm_num [sourceRotation,Matrix.mulVec, dotProduct,Fin.sum_univ_two]

theorem actual_rotation_preserves_every_norm_and_the_source_norms
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖WithLp.toLp 2 (sourceRotation *ᵥ WithLp.ofLp x)‖=‖x‖ ∧
      ‖WithLp.toLp 2 ![(3:ℝ),-4]‖=5 ∧ ‖WithLp.toLp 2 ![(4:ℝ),3]‖=5 := by
  have hn (v : Fin 2→ℝ) : ‖WithLp.toLp 2 v‖^2=v 0^2+v 1^2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  refine ⟨?_,?_,?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hn,show ‖x‖^2=(WithLp.ofLp x 0)^2+(WithLp.ofLp x 1)^2 by simpa using hn (WithLp.ofLp x)]
    simp [sourceRotation,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  · have h:=hn ![(3:ℝ),-4];norm_num at h;nlinarith [norm_nonneg (WithLp.toLp 2 ![(3:ℝ),-4])]
  · have h:=hn ![(4:ℝ),3];norm_num at h;nlinarith [norm_nonneg (WithLp.toLp 2 ![(4:ℝ),3])]

theorem actual_rectangular_gram_matrices_and_forward_backward_values :
    sourceEmbeddingᵀ*sourceEmbedding=1 ∧
      sourceEmbedding*sourceEmbeddingᵀ=diagonal ![(1:ℝ),0] ∧
      sourceEmbedding*sourceEmbeddingᵀ≠1 ∧
      (∀ x : ℝ,sourceEmbedding *ᵥ ![x]=![x,0] ∧ ‖WithLp.toLp 2 (sourceEmbedding *ᵥ ![x])‖=|x|) ∧
      sourceEmbeddingᵀ *ᵥ ![(0:ℝ),2]=0 ∧ ‖WithLp.toLp 2 ![(0:ℝ),2]‖=2 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · ext i j;fin_cases i;fin_cases j;norm_num [sourceEmbedding,Matrix.mul_apply,Fin.sum_univ_two]
  · ext i j;fin_cases i <;> fin_cases j <;>norm_num [sourceEmbedding,Matrix.mul_apply,Fin.sum_univ_one,diagonal_apply]
  · intro h;have hh:=congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ=> A 1 1) h
    norm_num [sourceEmbedding,Matrix.mul_apply,Fin.sum_univ_one] at hh
  · intro x
    have he : sourceEmbedding *ᵥ ![x]=![x,0] := by
      ext i;fin_cases i <;> simp [sourceEmbedding,Matrix.mulVec,dotProduct,Fin.sum_univ_one]
    refine ⟨he,?_⟩;rw [he]
    have h:=EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 ![x,(0:ℝ)])
    simp [Fin.sum_univ_two] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 ![x,(0:ℝ)]),abs_nonneg x,sq_abs x]
  · ext i;fin_cases i;norm_num [sourceEmbedding,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · have h:=EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 ![(0:ℝ),2])
    norm_num [Fin.sum_univ_two] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 ![(0:ℝ),2])]

theorem actual_every_backward_norm_preserved_requires_orthonormal_rows
    {rows cols : Type*} [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
    (W : Matrix rows cols ℝ)
    (h : ∀ y : EuclideanSpace ℝ rows, ‖Matrix.toEuclideanLin Wᵀ y‖=‖y‖) :
    W*Wᵀ=1 := by
  have hi := (LinearMap.norm_map_iff_inner_map_map (f:=Matrix.toEuclideanLin Wᵀ)).mp h
  ext i j
  have he := hi (WithLp.toLp 2 (Pi.single i (1:ℝ))) (WithLp.toLp 2 (Pi.single j (1:ℝ)))
  change (inner ℝ (WithLp.toLp 2 (Wᵀ *ᵥ (Pi.single i (1:ℝ) : rows → ℝ)))
      (WithLp.toLp 2 (Wᵀ *ᵥ (Pi.single j (1:ℝ) : rows → ℝ))) =
      inner ℝ (WithLp.toLp 2 (Pi.single i (1:ℝ) : rows → ℝ))
        (WithLp.toLp 2 (Pi.single j (1:ℝ) : rows → ℝ))) at he
  simpa [PiLp.inner_apply,RCLike.inner_apply,Matrix.mulVec_single_one,
    Matrix.col_apply,Matrix.mul_apply,Matrix.one_apply,Pi.single_apply,mul_comm] using he

end SafeLearning.CompleteModulesDesignEasyMatrices
