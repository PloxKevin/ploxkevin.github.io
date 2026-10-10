import SafeLearning.CompleteModulesLipSDPNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesLipSDPProduct

open CompleteModulesLipSDP CompleteModulesLipSDPNetwork
variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

/-- The norm here is the Euclidean induced operator norm, not a coordinate norm. -/
theorem actual_spectral_matrix_gain (weight : Matrix K I ℝ) (input : I → ℝ) :
    ‖WithLp.toLp 2 (weight *ᵥ input)‖ ≤ ‖weight‖*‖WithLp.toLp 2 input‖ := by
  exact Matrix.l2_opNorm_mulVec weight (WithLp.toLp 2 input)

theorem slope_restricted_hidden_nonexpansive (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1) (first second : K → ℝ) :
    ‖WithLp.toLp 2 (fun k => activation (first k)-activation (second k))‖ ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  have hsq : (∑ k, (activation (first k)-activation (second k))^2) ≤
      ∑ k, (first k-second k)^2 := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨slope,hl,hu,he⟩ := hactivation (first k) (second k)
    rw [he]
    have hs : slope^2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (first k-second k))]
  have h := hsq
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at h
  change ‖WithLp.toLp 2 (fun k => activation (first k)-activation (second k))‖^2 ≤
    ‖WithLp.toLp 2 (first-second)‖^2 at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => activation (first k)-activation (second k))),
    norm_nonneg (WithLp.toLp 2 (first-second))]

theorem actual_network_product_bound (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1) (first second : I → ℝ) :
    ‖WithLp.toLp 2 (oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation first-
      oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation second)‖ ≤
      (‖lastWeight‖*‖firstWeight‖)*‖WithLp.toLp 2 (first-second)‖ := by
  have hhidden : ‖WithLp.toLp 2 (hiddenValues firstWeight firstBias activation first-
      hiddenValues firstWeight firstBias activation second)‖ ≤
      ‖WithLp.toLp 2 (firstWeight *ᵥ (first-second))‖ := by
    have h := slope_restricted_hidden_nonexpansive activation hactivation
      (firstWeight *ᵥ first+firstBias) (firstWeight *ᵥ second+firstBias)
    change ‖WithLp.toLp 2 (fun k => activation ((firstWeight *ᵥ first) k+firstBias k)-
      activation ((firstWeight *ᵥ second) k+firstBias k))‖ ≤ _
    simpa only [Pi.sub_apply,Pi.add_apply,add_sub_add_right_eq_sub,← Matrix.mulVec_sub] using h
  calc
    _ = ‖WithLp.toLp 2 (lastWeight *ᵥ (hiddenValues firstWeight firstBias activation first-
        hiddenValues firstWeight firstBias activation second))‖ := by
      congr 2
      simp [oneHiddenNetwork,Matrix.mulVec_sub]
    _ ≤ ‖lastWeight‖*‖WithLp.toLp 2 (hiddenValues firstWeight firstBias activation first-
        hiddenValues firstWeight firstBias activation second)‖ := actual_spectral_matrix_gain _ _
    _ ≤ ‖lastWeight‖*‖WithLp.toLp 2 (firstWeight *ᵥ (first-second))‖ :=
      mul_le_mul_of_nonneg_left hhidden (norm_nonneg _)
    _ ≤ ‖lastWeight‖*(‖firstWeight‖*‖WithLp.toLp 2 (first-second)‖) :=
      mul_le_mul_of_nonneg_left (actual_spectral_matrix_gain _ _) (norm_nonneg _)
    _ = _ := by ring

def productCertificate (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (rho t : ℝ) : Matrix (I ⊕ K) (I ⊕ K) ℝ :=
  Matrix.fromBlocks (-rho • (1 : Matrix I I ℝ)) (t • firstWeightᵀ)
    (t • firstWeight) (lastWeightᵀ*lastWeight-(2*t) • (1 : Matrix K K ℝ))

theorem layer_certificate_is_product_matrix (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (rho t : ℝ) :
    blockCertificate firstWeight lastWeight 0 1 rho (fun _ => t)=
      productCertificate firstWeight lastWeight rho t := by
  have hd : Matrix.diagonal (fun _ : K => t)=t • (1 : Matrix K K ℝ) := by
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply,Matrix.smul_apply]
  unfold blockCertificate productCertificate
  rw [hd]
  simp only [mul_zero,zero_mul,zero_smul,zero_sub,zero_add,one_smul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.smul_apply] <;> ring

theorem product_certificate_is_hermitian (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (rho t : ℝ) :
    (productCertificate firstWeight lastWeight rho t).IsHermitian := by
  unfold productCertificate
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  · simp
  · have hg : (lastWeightᵀ*lastWeight).IsHermitian := by
      simpa using Matrix.isHermitian_conjTranspose_mul_self lastWeight
    exact hg.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

theorem product_matrix_quadratic_identity (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (rho t : ℝ) (input : I → ℝ) (hidden : K → ℝ) :
    quadratic (productCertificate firstWeight lastWeight rho t) (Sum.elim input hidden)=
      ‖WithLp.toLp 2 (lastWeight *ᵥ hidden)‖^2-rho*‖WithLp.toLp 2 input‖^2+
        t*(‖WithLp.toLp 2 (firstWeight *ᵥ input)‖^2-
          ‖WithLp.toLp 2 hidden‖^2-‖WithLp.toLp 2 (hidden-firstWeight *ᵥ input)‖^2) := by
  rw [← layer_certificate_is_product_matrix,← canonical_certificate_is_stated_block_matrix]
  unfold canonicalCertificate
  rw [certificate_quadratic_identity]
  simp only [Matrix.fromCols_mulVec_sumElim,Matrix.zero_mulVec,Matrix.one_mulVec,
    zero_add,add_zero,mul_zero,zero_mul,zero_add,zero_sub,zero_add,zero_mul]
  simp only [squared_norm_of_coordinates,Pi.sub_apply]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem product_bound_is_actual_lipsdp_feasible (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) :
    (-(blockCertificate firstWeight lastWeight 0 1
      (‖lastWeight‖^2*‖firstWeight‖^2) (fun _ => ‖lastWeight‖^2))).PosSemidef := by
  rw [layer_certificate_is_product_matrix]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (product_certificate_is_hermitian _ _ _ _).neg
  intro vector
  let input : I → ℝ := fun i => vector (Sum.inl i)
  let hidden : K → ℝ := fun k => vector (Sum.inr k)
  have hv : vector=Sum.elim input hidden := by ext i; cases i <;> rfl
  rw [hv]
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
  change 0 ≤ -quadratic _ _
  rw [product_matrix_quadratic_identity]
  have hfirst := actual_spectral_matrix_gain firstWeight input
  have hlast := actual_spectral_matrix_gain lastWeight hidden
  have hfirstsq : ‖WithLp.toLp 2 (firstWeight *ᵥ input)‖^2 ≤
      ‖firstWeight‖^2*‖WithLp.toLp 2 input‖^2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (firstWeight *ᵥ input)),
      mul_nonneg (norm_nonneg firstWeight) (norm_nonneg (WithLp.toLp 2 input))]
  have hlastsq : ‖WithLp.toLp 2 (lastWeight *ᵥ hidden)‖^2 ≤
      ‖lastWeight‖^2*‖WithLp.toLp 2 hidden‖^2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (lastWeight *ᵥ hidden)),
      mul_nonneg (norm_nonneg lastWeight) (norm_nonneg (WithLp.toLp 2 hidden))]
  have hbound := mul_le_mul_of_nonneg_left hfirstsq (sq_nonneg ‖lastWeight‖)
  have hres := mul_nonneg (sq_nonneg ‖lastWeight‖)
    (sq_nonneg ‖WithLp.toLp 2 (hidden-firstWeight *ᵥ input)‖)
  nlinarith

def feasibleLayerRhos (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ) : Set ℝ :=
  {rho | 0 ≤ rho ∧ ∃ t : ℝ, 0 ≤ t ∧
    (-(blockCertificate firstWeight lastWeight 0 1 rho (fun _ => t))).PosSemidef}

def optimalLayerRho (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ) : ℝ :=
  sInf (feasibleLayerRhos firstWeight lastWeight)

theorem actual_layer_optimization_never_exceeds_product
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ) :
    Real.sqrt (optimalLayerRho firstWeight lastWeight) ≤ ‖lastWeight‖*‖firstWeight‖ := by
  have hmem : ‖lastWeight‖^2*‖firstWeight‖^2 ∈ feasibleLayerRhos firstWeight lastWeight :=
    ⟨mul_nonneg (sq_nonneg _) (sq_nonneg _),‖lastWeight‖^2,sq_nonneg _,
      product_bound_is_actual_lipsdp_feasible firstWeight lastWeight⟩
  have hbound : BddBelow (feasibleLayerRhos firstWeight lastWeight) :=
    ⟨0,fun _ h => h.1⟩
  have hi : optimalLayerRho firstWeight lastWeight ≤ (‖lastWeight‖*‖firstWeight‖)^2 := by
    unfold optimalLayerRho
    have h := csInf_le hbound hmem
    nlinarith
  have h := Real.sqrt_le_sqrt hi
  rwa [Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h

theorem actual_layer_optimum_is_nonnegative
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ) :
    0 ≤ optimalLayerRho firstWeight lastWeight := by
  apply le_csInf
  · exact ⟨‖lastWeight‖^2*‖firstWeight‖^2,
      mul_nonneg (sq_nonneg _) (sq_nonneg _),‖lastWeight‖^2,sq_nonneg _,
      product_bound_is_actual_lipsdp_feasible firstWeight lastWeight⟩
  · intro rho h
    exact h.1

end SafeLearning.CompleteModulesLipSDPProduct
