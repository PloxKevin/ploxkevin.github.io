import SafeLearning.CompleteModulesSafeOptGPInformationBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesSafeOptFiniteInformationBound

open CompleteFoundationsSequentialLogDet CompleteModulesSafeOptGPInformationBudget

/-- The exact spectral product for a positive semidefinite real matrix.
Every normalized factor is at least one, including zero eigenvalues. -/
theorem actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    {index : Type*} [Fintype index] [DecidableEq index]
    (G : Matrix index index ℝ) (hG : G.PosSemidef) (a : ℝ) (ha : 0 ≤ a) :
    (1 + a • G).det = ∏ i, (1 + a * hG.isHermitian.eigenvalues i) ∧
      1 ≤ (1 + a • G).det := by
  let U := hG.isHermitian.eigenvectorUnitary
  have hdiag : Matrix.diagonal (fun i => 1 + a * hG.isHermitian.eigenvalues i) =
      1 + a • Matrix.diagonal hG.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hconj : (1 + a • G) = Unitary.conjStarAlgAut ℝ _ U
      (Matrix.diagonal (fun i => 1 + a * hG.isHermitian.eigenvalues i)) := by
    rw [hdiag, map_add, map_one, map_smul]
    simpa only [U, RCLike.ofReal_real_eq_id, Function.id_comp] using
      congrArg (fun M : Matrix index index ℝ => 1 + a • M) hG.isHermitian.spectral_theorem
  have hu : (U : Matrix index index ℝ).det * (star U : Matrix index index ℝ).det = 1 := by
    simpa only [Unitary.coe_star, Matrix.det_mul, Matrix.det_one] using
      congrArg Matrix.det (Unitary.coe_mul_star_self U)
  have hdet : (1 + a • G).det = ∏ i, (1 + a * hG.isHermitian.eigenvalues i) := by
    rw [hconj, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc
      _ = ((U : Matrix index index ℝ).det * (star U : Matrix index index ℝ).det) *
          (∏ i, (1 + a * hG.isHermitian.eigenvalues i)) := by ring
      _ = _ := by rw [hu, one_mul]
  refine ⟨hdet, ?_⟩
  rw [hdet]
  calc
    (1 : ℝ) = ∏ _i : index, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by norm_num)
      (fun i _ => le_add_of_nonneg_right (mul_nonneg ha (hG.eigenvalues_nonneg i)))

/-- Every repeated finite design for an arbitrary normalized finite PSD
kernel has information at most |X|/2 log(1+T/lambda). The finite dimension
comes from the derived whole-domain real kernel features. -/
theorem actual_normalized_finite_kernel_every_design_information_has_the_cardinality_log_bound
    {X : Type*} [Fintype X] [DecidableEq X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda : ℝ) (hlambda : 0 < lambda)
    (T : ℕ) (design : Fin T → X) :
    actualKernelDesignInformation kernel lambda T design ∈
      Icc 0 ((Fintype.card X : ℝ) / 2 * Real.log (1 + (T : ℝ) / lambda)) := by
  obtain ⟨features, hfeatures⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  let Phi : Matrix (Fin T) X ℝ := fun i j => features (design i) j
  let G := featureGram Phi
  have hG : G.PosSemidef := by
    simpa only [G, featureGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Phi
  have htrace : G.trace ≤ (T : ℝ) := by
    change (∑ j : X, ∑ i : Fin T, features (design i) j * features (design i) j) ≤ (T : ℝ)
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin T, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        have h := hnormalized (design i)
        rw [hfeatures] at h
        exact h)
      _ = _ := by simp
  have heigen : ∀ i, hG.isHermitian.eigenvalues i ≤ (T : ℝ) := by
    intro i
    have hs := Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j) (Finset.mem_univ i)
    have hsum : (∑ j, hG.isHermitian.eigenvalues j) = G.trace := by
      simpa using hG.isHermitian.trace_eq_sum_eigenvalues.symm
    rw [hsum] at hs
    exact hs.trans htrace
  have hspectral := actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    G hG lambda⁻¹ (inv_nonneg.mpr hlambda.le)
  have hdetbound : (1 + lambda⁻¹ • G).det ≤ (1 + (T : ℝ) / lambda) ^ Fintype.card X := by
    rw [hspectral.1]
    calc
      _ ≤ ∏ _i : X, (1 + (T : ℝ) / lambda) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity)
          (fun i _ => by simpa only [div_eq_mul_inv, mul_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_left (heigen i) (inv_nonneg.mpr hlambda.le)) 1)
      _ = _ := by simp
  have hgram : kernelGram Phi = Matrix.of (fun i j : Fin T => kernel (design i) (design j)) := by
    ext i j
    change features (design i) ⬝ᵥ features (design j) = kernel (design i) (design j)
    exact (hfeatures (design i) (design j)).symm
  have hdet : (1 + lambda⁻¹ • kernelGram Phi).det = (1 + lambda⁻¹ • G).det := by
    simpa only [G, featureGram, kernelGram, Matrix.mul_smul, Matrix.smul_mul] using
      CompleteFoundationsUniversalMatrices.actual_sylvester_determinant_identity (lambda⁻¹ • Phi) Phiᵀ
  have hpositive : 0 < (1 + lambda⁻¹ • G).det := lt_of_lt_of_le zero_lt_one hspectral.2
  have hlogbound := Real.log_le_log hpositive hdetbound
  rw [Real.log_pow] at hlogbound
  unfold actualKernelDesignInformation
  rw [← hgram, hdet]
  refine ⟨mul_nonneg (by norm_num) (Real.log_nonneg hspectral.2), ?_⟩
  nlinarith

/-- The actual attained repeated-design maximum inherits the same explicit
finite-domain logarithmic information bound, rather than assuming Gamma. -/
theorem actual_normalized_finite_kernel_maximum_information_has_the_cardinality_log_bound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda : ℝ) (hlambda : 0 < lambda) (T : ℕ) :
    actualFiniteMaximumKernelInformationGain kernel lambda T ∈
      Icc 0 ((Fintype.card X : ℝ) / 2 * Real.log (1 + (T : ℝ) / lambda)) := by
  obtain ⟨design, hdesign⟩ :=
    (actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design kernel lambda T).1
  rw [← hdesign]
  exact actual_normalized_finite_kernel_every_design_information_has_the_cardinality_log_bound
    kernel hkernel hnormalized lambda hlambda T design

end SafeLearning.CompleteModulesSafeOptFiniteInformationBound
