import SafeLearning.CompleteModulesGaussianSchurConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianSequentialAlgebra
variable {I : Type*} [Fintype I] [DecidableEq I]

def augmented (A : Matrix I I ℝ) (d : I → ℝ) (v : ℝ) : Matrix (I ⊕ Unit) (I ⊕ Unit) ℝ :=
  fromBlocks A (Matrix.of (fun (i : I) (_ : Unit) => d i)) (Matrix.of (fun (_ : Unit) (i : I) => d i)) (Matrix.of (fun (_ _ : Unit) => v))
def innovationVariance (A : Matrix I I ℝ) (d : I → ℝ) (v : ℝ) : ℝ :=
  v-d ⬝ᵥ (A⁻¹*ᵥd)
def innovationCross (A : Matrix I I ℝ) (d c : I → ℝ) (r : ℝ) : ℝ :=
  r-d ⬝ᵥ (A⁻¹*ᵥc)
def lastWeight (A : Matrix I I ℝ) (d c : I → ℝ) (v r : ℝ) : ℝ :=
  innovationCross A d c r/innovationVariance A d v
def sequentialWeights (A : Matrix I I ℝ) (d c : I → ℝ) (v r : ℝ) : I ⊕ Unit → ℝ :=
  Sum.elim (A⁻¹*ᵥc-lastWeight A d c v r • (A⁻¹*ᵥd)) (fun _ => lastWeight A d c v r)

theorem actual_invertible_old_covariance_and_nonzero_innovation_make_the_joint_covariance_invertible
    (A : Matrix I I ℝ) (d : I → ℝ) (v : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) : IsUnit (augmented A d v) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  apply isUnit_fromBlocks_iff_of_invertible₁₁.mpr
  have he : Matrix.of (fun (_ _ : Unit) => v)-Matrix.of (fun (_ : Unit) (i : I) => d i)*⅟A*Matrix.of (fun (i : I) (_ : Unit) => d i)=
      Matrix.of (fun (_ _ : Unit) => innovationVariance A d v) := by
    ext i j
    simp only [sub_apply,mul_apply,Matrix.of_apply,invOf_eq_nonsing_inv,Fintype.sum_unique]
    simp [innovationVariance,dotProduct,mulVec,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [he]
  apply (isUnit_iff_isUnit_det _).mpr
  simpa only [det_unique] using (isUnit_iff_ne_zero.mpr hs)

theorem actual_sequential_regression_weights_solve_the_joint_covariance_system
    (A : Matrix I I ℝ) (d c : I → ℝ) (v r : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) :
    augmented A d v*ᵥsequentialWeights A d c v r=Sum.elim c (fun _ => r) := by
  have hc : A*ᵥ(A⁻¹*ᵥc)=c := by
    rw [mulVec_mulVec,mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hA),one_mulVec]
  have hd : A*ᵥ(A⁻¹*ᵥd)=d := by
    rw [mulVec_mulVec,mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hA),one_mulVec]
  have hw : lastWeight A d c v r*innovationVariance A d v=innovationCross A d c r := by
    exact div_mul_cancel₀ _ hs
  rw [augmented,sequentialWeights,fromBlocks_mulVec]
  apply funext
  intro k
  cases k with
  | inl i =>
    simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,mulVec_sub,mulVec_smul,hc,hd,
      Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    simp [mulVec,dotProduct,mul_comm]
  | inr u =>
    simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,Pi.add_apply,mulVec, dotProduct,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Fintype.sum_unique,Finset.mul_sum,
      Finset.sum_sub_distrib]
    simp only [innovationVariance,innovationCross,dotProduct,mulVec] at hw
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    have hm : (∑ i,d i*(lastWeight A d c v r*(A⁻¹*ᵥd) i))=
        lastWeight A d c v r*(d ⬝ᵥ (A⁻¹*ᵥd)) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hm]
    simp only [innovationVariance,innovationCross] at hw
    linarith

theorem actual_joint_inverse_regression_weights_equal_the_sequential_weights
    (A : Matrix I I ℝ) (d c : I → ℝ) (v r : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) :
    (augmented A d v)⁻¹*ᵥ(Sum.elim c (fun _ => r))=sequentialWeights A d c v r := by
  have hu := actual_invertible_old_covariance_and_nonzero_innovation_make_the_joint_covariance_invertible A d v hA hs
  rw [← actual_sequential_regression_weights_solve_the_joint_covariance_system A d c v r hA hs,
    mulVec_mulVec,nonsing_inv_mul _ ((augmented A d v).isUnit_iff_isUnit_det.mp hu),one_mulVec]

lemma actual_symmetric_inverse_cross_terms_commute
    (A : Matrix I I ℝ) (d c : I → ℝ) (hA : Aᵀ=A) :
    d ⬝ᵥ (A⁻¹*ᵥc)=c ⬝ᵥ (A⁻¹*ᵥd) := by
  rw [dotProduct_mulVec,←mulVec_transpose,transpose_nonsing_inv,hA,dotProduct_comm]

theorem actual_sequential_and_joint_gaussian_regression_means_are_identical
    (A : Matrix I I ℝ) (d c y : I → ℝ) (v r z : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) (hSymm : Aᵀ=A) :
    ((augmented A d v)⁻¹*ᵥ(Sum.elim c (fun _ => r))) ⬝ᵥ (Sum.elim y (fun _ => z))=
      c ⬝ᵥ (A⁻¹*ᵥy)+lastWeight A d c v r*(z-d ⬝ᵥ (A⁻¹*ᵥy)) := by
  rw [actual_joint_inverse_regression_weights_equal_the_sequential_weights A d c v r hA hs,
    sequentialWeights,sumElim_dotProduct_sumElim,sub_dotProduct,smul_dotProduct]
  have hc := actual_symmetric_inverse_cross_terms_commute A c y hSymm
  have hd := actual_symmetric_inverse_cross_terms_commute A d y hSymm
  rw [dotProduct_comm (A⁻¹*ᵥc),←hc,dotProduct_comm (A⁻¹*ᵥd),←hd]
  simp only [dotProduct,Fintype.sum_unique,smul_eq_mul]
  ring

theorem actual_sequential_and_joint_gaussian_regression_variances_are_identical
    (A : Matrix I I ℝ) (d c : I → ℝ) (v r b : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) (hSymm : Aᵀ=A) :
    b-((augmented A d v)⁻¹*ᵥ(Sum.elim c (fun _ => r))) ⬝ᵥ (Sum.elim c (fun _ => r))=
      b-c ⬝ᵥ (A⁻¹*ᵥc)-(innovationCross A d c r)^2/innovationVariance A d v := by
  rw [actual_sequential_and_joint_gaussian_regression_means_are_identical A d c c v r r hA hs hSymm]
  unfold lastWeight innovationCross
  ring

theorem actual_gaussian_posterior_measures_from_joint_and_sequential_formulas_are_identical
    (A : Matrix I I ℝ) (d c y : I → ℝ) (v r b z : ℝ) (hA : IsUnit A)
    (hs : innovationVariance A d v≠0) (hSymm : Aᵀ=A) :
    gaussianReal
      (((augmented A d v)⁻¹*ᵥ(Sum.elim c (fun _ => r))) ⬝ᵥ (Sum.elim y (fun _ => z)))
      (b-((augmented A d v)⁻¹*ᵥ(Sum.elim c (fun _ => r))) ⬝ᵥ (Sum.elim c (fun _ => r))).toNNReal=
    gaussianReal
      (c ⬝ᵥ (A⁻¹*ᵥy)+lastWeight A d c v r*(z-d ⬝ᵥ (A⁻¹*ᵥy)))
      (b-c ⬝ᵥ (A⁻¹*ᵥc)-(innovationCross A d c r)^2/innovationVariance A d v).toNNReal := by
  rw [actual_sequential_and_joint_gaussian_regression_means_are_identical A d c y v r z hA hs hSymm,
    actual_sequential_and_joint_gaussian_regression_variances_are_identical A d c v r b hA hs hSymm]

end SafeLearning.CompleteModulesGaussianSequentialAlgebra
