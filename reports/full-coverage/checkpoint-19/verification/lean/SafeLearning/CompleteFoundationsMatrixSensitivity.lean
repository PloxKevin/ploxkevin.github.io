import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsMatrixSensitivity

section General
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem actual_generic_inverse_differential (X : Matrix N N ℝ) (hX : IsUnit X) :
    HasFDerivAt (fun Y : Matrix N N ℝ => Y⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix N N ℝ) X⁻¹ X⁻¹) X := by
  obtain ⟨u,hu⟩ := hX
  subst X
  simpa only [Matrix.nonsing_inv_eq_ringInverse,Matrix.coe_units_inv] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

theorem actual_generic_inverse_direction (X E : Matrix N N ℝ) (hX : IsUnit X) :
    HasDerivAt (fun t : ℝ => (X+t • E)⁻¹) (-(X⁻¹*E*X⁻¹)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => X+t • E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add X
  have hg : HasFDerivAt (fun Y : Matrix N N ℝ => Y⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix N N ℝ) X⁻¹ X⁻¹) (X+(0 : ℝ) • E) := by
    simpa using actual_generic_inverse_differential X hX
  have h := hg.comp_hasDerivAt 0 hp
  convert! h using 1

theorem actual_generic_identity_determinant_direction (E : Matrix N N ℝ) :
    HasDerivAt (fun t : ℝ => (1+t • E).det) E.trace 0 := by
  let p : Polynomial ℝ := (1+(Polynomial.X : Polynomial ℝ) • E.map Polynomial.C).det
  have h := p.hasDerivAt (0 : ℝ)
  have he : (fun t : ℝ => p.eval t)=(fun t : ℝ => (1+t • E).det) := by
    funext t
    dsimp [p]
    rw [Polynomial.eval,← Polynomial.coe_eval₂RingHom,RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i=j <;>
      simp [Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,hij] <;> ring
  rw [he] at h
  simpa [p,Matrix.derivative_det_one_add_X_smul] using h

theorem actual_generic_determinant_direction (X E : Matrix N N ℝ) (hX : IsUnit X) :
    HasDerivAt (fun t : ℝ => (X+t • E).det) (X.det*(X⁻¹*E).trace) 0 := by
  have he : (fun t : ℝ => (X+t • E).det)=
      (fun t : ℝ => X.det*(1+t • (X⁻¹*E)).det) := by
    funext t
    have hx : X*X⁻¹=1 := Matrix.mul_nonsing_inv _ (X.isUnit_iff_isUnit_det.mp hX)
    have hm : X*(1+t • (X⁻¹*E))=X+t • E := by
      rw [Matrix.mul_add,Matrix.mul_one,Matrix.mul_smul,← Matrix.mul_assoc,hx,Matrix.one_mul]
    rw [← hm,Matrix.det_mul]
  rw [he]
  exact (actual_generic_identity_determinant_direction (X⁻¹*E)).const_mul X.det

theorem actual_generic_log_determinant_direction (X E : Matrix N N ℝ) (hX : IsUnit X) :
    HasDerivAt (fun t : ℝ => Real.log (X+t • E).det) (X⁻¹*E).trace 0 := by
  have hn : X.det≠0 := (X.isUnit_iff_isUnit_det.mp hX).ne_zero
  have h := (actual_generic_determinant_direction X E hX).log (by simpa using hn)
  simp only [zero_smul,add_zero] at h
  convert h using 1
  field_simp [hn]

end General

def sourceX : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,3]
def sourceE : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,0]
def sourcePath (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := sourceX+t • sourceE

theorem actual_source_path (t : ℝ) : sourcePath t=!![2+t,t;t,3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourcePath,sourceX,sourceE]

theorem actual_source_determinant (t : ℝ) : (sourcePath t).det=6+3*t-t^2 := by
  rw [actual_source_path,Matrix.det_fin_two]
  simp
  ring

theorem actual_source_inverse : sourceX⁻¹=Matrix.diagonal ![(1/2 : ℝ),1/3] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceX,Matrix.diagonal_mul,Matrix.diagonal_apply]

theorem actual_source_invertible : IsUnit sourceX := by
  apply sourceX.isUnit_iff_isUnit_det.mpr
  norm_num [sourceX,Matrix.det_diagonal,Fin.prod_univ_two]

theorem actual_source_log_trace : sourceX⁻¹*sourceE=!![(1/2 : ℝ),1/2;1/3,0] ∧
    (sourceX⁻¹*sourceE).trace=1/2 := by
  rw [actual_source_inverse]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceE,Matrix.diagonal_mul]
  · norm_num [sourceE,Matrix.diagonal_mul,Matrix.trace,Fin.sum_univ_two]

theorem actual_source_log_derivative :
    HasDerivAt (fun t : ℝ => Real.log (sourcePath t).det) (1/2) 0 := by
  simpa [sourcePath,actual_source_log_trace.2] using
    actual_generic_log_determinant_direction sourceX sourceE actual_source_invertible

theorem actual_source_log_expansion_derivative :
    HasDerivAt (fun t : ℝ => Real.log (6+3*t-t^2)) (1/2) 0 := by
  have h := actual_source_log_derivative
  simpa only [actual_source_determinant] using h

theorem actual_source_inverse_formula :
    -(sourceX⁻¹*sourceE*sourceX⁻¹)= -!![(1/4 : ℝ),1/6;1/6,0] := by
  rw [actual_source_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceE,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem actual_source_inverse_derivative :
    HasDerivAt (fun t : ℝ => (sourcePath t)⁻¹) (-!![(1/4 : ℝ),1/6;1/6,0]) 0 := by
  rw [← actual_source_inverse_formula]
  exact actual_generic_inverse_direction sourceX sourceE actual_source_invertible

theorem actual_source_positive_definite (t : ℝ) (ht : t ∈ Ioo (-1/2 : ℝ) (1/2)) :
    (sourcePath t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [actual_source_path]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro x hx
    have hp : 0< (3/2+t)*(x 0)^2+(5/2 : ℝ)*(x 1)^2 := by
      have ht0 : 0 < 3/2+t := by linarith [ht.1]
      by_cases h0 : x 0=0
      · have h1 : x 1≠0 := by
          intro h1
          apply hx
          ext i
          fin_cases i <;> simp_all
        exact add_pos_of_nonneg_of_pos (mul_nonneg ht0.le (sq_nonneg _))
          (mul_pos (by norm_num) (sq_pos_of_ne_zero h1))
      · exact add_pos_of_pos_of_nonneg (mul_pos ht0 (sq_pos_of_ne_zero h0))
          (mul_nonneg (by norm_num) (sq_nonneg _))
    have hplus : 0 ≤ ((1/2+t)/2)*(x 0+x 1)^2 :=
      mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
    have hminus : 0 ≤ ((1/2-t)/2)*(x 0-x 1)^2 :=
      mul_nonneg (by linarith [ht.2]) (sq_nonneg _)
    rw [actual_source_path]
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    nlinarith

theorem actual_source_positive_neighbourhood :
    ∀ᶠ t : ℝ in 𝓝 0, (sourcePath t).PosDef ∧ 0<(sourcePath t).det := by
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ)<0) (by norm_num : (0 : ℝ)<1/2)] with t ht
  have hp := actual_source_positive_definite t ht
  exact ⟨hp,hp.det_pos⟩

theorem actual_source_inverse_is_not_entrywise_reciprocal :
    (sourceX⁻¹) 0 1=0 ∧
      deriv (fun t : ℝ => ((sourcePath t)⁻¹) 0 1) 0= -(1/6) := by
  constructor
  · rw [actual_source_inverse]
    norm_num [Matrix.diagonal_apply]
  · have h := actual_source_inverse_derivative
    have hr := (hasDerivAt_pi.mp h) 0
    have hc := (hasDerivAt_pi.mp hr) 1
    norm_num at hc
    exact hc.deriv

end SafeLearning.CompleteFoundationsMatrixSensitivity
