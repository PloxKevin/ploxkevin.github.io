import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsGeometry

section InnerProducts
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cauchy_schwarz_general (x y : E) : |⟪x,y⟫| ≤ ‖x‖*‖y‖ := abs_real_inner_le_norm x y

theorem cauchy_schwarz_equality (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    |⟪x,y⟫|=‖x‖*‖y‖ ↔ ∃ r : ℝ, r ≠ 0 ∧ y=r • x := by
  simpa [Real.norm_eq_abs] using (norm_inner_eq_norm_iff (𝕜 := ℝ) hx hy)

theorem cauchy_schwarz_equality_including_zero (x y : E) :
    |⟪x,y⟫|=‖x‖*‖y‖ ↔ x=0 ∨ ∃ r : ℝ, y=r • x := by
  simpa [Real.norm_eq_abs] using ((norm_inner_eq_norm_tfae ℝ x y).out 1 3)

theorem inner_product_quadratic_expansion (x y : E) (t : ℝ) :
    ‖x-t • y‖^2=‖x‖^2-2*t*⟪x,y⟫+t^2*‖y‖^2 := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs]
  rw [mul_pow,sq_abs]
  ring

theorem linear_ball_upper_bound (c center u : E) (r : ℝ)
    (hu : ‖u-center‖ ≤ r) : ⟪c,u⟫ ≤ ⟪c,center⟫+r*‖c‖ := by
  have hc := (le_abs_self ⟪c,u-center⟫).trans (abs_real_inner_le_norm c (u-center))
  rw [inner_sub_right] at hc
  have hm := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
  linarith

theorem linear_ball_attainment (c center : E) (r : ℝ) (hr : 0 ≤ r) :
    ∃ u : E, ‖u-center‖ ≤ r ∧ ⟪c,u⟫=⟪c,center⟫+r*‖c‖ := by
  by_cases hc : c=0
  · refine ⟨center,by simpa using hr,?_⟩
    simp [hc]
  · have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    refine ⟨center+(r/‖c‖) • c,?_,?_⟩
    · simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr hnorm.le)]
      rw [div_mul_cancel₀ _ (ne_of_gt hnorm)]
    · rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
      field_simp <;> ring

theorem scalar_young_absolute (a b ε : ℝ) (hε : 0 < ε) :
    2*|a*b| ≤ ε*a^2+b^2/ε := by
  simpa [abs_mul,mul_assoc] using SafeLearning.PrimersFoundations.young_scaled |a| |b| ε hε

theorem am_gm_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a*b) ≤ (a+b)/2 ∧
    (Real.sqrt (a*b)=(a+b)/2 ↔ a=b) := by
  have hs := Real.sq_sqrt (mul_nonneg ha hb)
  have hp := Real.sqrt_nonneg (a*b)
  constructor
  · nlinarith [sq_nonneg (a-b)]
  · constructor
    · intro h; nlinarith [sq_nonneg (a-b)]
    · intro h; subst b; rw [← pow_two,Real.sqrt_sq ha]; ring

theorem reciprocal_am_gm (u c : ℝ) (hu : 0<u) (hc : 0<c) :
    2*Real.sqrt c ≤ u+c/u ∧ (u+c/u=2*Real.sqrt c ↔ u=Real.sqrt c) := by
  have hs := Real.sq_sqrt hc.le
  have hp := Real.sqrt_nonneg c
  have hmul : c/u*u=c := div_mul_cancel₀ _ (ne_of_gt hu)
  have hbound : 2*Real.sqrt c ≤ u+c/u := by
    apply (mul_le_mul_iff_of_pos_right hu).mp
    nlinarith [sq_nonneg (u-Real.sqrt c)]
  refine ⟨hbound,?_⟩
  constructor
  · intro h
    have hh := congrArg (fun t : ℝ => t*u) h
    nlinarith [sq_nonneg (u-Real.sqrt c)]
  · intro h; rw [h]; field_simp; nlinarith
end InnerProducts

section NormsAndOperators
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem reverse_triangle_general (x y : E) : |‖x‖-‖y‖| ≤ ‖x-y‖ := abs_norm_sub_norm_le x y
theorem norm_vanishes_iff (x : E) : ‖x‖=0 ↔ x=0 := norm_eq_zero
theorem norm_scale (a : ℝ) (x : E) : ‖a • x‖=|a| * ‖x‖ := by simp [norm_smul]
theorem norm_triangle (x y : E) : ‖x+y‖ ≤ ‖x‖+‖y‖ := norm_add_le x y

theorem operator_norm_bound (A : E →L[ℝ] F) (x : E) :
    ‖A x‖ ≤ ‖A‖*‖x‖ := A.le_opNorm x

theorem operator_norm_is_least (A : E →L[ℝ] F) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x, ‖A x‖ ≤ M*‖x‖) : ‖A‖ ≤ M := A.opNorm_le_bound hM h

theorem operator_product_bound (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    ‖A.comp B‖ ≤ ‖A‖*‖B‖ := A.opNorm_comp_le B

theorem linear_map_lipschitz (A : E →L[ℝ] F) (x y : E) :
    ‖A x-A y‖ ≤ ‖A‖*‖x-y‖ := by rw [← A.map_sub]; exact A.le_opNorm (x-y)
end NormsAndOperators

theorem positive_lipschitz_certified_ball {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (L : NNReal) (hg : LipschitzWith L g) (hL : 0 < (L : ℝ))
    (z : X) (c : ℝ) (hc : 0 < c) (hgz : g z=c) :
    ∀ x ∈ Metric.closedBall z (c/L), 0 ≤ g x := by
  intro x hx
  have hd := hg.dist_le_mul x z
  rw [Real.dist_eq,hgz] at hd
  have hm := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hx) L.coe_nonneg
  have hne : (L : ℝ) ≠ 0 := ne_of_gt hL
  have he : (L : ℝ)*(c/L)=c := by field_simp
  rw [he] at hm
  have hlo := (abs_le.mp hd).1
  linarith

section SpectralTheorem
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem symmetric_orthonormal_eigenbasis (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : n) :
    A.mulVec (hA.eigenvectorBasis j)=hA.eigenvalues j • (hA.eigenvectorBasis j : n → ℝ) :=
  hA.mulVec_eigenvectorBasis j

theorem symmetric_spectral_decomposition (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A=((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hA.eigenvectorUnitary)
      (Matrix.diagonal hA.eigenvalues) := by simpa using hA.spectral_theorem

theorem symmetric_psd_eigenvalues (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ i, 0 ≤ hA.eigenvalues i := hA.posSemidef_iff_eigenvalues_nonneg

theorem symmetric_pd_eigenvalues (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := hA.posDef_iff_eigenvalues_pos

theorem determinant_eigenvalue_product (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.det=∏ i, hA.eigenvalues i := by simpa using hA.det_eq_prod_eigenvalues

theorem trace_eigenvalue_sum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.trace=∑ i, hA.eigenvalues i := by simpa using hA.trace_eq_sum_eigenvalues

theorem positive_definite_inverse (A : Matrix n n ℝ) (hA : A.PosDef) : A⁻¹.PosDef := hA.inv

theorem positive_definite_determinant (A : Matrix n n ℝ) (hA : A.PosDef) : 0 < A.det := hA.det_pos
end SpectralTheorem

theorem neumann_series_general {R : Type*} [NormedRing R] [CompleteSpace R] [NormOneClass R]
    (A : R) (hA : ‖A‖<1) :
    IsUnit (1-A) ∧ HasSum (fun n : ℕ => A^n) (Ring.inverse (1-A)) ∧
    ‖Ring.inverse (1-A)‖ ≤ 1/(1-‖A‖) := by
  refine ⟨isUnit_one_sub_of_norm_lt_one hA,hasSum_geom_series_inverse A hA,?_⟩
  rw [← geom_series_eq_inverse A hA]
  simpa [norm_one,one_div] using tsum_geometric_le_of_norm_lt_one A hA

section FrobeniusNorm
open scoped Matrix.Norms.Frobenius

theorem frobenius_submultiplicativity {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) : ‖A*B‖ ≤ ‖A‖*‖B‖ :=
  Matrix.frobenius_norm_mul A B

theorem frobenius_norm_formula {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A‖=Real.sqrt (∑ i, ∑ j, A i j^2) := by
  simpa [Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow,one_div] using Matrix.frobenius_norm_def A
end FrobeniusNorm

theorem lipschitz_composition_general {X Y Z : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (f : X → Y) (g : Y → Z) (Lf Lg : NNReal)
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    LipschitzWith (Lg*Lf) (g ∘ f) := hg.comp hf

end SafeLearning.CompleteFoundationsGeometry
