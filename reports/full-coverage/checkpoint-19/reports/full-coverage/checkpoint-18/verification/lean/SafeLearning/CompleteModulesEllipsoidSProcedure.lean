import SafeLearning.CompleteModulesEllipsoidOptimum

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidOptimum
namespace SafeLearning.CompleteModulesEllipsoidSProcedure

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

omit [DecidableEq Index] in
theorem actual_quadratic_homogeneity (matrix : Matrix Index Index ℝ)
    (vector : Index → ℝ) (scale : ℝ) :
    quadraticValue matrix (scale • vector)=scale^2*quadraticValue matrix vector := by
  simp [quadraticValue,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,pow_two,mul_assoc]

omit [DecidableEq Index] in
theorem actual_constant_plus_symmetric_quadratic_nonnegative_iff
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (constant : ℝ) :
    (∀ vector : Index → ℝ,0 ≤ constant+quadraticValue matrix vector) ↔
      0 ≤ constant ∧ matrix.PosSemidef := by
  constructor
  · intro h
    have hc : 0 ≤ constant := by simpa [quadraticValue] using h 0
    refine ⟨hc,Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymmetric ?_⟩
    intro vector
    simp only [star_trivial]
    by_contra hbad
    have hnegative : quadraticValue matrix vector < 0 := lt_of_not_ge hbad
    let scale := Real.sqrt ((constant+1)/(-quadraticValue matrix vector))
    have hratio : 0 ≤ (constant+1)/(-quadraticValue matrix vector) :=
      div_nonneg (by linarith) (by linarith)
    have hscale : scale^2=(constant+1)/(-quadraticValue matrix vector) := Real.sq_sqrt hratio
    have hmul : ((constant+1)/(-quadraticValue matrix vector))*quadraticValue matrix vector= -(constant+1) := by
      field_simp [hnegative.ne]
    have htest := h (scale • vector)
    rw [actual_quadratic_homogeneity,hscale,hmul] at htest
    linarith
  · rintro ⟨hc,hpsd⟩ vector
    have hq := hpsd.dotProduct_mulVec_nonneg vector
    simp only [star_trivial] at hq
    exact add_nonneg hc hq

def actualSProcedureResidual (storage matrix : Matrix Index Index ℝ)
    (bound multiplier : ℝ) (vector : Index → ℝ) : ℝ :=
  bound-quadraticValue matrix vector-multiplier*(1-quadraticValue storage vector)

omit [DecidableEq Index] in
theorem actual_s_procedure_residual_is_the_literal_constant_plus_quadratic
    (storage matrix : Matrix Index Index ℝ) (bound multiplier : ℝ) (vector : Index → ℝ) :
    actualSProcedureResidual storage matrix bound multiplier vector=
      (bound-multiplier)+quadraticValue (multiplier • storage-matrix) vector := by
  simp [actualSProcedureResidual,quadraticValue,Matrix.sub_mulVec,Matrix.smul_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul]
  ring

omit [DecidableEq Index] in
theorem actual_s_procedure_residual_is_globally_nonnegative_iff_literal_matrix_conditions
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.IsHermitian)
    (hmatrix : matrix.IsHermitian) (bound multiplier : ℝ) :
    (∀ vector : Index → ℝ,0 ≤ actualSProcedureResidual storage matrix bound multiplier vector) ↔
      multiplier ≤ bound ∧ (multiplier • storage-matrix).PosSemidef := by
  simp_rw [actual_s_procedure_residual_is_the_literal_constant_plus_quadratic]
  rw [actual_constant_plus_symmetric_quadratic_nonnegative_iff _
    ((hstorage.smul (show IsSelfAdjoint multiplier by rfl)).sub hmatrix),sub_nonneg]

omit [DecidableEq Index] in
theorem actual_ellipsoid_constraint_has_a_strictly_feasible_point
    (storage : Matrix Index Index ℝ) :
    0 < 1-quadraticValue storage (0 : Index → ℝ) := by
  simp [quadraticValue]

theorem actual_ellipsoid_inhomogeneous_s_lemma_equivalence [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) (bound : ℝ) :
    (∀ vector : Index → ℝ,quadraticValue storage vector ≤ 1 → quadraticValue matrix vector ≤ bound) ↔
      ∃ multiplier : ℝ,0 ≤ multiplier ∧
        ∀ vector : Index → ℝ,0 ≤ actualSProcedureResidual storage matrix bound multiplier vector := by
  constructor
  · intro hbound
    let optimum := max 0 (actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
      (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix))
    have hm := actual_ellipsoid_quadratic_maximum storage matrix hstorage hmatrix
    obtain ⟨vector,henergy,hvalue⟩ := hm.1
    have hb : optimum ≤ bound := by
      have hh := hbound vector henergy
      change optimum=quadraticValue matrix vector at hvalue
      rwa [←hvalue] at hh
    have hd := actual_smallest_nonnegative_s_procedure_multiplier storage matrix hstorage hmatrix
    refine ⟨optimum,hd.1.1,?_⟩
    exact (actual_s_procedure_residual_is_globally_nonnegative_iff_literal_matrix_conditions
      storage matrix hstorage.isHermitian hmatrix bound optimum).2 ⟨hb,hd.1.2⟩
  · rintro ⟨multiplier,hmultiplier,hall⟩ vector henergy
    have hr := hall vector
    have hm : 0 ≤ multiplier*(1-quadraticValue storage vector) :=
      mul_nonneg hmultiplier (sub_nonneg.mpr henergy)
    unfold actualSProcedureResidual at hr
    linarith

end SafeLearning.CompleteModulesEllipsoidSProcedure
