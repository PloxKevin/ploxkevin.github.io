import SafeLearning.CompleteModulesEllipsoidSProcedure

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidOptimum
open SafeLearning.CompleteModulesEllipsoidSProcedure
namespace SafeLearning.CompleteModulesEllipsoidLagrange

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]

def actualLagrangian (storage matrix : Matrix Index Index ℝ) (multiplier : ℝ)
    (vector : Index → ℝ) : ℝ :=
  quadraticValue matrix vector+multiplier*(1-quadraticValue storage vector)

theorem actual_attained_ellipsoid_optimum_obeys_generic_kkt
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    ∃ multiplier : ℝ,∃ vector : Index → ℝ,
      0 ≤ multiplier ∧ quadraticValue storage vector ≤ 1 ∧
      quadraticValue matrix vector=multiplier ∧
      (multiplier • storage-matrix).PosSemidef ∧
      (multiplier • storage-matrix)*ᵥ vector=0 ∧
      multiplier*(quadraticValue storage vector-1)=0 ∧
      IsGreatest (Set.range (actualLagrangian storage matrix multiplier)) multiplier := by
  obtain ⟨optimum,hprimal,hdual⟩ :=
    actual_ellipsoid_primal_and_multiplier_dual_have_the_same_attained_optimum storage matrix hstorage hmatrix
  obtain ⟨vector,henergy,hvalue⟩ := hprimal.1
  have hnonneg : 0 ≤ optimum := hdual.1.1
  have hpsd : (optimum • storage-matrix).PosSemidef := hdual.1.2
  have hquad := hpsd.dotProduct_mulVec_nonneg vector
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul] at hquad
  change 0 ≤ optimum*quadraticValue storage vector-quadraticValue matrix vector at hquad
  have hupper := mul_le_mul_of_nonneg_left henergy hnonneg
  change optimum=quadraticValue matrix vector at hvalue
  have hzero : vector ⬝ᵥ ((optimum • storage-matrix)*ᵥ vector)=0 := by
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul]
    change optimum*quadraticValue storage vector-quadraticValue matrix vector=0
    nlinarith
  have hkkt : (optimum • storage-matrix)*ᵥ vector=0 := by
    apply hpsd.dotProduct_mulVec_zero_iff.mp
    simpa only [star_trivial] using hzero
  have hcomp : optimum*(quadraticValue storage vector-1)=0 := by
    nlinarith
  refine ⟨optimum,vector,hnonneg,henergy,hvalue.symm,hpsd,hkkt,hcomp,?_,?_⟩
  · refine ⟨vector,?_⟩
    unfold actualLagrangian
    rw [←hvalue]
    nlinarith
  · rintro value ⟨point,rfl⟩
    have hp := hpsd.dotProduct_mulVec_nonneg point
    simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul] at hp
    change 0 ≤ optimum*quadraticValue storage point-quadraticValue matrix point at hp
    unfold actualLagrangian
    nlinarith

end SafeLearning.CompleteModulesEllipsoidLagrange
