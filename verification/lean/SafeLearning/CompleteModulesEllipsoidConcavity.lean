import SafeLearning.CompleteModulesEllipsoidSProcedure

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidSProcedure
namespace SafeLearning.CompleteModulesEllipsoidConcavity

variable {Index : Type*} [Fintype Index]

def actualEllipsoid (storage : Matrix Index Index ℝ) : Set (Index → ℝ) :=
  {vector | quadraticValue storage vector ≤ 1}

theorem actual_quadratic_jensen_gap_identity (matrix : Matrix Index Index ℝ)
    (first second : Index → ℝ) (left right : ℝ) (hsum : left+right=1) :
    quadraticValue matrix (left • first+right • second)-
      (left*quadraticValue matrix first+right*quadraticValue matrix second)=
      -(left*right)*quadraticValue matrix (first-second) := by
  unfold quadraticValue
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,Matrix.mulVec_smul,
    dotProduct_add,add_dotProduct,dotProduct_sub,sub_dotProduct,dotProduct_smul,
    smul_dotProduct,smul_eq_mul]
  have hr : right=1-left := by linarith
  rw [hr]
  ring

theorem actual_psd_quadratic_is_nonnegative (matrix : Matrix Index Index ℝ)
    (hpsd : matrix.PosSemidef) (vector : Index → ℝ) : 0 ≤ quadraticValue matrix vector := by
  simpa only [quadraticValue,star_trivial] using hpsd.dotProduct_mulVec_nonneg vector

theorem actual_positive_semidefinite_storage_ellipsoid_is_convex
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosSemidef) :
    Convex ℝ (actualEllipsoid storage) := by
  intro first hfirst second hsecond left right hl hr hsum
  have he := actual_quadratic_jensen_gap_identity storage first second left right hsum
  have hq := actual_psd_quadratic_is_nonnegative storage hstorage (first-second)
  have hm := mul_nonneg (mul_nonneg hl hr) hq
  change quadraticValue storage first ≤ 1 at hfirst
  change quadraticValue storage second ≤ 1 at hsecond
  change quadraticValue storage (left • first+right • second) ≤ 1
  have hleft := mul_le_mul_of_nonneg_left hfirst hl
  have hright := mul_le_mul_of_nonneg_left hsecond hr
  nlinarith

theorem actual_quadratic_is_concave_on_a_positive_storage_ellipsoid_iff_negative_semidefinite
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosSemidef)
    (hmatrix : matrix.IsHermitian) :
    ConcaveOn ℝ (actualEllipsoid storage) (quadraticValue matrix) ↔ (-matrix).PosSemidef := by
  constructor
  · intro hconcave
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hmatrix.neg
    intro vector
    have hp := actual_psd_quadratic_is_nonnegative storage hstorage vector
    let scale := Real.sqrt (1/(quadraticValue storage vector+1))
    have hden : 0 < quadraticValue storage vector+1 := by linarith
    have hratio : 0 < 1/(quadraticValue storage vector+1) := one_div_pos.mpr hden
    have hs : scale^2=1/(quadraticValue storage vector+1) := Real.sq_sqrt hratio.le
    have hspos : 0 < scale^2 := by rw [hs];exact hratio
    have he : scale^2*(quadraticValue storage vector+1)=1 := by
      rw [hs]
      field_simp
    have henergy : scale^2*quadraticValue storage vector ≤ 1 := by nlinarith [sq_nonneg scale]
    have hf : scale • vector ∈ actualEllipsoid storage := by
      change quadraticValue storage (scale • vector) ≤ 1
      rwa [actual_quadratic_homogeneity]
    have hg : (-scale) • vector ∈ actualEllipsoid storage := by
      change quadraticValue storage ((-scale) • vector) ≤ 1
      rwa [actual_quadratic_homogeneity,neg_sq]
    have hh := hconcave.2 hf hg
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    have hmid : (1/2:ℝ) • (scale • vector)+(1/2:ℝ) • ((-scale) • vector)=0 := by
      ext index
      simp
    rw [hmid,actual_quadratic_homogeneity,actual_quadratic_homogeneity,neg_sq] at hh
    simp only [quadraticValue,Matrix.mulVec_zero,dotProduct_zero] at hh
    have hnegative : quadraticValue matrix vector ≤ 0 := by
      change (1/2)*(scale^2*quadraticValue matrix vector)+(1/2)*(scale^2*quadraticValue matrix vector) ≤ 0 at hh
      nlinarith
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
    change 0 ≤ -quadraticValue matrix vector
    linarith
  · intro hnegative
    refine ⟨actual_positive_semidefinite_storage_ellipsoid_is_convex storage hstorage,?_⟩
    intro first _ second _ left right hl hr hsum
    have he := actual_quadratic_jensen_gap_identity matrix first second left right hsum
    have hq := actual_psd_quadratic_is_nonnegative (-matrix) hnegative (first-second)
    simp only [quadraticValue,Matrix.neg_mulVec,dotProduct_neg] at hq
    change 0 ≤ -quadraticValue matrix (first-second) at hq
    have hm := mul_nonneg (mul_nonneg hl hr) hq
    change left*quadraticValue matrix first+right*quadraticValue matrix second ≤
      quadraticValue matrix (left • first+right • second)
    nlinarith

end SafeLearning.CompleteModulesEllipsoidConcavity
