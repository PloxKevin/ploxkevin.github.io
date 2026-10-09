import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsFeatures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def featureGram (φ : ι → E) : Matrix ι ι ℝ := fun i j => ⟪φ i,φ j⟫
def featureSum (φ : ι → E) (a : ι → ℝ) : E := ∑ i, a i • φ i

theorem feature_evaluation (φ : ι → E) (a : ι → ℝ) (x : E) :
    ⟪x,featureSum φ a⟫=∑ i, a i*⟪x,φ i⟫ := by
  simp [featureSum,inner_sum,real_inner_smul_right]

theorem gram_coefficient_evaluation (φ : ι → E) (a : ι → ℝ) (i : ι) :
    ⟪φ i,featureSum φ a⟫=(featureGram φ).mulVec a i := by
  simp [feature_evaluation,featureGram,Matrix.mulVec,dotProduct,mul_comm]

theorem feature_norm_quadratic (φ : ι → E) (a : ι → ℝ) :
    ‖featureSum φ a‖^2=a ⬝ᵥ ((featureGram φ).mulVec a) := by
  calc
    _ = ⟪featureSum φ a,featureSum φ a⟫ := (real_inner_self_eq_norm_sq _).symm
    _ = _ := by
      simp only [featureSum,featureGram,sum_inner,inner_sum,real_inner_smul_left,
        real_inner_smul_right,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (φ j) (φ i)]
      ring

theorem feature_gram_psd (φ : ι → E) : (featureGram φ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change (featureGram φ).conjTranspose=featureGram φ
    ext i j; simp [featureGram,Matrix.conjTranspose_apply,real_inner_comm]
  · intro a
    simpa only [star_trivial,← feature_norm_quadratic] using sq_nonneg ‖featureSum φ a‖

theorem feature_null_quadratic_iff (φ : ι → E) (a : ι → ℝ) :
    a ⬝ᵥ ((featureGram φ).mulVec a)=0 ↔ featureSum φ a=0 := by
  rw [← feature_norm_quadratic,sq_eq_zero_iff,norm_eq_zero]

theorem reproducing_evaluation_bound {X : Type*} (φ : X → E) (x : X) (w : E) :
    |⟪φ x,w⟫| ≤ Real.sqrt ⟪φ x,φ x⟫*‖w‖ := by
  rw [real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem interpolant_orthogonal_residual (φ : ι → E) (a : ι → ℝ) (v : E)
    (hfit : ∀ i, ⟪φ i,v⟫=⟪φ i,featureSum φ a⟫) :
    ⟪featureSum φ a,v-featureSum φ a⟫=0 := by
  simp only [featureSum,sum_inner,real_inner_smul_left,inner_sub_right]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  have hh := hfit i
  dsimp [featureSum] at hh
  rw [hh]

theorem minimum_norm_interpolant (φ : ι → E) (a : ι → ℝ) (v : E)
    (hfit : ∀ i, ⟪φ i,v⟫=⟪φ i,featureSum φ a⟫) :
    ‖v‖^2=‖featureSum φ a‖^2+‖v-featureSum φ a‖^2 ∧
    ‖featureSum φ a‖ ≤ ‖v‖ ∧
    (‖v‖=‖featureSum φ a‖ ↔ v=featureSum φ a) := by
  have ho := interpolant_orthogonal_residual φ a v hfit
  have hi : ⟪featureSum φ a,v⟫=‖featureSum φ a‖^2 := by
    rw [inner_sub_right,real_inner_self_eq_norm_sq] at ho
    linarith
  have hnorm := norm_sub_sq_real v (featureSum φ a)
  have hiv : ⟪v,featureSum φ a⟫=‖featureSum φ a‖^2 :=
    (real_inner_comm v (featureSum φ a)).symm.trans hi
  rw [hiv] at hnorm
  refine ⟨by linarith,?_,?_⟩
  · nlinarith [sq_nonneg ‖v-featureSum φ a‖,norm_nonneg v,norm_nonneg (featureSum φ a)]
  · constructor
    · intro h
      have hzsq : ‖v-featureSum φ a‖^2=0 := by rw [h] at hnorm; nlinarith
      have hz : ‖v-featureSum φ a‖=0 := sq_eq_zero_iff.mp hzsq
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    · intro h; rw [h]

theorem invertible_gram_interpolant [DecidableEq ι] (φ : ι → E) (y : ι → ℝ)
    (hdet : IsUnit (featureGram φ).det) :
    ∀ i, ⟪φ i,featureSum φ ((featureGram φ)⁻¹.mulVec y)⟫=y i := by
  intro i
  rw [gram_coefficient_evaluation,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec]

theorem interpolant_norm_data_identity (φ : ι → E) (a y : ι → ℝ)
    (hfit : (featureGram φ).mulVec a=y) :
    ‖featureSum φ a‖^2=a ⬝ᵥ y := by rw [feature_norm_quadratic,hfit]

end SafeLearning.CompleteFoundationsFeatures
