import Mathlib

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyQuadraticDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lagrangian (H : Matrix ι ι ℝ) (g b : ι → ℝ) (c δ lam ν : ℝ) (x : ι → ℝ) : ℝ :=
  g ⬝ᵥ x - ν * (c + b ⬝ᵥ x) - lam * ((x ⬝ᵥ (H *ᵥ x)) / 2 - δ)

def optimizer (H : Matrix ι ι ℝ) (g b : ι → ℝ) (lam ν : ℝ) : ι → ℝ :=
  (1 / lam) • (H⁻¹ *ᵥ (g - ν • b))

def closedDual (H : Matrix ι ι ℝ) (g b : ι → ℝ) (c δ lam ν : ℝ) : ℝ :=
  ((g - ν • b) ⬝ᵥ (H⁻¹ *ᵥ (g - ν • b))) / (2 * lam) - ν * c + lam * δ

def actualDual (H : Matrix ι ι ℝ) (g b : ι → ℝ) (c δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  sSup (range (lagrangian H g b c δ p.1 p.2))

theorem actual_inverse_solves (H : Matrix ι ι ℝ) (hH : H.PosDef) (u : ι → ℝ) :
    H *ᵥ (H⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv H ((isUnit_iff_isUnit_det H).mp hH.isUnit), one_mulVec]

theorem actual_real_symmetric_form (H : Matrix ι ι ℝ) (hH : H.PosDef) (x y : ι → ℝ) :
    x ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ x) := by
  simpa using hH.isHermitian.star_dotProduct_mulVec_comm x y

theorem actual_optimizer_stationarity (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (lam ν : ℝ) (hlam : 0 < lam) :
    lam • (H *ᵥ optimizer H g b lam ν) = g - ν • b := by
  simp [optimizer, mulVec_smul, actual_inverse_solves H hH, smul_smul, ne_of_gt hlam]

theorem actual_lagrangian_completed_square (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam ν : ℝ) (hlam : 0 < lam) (x : ι → ℝ) :
    lagrangian H g b c δ lam ν (optimizer H g b lam ν) - lagrangian H g b c δ lam ν x =
      (lam / 2) * ((x - optimizer H g b lam ν) ⬝ᵥ
        (H *ᵥ (x - optimizer H g b lam ν))) := by
  let z := optimizer H g b lam ν
  have hs := actual_optimizer_stationarity H hH g b lam ν hlam
  have hx : g ⬝ᵥ x - ν * (b ⬝ᵥ x) = lam * (x ⬝ᵥ (H *ᵥ z)) := by
    have := congrArg (fun u : ι → ℝ => u ⬝ᵥ x) hs
    have he : g ⬝ᵥ x - ν * (b ⬝ᵥ x) = lam * ((H *ᵥ z) ⬝ᵥ x) := by
      simpa [z, sub_dotProduct, smul_dotProduct] using this.symm
    exact he.trans (by rw [dotProduct_comm (H *ᵥ z) x])
  have hz : g ⬝ᵥ z - ν * (b ⬝ᵥ z) = lam * (z ⬝ᵥ (H *ᵥ z)) := by
    have := congrArg (fun u : ι → ℝ => u ⬝ᵥ z) hs
    have he : g ⬝ᵥ z - ν * (b ⬝ᵥ z) = lam * ((H *ᵥ z) ⬝ᵥ z) := by
      simpa [z, sub_dotProduct, smul_dotProduct] using this.symm
    exact he.trans (by rw [dotProduct_comm (H *ᵥ z) z])
  change lagrangian H g b c δ lam ν z - lagrangian H g b c δ lam ν x = _
  simp only [lagrangian, mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [actual_real_symmetric_form H hH z x]
  nlinarith

theorem actual_global_lagrangian_maximum (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam ν : ℝ) (hlam : 0 < lam) (x : ι → ℝ) :
    lagrangian H g b c δ lam ν x ≤ lagrangian H g b c δ lam ν (optimizer H g b lam ν) := by
  have hq : 0 ≤ (x - optimizer H g b lam ν) ⬝ᵥ
      (H *ᵥ (x - optimizer H g b lam ν)) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg (x - optimizer H g b lam ν)
  have := actual_lagrangian_completed_square H hH g b c δ lam ν hlam x
  have := mul_nonneg (le_of_lt (div_pos hlam (by norm_num : (0 : ℝ) < 2))) hq
  linarith

theorem actual_attained_closed_dual_value (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam ν : ℝ) (hlam : 0 < lam) :
    lagrangian H g b c δ lam ν (optimizer H g b lam ν) = closedDual H g b c δ lam ν := by
  simp only [lagrangian, optimizer, closedDual, mulVec_smul, actual_inverse_solves H hH,
    smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul]
  rw [dotProduct_comm (H⁻¹ *ᵥ (g - ν • b)) g,
    dotProduct_comm (H⁻¹ *ᵥ (g - ν • b)) b]
  field_simp [ne_of_gt hlam]
  <;> ring

theorem actual_true_supremum_equals_closed_dual (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam ν : ℝ) (hlam : 0 < lam) :
    actualDual H g b c δ (lam, ν) = closedDual H g b c δ lam ν := by
  unfold actualDual
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro y ⟨x,rfl⟩
    exact (actual_global_lagrangian_maximum H hH g b c δ lam ν hlam x).trans_eq
      (actual_attained_closed_dual_value H hH g b c δ lam ν hlam)
  · rw [← actual_attained_closed_dual_value H hH g b c δ lam ν hlam]
    apply le_csSup
    · refine ⟨lagrangian H g b c δ lam ν (optimizer H g b lam ν), ?_⟩
      rintro y ⟨x,rfl⟩
      exact actual_global_lagrangian_maximum H hH g b c δ lam ν hlam x
    · exact mem_range_self _

theorem actual_weak_duality (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam ν : ℝ) (hlam : 0 < lam) (hν : 0 ≤ ν)
    (x : ι → ℝ) (hcost : c + b ⬝ᵥ x ≤ 0) (htrust : (x ⬝ᵥ (H *ᵥ x)) / 2 ≤ δ) :
    g ⬝ᵥ x ≤ actualDual H g b c δ (lam,ν) := by
  have hn := mul_nonpos_of_nonneg_of_nonpos hν hcost
  have ht := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam) (sub_nonpos.mpr htrust)
  have hg := actual_global_lagrangian_maximum H hH g b c δ lam ν hlam x
  rw [actual_true_supremum_equals_closed_dual H hH g b c δ lam ν hlam,
    ← actual_attained_closed_dual_value H hH g b c δ lam ν hlam]
  unfold lagrangian at hg ⊢
  linarith

end SafeLearning.CompletePolicyQuadraticDual
