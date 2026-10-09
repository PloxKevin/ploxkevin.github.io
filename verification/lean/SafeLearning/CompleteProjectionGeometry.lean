import SafeLearning.CompleteProjectionCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteProjectionGeometry

open SafeLearning.CompleteWeightedProjection SafeLearning.CompleteProjectionCharacterization

theorem energy_smul {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (c : ℝ) (x : ι → ℝ) : energy H (c • x) = c ^ 2 * energy H x := by
  simp only [energy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem energy_convex_gap {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (hH : H.IsSymm) (x y : ι → ℝ) (a b : ℝ) (hab : a + b = 1) :
    energy H (a • x + b • y) =
      a * energy H x + b * energy H y - a * b * energy H (x - y) := by
  simp only [energy, mulVec_add, mulVec_sub, mulVec_smul, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [hH.dotProduct_mulVec_comm (x := y) (y := x)]
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

theorem energy_strictly_convex {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) : StrictConvexOn ℝ Set.univ (energy H) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  rw [energy_convex_gap H hH.isHermitian.isSymm x y a b hab]
  simp only [smul_eq_mul]
  have hq := energy_positive H hH (x - y) (sub_ne_zero.mpr hxy)
  have hp : 0 < a * b * energy H (x - y) := mul_pos (mul_pos ha hb) hq
  linarith

theorem objective_strictly_convex {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (nominal : ι → ℝ) :
    StrictConvexOn ℝ Set.univ (objective H nominal) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have ht : a • x + b • y - nominal = a • (x - nominal) + b • (y - nominal) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (nominal i) * hab
  have hn : x - nominal ≠ y - nominal := by simpa using hxy
  have h := (energy_strictly_convex H hH).2 (Set.mem_univ (x - nominal))
    (Set.mem_univ (y - nominal)) hn ha hb hab
  unfold objective
  rw [ht]
  simp only [smul_eq_mul] at h ⊢
  linarith

theorem inverse_direction_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (b : ι → ℝ) :
    energy H (H⁻¹ *ᵥ b) = b ⬝ᵥ (H⁻¹ *ᵥ b) := by
  unfold energy
  rw [inverse_direction H hH b, dotProduct_comm]

theorem metric_linear_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (b v : ι → ℝ) (hb : b ≠ 0) :
    (b ⬝ᵥ v) ^ 2 ≤ (b ⬝ᵥ (H⁻¹ *ᵥ b)) * energy H v := by
  let d := b ⬝ᵥ (H⁻¹ *ᵥ b)
  let z := H⁻¹ *ᵥ b
  have hd : 0 < d := inverse_denominator_positive H hH b hb
  have hz : energy H z = d := inverse_direction_energy H hH b
  have hn := energy_nonneg H hH (v + (-(b ⬝ᵥ v) / d) • z)
  rw [energy_expansion H hH.isHermitian.isSymm, energy_smul, hz] at hn
  have hi : H *ᵥ z = b := inverse_direction H hH b
  rw [mulVec_smul, hi, dotProduct_smul, smul_eq_mul, dotProduct_comm v b] at hn
  have he : energy H v + (-(b ⬝ᵥ v) / d) ^ 2 * d +
      2 * ((-(b ⬝ᵥ v) / d) * (b ⬝ᵥ v)) =
        energy H v - (b ⬝ᵥ v) ^ 2 / d := by
    field_simp
    ring
  rw [he] at hn
  have hc : (b ⬝ᵥ v) ^ 2 ≤ energy H v * d := (div_le_iff₀ hd).mp (by linarith)
  simpa [d, mul_comm] using hc

theorem metric_steepest_ascent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (b : ι → ℝ) (hb : b ≠ 0) :
    let d := b ⬝ᵥ (H⁻¹ *ᵥ b)
    let direction := (1 / Real.sqrt d) • (H⁻¹ *ᵥ b)
    energy H direction = 1 ∧ b ⬝ᵥ direction = Real.sqrt d ∧
      ∀ v : ι → ℝ, energy H v ≤ 1 → b ⬝ᵥ v ≤ b ⬝ᵥ direction := by
  dsimp only
  let d := b ⬝ᵥ (H⁻¹ *ᵥ b)
  have hd : 0 < d := inverse_denominator_positive H hH b hb
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have he : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd.le
  have hv : b ⬝ᵥ ((1 / Real.sqrt d) • (H⁻¹ *ᵥ b)) = Real.sqrt d := by
    rw [dotProduct_smul, smul_eq_mul]
    change (1 / Real.sqrt d) * d = Real.sqrt d
    calc
      (1 / Real.sqrt d) * d = (1 / Real.sqrt d) * (Real.sqrt d) ^ 2 := by rw [he]
      _ = Real.sqrt d := by field_simp [ne_of_gt hs]
  refine ⟨?_, hv, ?_⟩
  · rw [energy_smul, inverse_direction_energy H hH b]
    change (1 / Real.sqrt d) ^ 2 * d = 1
    calc
      (1 / Real.sqrt d) ^ 2 * d = (1 / Real.sqrt d) ^ 2 * (Real.sqrt d) ^ 2 := by rw [he]
      _ = 1 := by field_simp [ne_of_gt hs]
  · intro v hve
    rw [hv]
    have h := metric_linear_bound H hH b v hb
    change (b ⬝ᵥ v) ^ 2 ≤ d * energy H v at h
    have hupper : (b ⬝ᵥ v) ^ 2 ≤ d := h.trans (by nlinarith)
    nlinarith [sq_nonneg (b ⬝ᵥ v + Real.sqrt d)]

theorem identity_weight_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (b nominal : ι → ℝ) :
    solution (1 : Matrix ι ι ℝ) a b nominal =
      nominal + max 0 (-(a + b ⬝ᵥ nominal) / (b ⬝ᵥ b)) • b := by
  simp [solution, multiplier]

end SafeLearning.CompleteProjectionGeometry
