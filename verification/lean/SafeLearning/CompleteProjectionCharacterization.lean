import SafeLearning.CompleteWeightedProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteProjectionCharacterization

open SafeLearning.CompleteWeightedProjection

def objective {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (nominal u : ι → ℝ) : ℝ := (1 / 2) * energy H (u - nominal)

def isOptimizer {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (a : ℝ) (b nominal candidate : ι → ℝ) : Prop :=
  0 ≤ a + b ⬝ᵥ candidate ∧
    ∀ u, 0 ≤ a + b ⬝ᵥ u → objective H nominal candidate ≤ objective H nominal u

theorem actual_half_objective_minimum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) (hb : b ≠ 0) :
    isOptimizer H a b nominal (solution H a b nominal) := by
  have h := weighted_halfspace_unique_minimum H hH a b nominal hb
  refine ⟨h.1, ?_⟩
  intro u hu
  exact mul_le_mul_of_nonneg_left (h.2 u hu).1 (by norm_num)

theorem optimizer_is_explicit_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal candidate : ι → ℝ)
    (hb : b ≠ 0) (hc : isOptimizer H a b nominal candidate) :
    candidate = solution H a b nominal := by
  have h := weighted_halfspace_unique_minimum H hH a b nominal hb
  have hc' := hc.2 (solution H a b nominal) h.1
  unfold objective at hc'
  apply (h.2 candidate hc.1).2
  linarith [(h.2 candidate hc.1).1]

/-- Necessity follows from the explicit unique optimizer; sufficiency follows
from the positive quadratic remainder, without assuming either conclusion. -/
theorem optimizer_iff_kkt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal candidate : ι → ℝ)
    (hb : b ≠ 0) :
    isOptimizer H a b nominal candidate ↔
      0 ≤ a + b ⬝ᵥ candidate ∧ ∃ μ : ℝ, 0 ≤ μ ∧
        H *ᵥ (candidate - nominal) = μ • b ∧ μ * (a + b ⬝ᵥ candidate) = 0 := by
  constructor
  · intro hc
    have he := optimizer_is_explicit_solution H hH a b nominal candidate hb hc
    subst candidate
    exact ⟨(solution_feasible_complementarity H hH a b nominal hb).1,
      multiplier H a b nominal, le_max_left _ _, solution_stationarity H hH a b nominal,
      (solution_feasible_complementarity H hH a b nominal hb).2⟩
  · rintro ⟨hc, μ, hμ, hs, hcomp⟩
    refine ⟨hc, ?_⟩
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (kkt_global_optimal H hH a μ b nominal candidate hμ hs hcomp u hu) (by norm_num)

theorem strict_feasible_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) (hb : b ≠ 0) :
    ∃ u : ι → ℝ, a + b ⬝ᵥ u = 1 := by
  let d := b ⬝ᵥ (H⁻¹ *ᵥ b)
  have hd : 0 < d := inverse_denominator_positive H hH b hb
  refine ⟨nominal + ((1 - (a + b ⬝ᵥ nominal)) / d) • (H⁻¹ *ᵥ b), ?_⟩
  rw [dotProduct_add, dotProduct_smul]
  change a + (b ⬝ᵥ nominal + ((1 - (a + b ⬝ᵥ nominal)) / d) * d) = 1
  rw [div_mul_cancel₀ _ (ne_of_gt hd)]
  ring

def lagrangian {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (a : ℝ) (b nominal u : ι → ℝ) (μ : ℝ) : ℝ :=
  objective H nominal u - μ * (a + b ⬝ᵥ u)

theorem lagrangian_quadratic_remainder {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a μ : ℝ)
    (b nominal center u : ι → ℝ)
    (hs : H *ᵥ (center - nominal) = μ • b) :
    lagrangian H a b nominal u μ =
      lagrangian H a b nominal center μ + (1 / 2) * energy H (u - center) := by
  have he : u - nominal = (u - center) + (center - nominal) := by abel
  unfold lagrangian objective
  rw [he, energy_expansion H hH.isHermitian.isSymm, hs, dotProduct_smul,
      smul_eq_mul, dotProduct_comm (u - center) b, dotProduct_sub]
  ring

def dual {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (a : ℝ) (b nominal : ι → ℝ) (μ : ℝ) : ℝ :=
  sInf (Set.range (fun u : ι → ℝ => lagrangian H a b nominal u μ))

theorem actual_dual_infimum_at_stationary_point {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a μ : ℝ)
    (b nominal center : ι → ℝ)
    (hs : H *ᵥ (center - nominal) = μ • b) :
    dual H a b nominal μ = lagrangian H a b nominal center μ := by
  have hlo : ∀ u, lagrangian H a b nominal center μ ≤ lagrangian H a b nominal u μ := by
    intro u
    rw [lagrangian_quadratic_remainder H hH a μ b nominal center u hs]
    linarith [energy_nonneg H hH (u - center)]
  have hbdd : BddBelow (Set.range (fun u => lagrangian H a b nominal u μ)) :=
    ⟨lagrangian H a b nominal center μ, by rintro v ⟨u, rfl⟩; exact hlo u⟩
  apply le_antisymm
  · exact csInf_le hbdd ⟨center, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro v ⟨u, rfl⟩; exact hlo u)

theorem actual_strong_duality_attained {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) (hb : b ≠ 0) :
    dual H a b nominal (multiplier H a b nominal) =
      objective H nominal (solution H a b nominal) := by
  rw [actual_dual_infimum_at_stationary_point H hH a (multiplier H a b nominal)
    b nominal (solution H a b nominal) (solution_stationarity H hH a b nominal)]
  unfold lagrangian
  rw [(solution_feasible_complementarity H hH a b nominal hb).2, sub_zero]

end SafeLearning.CompleteProjectionCharacterization
