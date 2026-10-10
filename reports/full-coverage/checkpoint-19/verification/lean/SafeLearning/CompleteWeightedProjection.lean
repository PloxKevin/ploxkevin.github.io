import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace SafeLearning.CompleteWeightedProjection

def energy {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (H *ᵥ x)

theorem energy_nonneg {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (hH : H.PosDef) (x : ι → ℝ) : 0 ≤ energy H x := by
  simpa only [energy,star_trivial] using hH.posSemidef.dotProduct_mulVec_nonneg x

theorem energy_positive {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (hH : H.PosDef) (x : ι → ℝ) (hx : x ≠ 0) : 0 < energy H x := by
  simpa only [energy,star_trivial] using hH.dotProduct_mulVec_pos hx

theorem energy_expansion {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (hH : H.IsSymm) (x y : ι → ℝ) :
    energy H (x+y)=energy H x+energy H y+2*(x ⬝ᵥ (H *ᵥ y)) := by
  simp only [energy,mulVec_add,add_dotProduct,dotProduct_add]
  rw [hH.dotProduct_mulVec_comm (x := y) (y := x)]
  ring

/-- The KKT conditions imply global optimality by an exact positive quadratic
remainder. They are not an assumed optimality or convexity conclusion. -/
theorem kkt_global_optimal {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a mu : ℝ) (b nominal candidate : ι → ℝ)
    (hmu : 0 ≤ mu) (hs : H *ᵥ (candidate-nominal)=mu • b)
    (hcomp : mu*(a+b ⬝ᵥ candidate)=0) (u : ι → ℝ) (hu : 0 ≤ a+b ⬝ᵥ u) :
    energy H (candidate-nominal) ≤ energy H (u-nominal) := by
  have he : u-nominal=(u-candidate)+(candidate-nominal) := by abel
  rw [he,energy_expansion H hH.isHermitian.isSymm,hs,dotProduct_smul,smul_eq_mul]
  have hq := energy_nonneg H hH (u-candidate)
  have hp := mul_nonneg hmu hu
  have hc : mu*((u-candidate) ⬝ᵥ b) ≥ 0 := by
    rw [dotProduct_comm, dotProduct_sub]
    nlinarith
  linarith

theorem kkt_unique {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a mu : ℝ) (b nominal candidate : ι → ℝ)
    (hmu : 0 ≤ mu) (hs : H *ᵥ (candidate-nominal)=mu • b)
    (hcomp : mu*(a+b ⬝ᵥ candidate)=0) (u : ι → ℝ) (hu : 0 ≤ a+b ⬝ᵥ u)
    (heq : energy H (u-nominal)=energy H (candidate-nominal)) : u=candidate := by
  by_contra hn
  have hq := energy_positive H hH (u-candidate) (sub_ne_zero.mpr hn)
  have he : u-nominal=(u-candidate)+(candidate-nominal) := by abel
  rw [he,energy_expansion H hH.isHermitian.isSymm,hs,dotProduct_smul,smul_eq_mul] at heq
  have hp := mul_nonneg hmu hu
  have hc : mu*((u-candidate) ⬝ᵥ b) ≥ 0 := by
    rw [dotProduct_comm, dotProduct_sub]
    nlinarith
  linarith

def multiplier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (a : ℝ) (b nominal : ι → ℝ) : ℝ :=
  max 0 (-(a+b ⬝ᵥ nominal)/(b ⬝ᵥ (H⁻¹ *ᵥ b)))

def solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (a : ℝ) (b nominal : ι → ℝ) : ι → ℝ :=
  nominal+multiplier H a b nominal • (H⁻¹ *ᵥ b)

theorem inverse_denominator_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (b : ι → ℝ) (hb : b ≠ 0) :
    0 < b ⬝ᵥ (H⁻¹ *ᵥ b) := by
  simpa only [star_trivial] using hH.inv.dotProduct_mulVec_pos hb

theorem inverse_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (b : ι → ℝ) :
    H *ᵥ (H⁻¹ *ᵥ b)=b := by
  rw [mulVec_mulVec,H.mul_nonsing_inv ((H.isUnit_iff_isUnit_det).mp hH.isUnit),one_mulVec]

theorem solution_stationarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) :
    H *ᵥ (solution H a b nominal-nominal)=multiplier H a b nominal • b := by
  simp only [solution,add_sub_cancel_left,mulVec_smul,inverse_direction H hH b]

theorem solution_feasible_complementarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) (hb : b ≠ 0) :
    0 ≤ a+b ⬝ᵥ solution H a b nominal ∧
    multiplier H a b nominal*(a+b ⬝ᵥ solution H a b nominal)=0 := by
  have hd := inverse_denominator_positive H hH b hb
  by_cases hpsi : 0 ≤ a+b ⬝ᵥ nominal
  · have hm : multiplier H a b nominal=0 := by
      unfold multiplier
      rw [max_eq_left]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hd)
    simp only [solution,hm,zero_smul,add_zero,zero_mul,and_true]
    exact hpsi
  · have hm : multiplier H a b nominal=-(a+b ⬝ᵥ nominal)/(b ⬝ᵥ (H⁻¹ *ᵥ b)) := by
      unfold multiplier
      rw [max_eq_right]
      exact div_nonneg (by linarith) (le_of_lt hd)
    have hz : a+b ⬝ᵥ solution H a b nominal=0 := by
      simp only [solution,dotProduct_add,dotProduct_smul,smul_eq_mul,hm]
      rw [div_mul_cancel₀ _ (ne_of_gt hd)]
      ring
    rw [hz]
    simp

theorem weighted_halfspace_unique_minimum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a : ℝ) (b nominal : ι → ℝ) (hb : b ≠ 0) :
    0 ≤ a+b ⬝ᵥ solution H a b nominal ∧
    ∀ u : ι → ℝ, 0 ≤ a+b ⬝ᵥ u →
      energy H (solution H a b nominal-nominal) ≤ energy H (u-nominal) ∧
      (energy H (u-nominal)=energy H (solution H a b nominal-nominal) →
        u=solution H a b nominal) := by
  have hc := solution_feasible_complementarity H hH a b nominal hb
  refine ⟨hc.1,fun u hu => ⟨?_,?_⟩⟩
  · exact kkt_global_optimal H hH a (multiplier H a b nominal) b nominal _
      (le_max_left _ _) (solution_stationarity H hH a b nominal) hc.2 u hu
  · exact kkt_unique H hH a (multiplier H a b nominal) b nominal _
      (le_max_left _ _) (solution_stationarity H hH a b nominal) hc.2 u hu

def exampleWeight : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,4]

theorem exampleWeight_positive : exampleWeight.PosDef := by
  rw [exampleWeight,Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem example_inverse_direction :
    exampleWeight⁻¹ *ᵥ (![1,1] : Fin 2 → ℝ)=![1,1/4] := by
  letI : Invertible exampleWeight := exampleWeight_positive.isUnit.invertible
  apply Matrix.inv_mulVec_eq_vec
  ext i
  fin_cases i <;> norm_num [exampleWeight,Matrix.mulVec,Fin.sum_univ_succ]

theorem example_solution :
    solution exampleWeight (-3) (![1,1] : Fin 2 → ℝ) ![1,1]=![9/5,6/5] := by
  simp only [solution,multiplier,example_inverse_direction]
  norm_num [dotProduct,Fin.sum_univ_succ]

theorem example_minimum_unique (u : Fin 2 → ℝ) (hu : 3 ≤ u 0+u 1) :
    energy exampleWeight (![9/5,6/5]-![1,1]) ≤ energy exampleWeight (u-![1,1]) ∧
    (energy exampleWeight (u-![1,1])=energy exampleWeight (![9/5,6/5]-![1,1]) →
      u=![9/5,6/5]) := by
  have h := (weighted_halfspace_unique_minimum exampleWeight exampleWeight_positive (-3)
    (![1,1] : Fin 2 → ℝ) ![1,1] (by intro he;have h0 := congrFun he 0;norm_num at h0)).2 u
  rw [example_solution] at h
  apply h
  norm_num [dotProduct,Fin.sum_univ_succ]
  linarith

end SafeLearning.CompleteWeightedProjection
