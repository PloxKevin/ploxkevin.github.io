import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeCertificateChecks

theorem actual_sum_of_squared_polynomials_is_nonnegative_at_every_real_point
    {I : Type*} [Fintype I] (q : I → Polynomial ℝ) (x : ℝ) :
    Polynomial.eval x (∑ i, q i ^ 2) ≥ 0 := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem actual_polynomial_with_an_sos_identity_is_globally_nonnegative
    {I : Type*} [Fintype I] (p : Polynomial ℝ) (q : I → Polynomial ℝ)
    (hcertificate : p = ∑ i, q i ^ 2) :
    ∀ x : ℝ, 0 ≤ Polynomial.eval x p := by
  intro x
  rw [hcertificate]
  exact actual_sum_of_squared_polynomials_is_nonnegative_at_every_real_point q x

theorem actual_domain_sos_multipliers_need_nonnegative_constraint_values
    {X I : Type*} [Fintype I] (D : Set X) (s g : I → X → ℝ)
    (hs : ∀ i x, 0 ≤ s i x) (hg : ∀ i x, x ∈ D → 0 ≤ g i x) :
    ∀ x ∈ D, 0 ≤ ∑ i, s i x * g i x := by
  intro x hx
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hs i x) (hg i x hx))

theorem actual_covering_grid_and_lipschitz_margin_certify_the_entire_domain
    {X : Type*} [PseudoMetricSpace X] (D grid : Set X) (b : X → ℝ)
    (L : NNReal) (radius : ℝ) (hgrid : grid ⊆ D)
    (hcover : ∀ x ∈ D, ∃ anchor ∈ grid, dist x anchor ≤ radius)
    (hb : LipschitzOnWith L b D)
    (hmargin : ∀ anchor ∈ grid, (L : ℝ) * radius ≤ b anchor) :
    ∀ x ∈ D, 0 ≤ b x := by
  intro x hx
  obtain ⟨anchor, ha, hdist⟩ := hcover x hx
  have hd := hb.dist_le_mul x hx anchor (hgrid ha)
  rw [Real.dist_eq] at hd
  have hlower := (abs_le.mp hd).1
  have hproduct := mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  have hm := hmargin anchor ha
  linarith

theorem actual_literal_sos_polynomial_and_grid_margin :
    (∀ x : ℝ, x^4+2*x^2+1=(x^2+1)^2 ∧ 0 ≤ x^4+2*x^2+1) ∧
    (2 : ℝ)*(1/10)=1/5 := by
  constructor
  · intro x
    have he : x^4+2*x^2+1=(x^2+1)^2 := by ring
    exact ⟨he, he ▸ sq_nonneg (x^2+1)⟩
  · norm_num

theorem actual_nonnegative_grid_values_alone_do_not_certify_between_grid_points :
    let residual : ℝ → ℝ := fun x => -2*x
    LipschitzWith 2 residual ∧
    (∀ x ∈ ({0} : Set ℝ), 0 ≤ residual x) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, ∃ anchor ∈ ({0} : Set ℝ), dist x anchor ≤ 1) ∧
    residual (1/2) < 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  · intro x hx
    simpa only [mem_singleton_iff.mp hx] using (show (0 : ℝ) ≤ -2*0 by norm_num)
  · intro x hx
    refine ⟨0, by simp, ?_⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hx.1] using hx.2

end SafeLearning.CompleteModulesLandscapeCertificateChecks
