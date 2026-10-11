import SafeLearning.CompleteBookProjects

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteProjectDomains

open SafeLearning.CompleteBookProjects

theorem zero_lipschitz_on_constant {X : Type*} (S : Set X) (g : X → ℝ)
    (h : ∀ a ∈ S, ∀ b ∈ S, |g a - g b| ≤ 0) :
    ∀ a ∈ S, ∀ b ∈ S, g a = g b := by
  intro a ha b hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (h a ha b hb) (abs_nonneg _)))

theorem domain_lower_certificate {X : Type*} (S : Set X) (g : X → ℝ)
    (center : X) (lower : ℝ) (hc : center ∈ S)
    (h : ∀ a ∈ S, ∀ b ∈ S, |g a - g b| ≤ 0)
    (hl : lower ≤ g center) (hn : 0 ≤ lower) : ∀ a ∈ S, 0 ≤ g a := by
  intro a ha
  rw [zero_lipschitz_on_constant S g h a ha center hc]
  exact hn.trans hl

theorem operating_interval_certificate (g : ℝ → ℝ) (center : ℝ)
    (hc : center ∈ Icc 0 1)
    (h : ∀ a ∈ Icc 0 1, ∀ b ∈ Icc 0 1, |g a - g b| ≤ 0)
    (hl : (4 / 25 : ℝ) ≤ g center) : ∀ a ∈ Icc 0 1, 0 ≤ g a :=
  domain_lower_certificate (Icc 0 1) g center (4 / 25) hc h hl (by norm_num)

theorem negative_domain_lower_underdetermined {X : Type*} (S : Set X)
    (lower : ℝ) (hl : lower < 0) :
    ∃ positive negative : X → ℝ,
      (∀ a ∈ S, ∀ b ∈ S,
        |positive a - positive b| ≤ 0 ∧ |negative a - negative b| ≤ 0) ∧
      (∀ a ∈ S, lower ≤ positive a ∧ lower ≤ negative a) ∧
      (∀ a ∈ S, 0 < positive a ∧ negative a < 0) := by
  refine ⟨fun _ => 1, fun _ => lower, ?_, ?_, ?_⟩
  · intros
    norm_num
  · intro a _
    exact ⟨by linarith, le_rfl⟩
  · intro a _
    exact ⟨by norm_num, hl⟩

theorem zero_has_no_multiplicative_inverse : ¬∃ r : ℝ, 0 * r = 1 := by
  norm_num

theorem noisier_strict_margin_set (a : ℝ) :
    (a ∈ Icc 0 1 ∧ 0 < tuningLower (9 / 50) (1 / 20) (1 / 5) a) ↔
      a ∈ Ico 0 (23 / 50) := by
  unfold tuningLower
  constructor
  · rintro ⟨ha, hl⟩
    have h := le_abs_self (a - 1 / 5)
    exact ⟨ha.1, by linarith⟩
  · intro ha
    have hab : |a - 1 / 5| < 13 / 50 := abs_lt.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
    refine ⟨⟨ha.1, by linarith [ha.2]⟩, ?_⟩
    linarith

theorem strict_margin_excludes_right_endpoint :
    tuningLower (9 / 50) (1 / 20) (1 / 5) (23 / 50) = 0 ∧
      ¬0 < tuningLower (9 / 50) (1 / 20) (1 / 5) (23 / 50) := by
  norm_num [tuningLower]

end SafeLearning.CompleteProjectDomains
