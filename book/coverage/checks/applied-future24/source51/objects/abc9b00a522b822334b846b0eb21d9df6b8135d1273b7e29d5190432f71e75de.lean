import SafeLearning.CompleteFiniteCMDPDeterministicVertices
import SafeLearning.CompleteFiniteNonnegativeAffineExtrema

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteCMDPActiveFlow

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery SafeLearning.CompleteFiniteNonnegativeAffineExtrema

variable {S A : Type*} [Fintype S] [Fintype A]

def flowLinearMap (M : Model S A) (γ : ℝ) :
    ((S × A) → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun x t := (∑ a, x (t, a)) - γ * ∑ s, ∑ a, x (s, a) * M.transition s a t
  map_add' x y := by
    ext t
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    ext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

theorem actual_flat_affine_feasibility_iff_true_bellman_flow
    (M : Model S A) (γ : ℝ) (x : (S × A) → ℝ) :
    AffineFeasible (flowLinearMap M γ) (fun t => (1 - γ) * M.initial t) x ↔
      FlowFeasible M γ (fun s a => x (s, a)) := by
  constructor
  · intro h
    refine ⟨fun s a => h.1 (s, a), ?_⟩
    intro t
    have ht := congrArg (fun y : S → ℝ => y t) h.2
    change (∑ a, x (t, a)) - γ * (∑ s, ∑ a, x (s, a) * M.transition s a t) =
      (1 - γ) * M.initial t at ht
    change (∑ a, x (t, a)) = (1 - γ) * M.initial t +
      γ * (∑ s, ∑ a, x (s, a) * M.transition s a t)
    linarith
  · intro h
    refine ⟨fun p => h.1 p.1 p.2, ?_⟩
    ext t
    change (∑ a, x (t, a)) - γ * (∑ s, ∑ a, x (s, a) * M.transition s a t) =
      (1 - γ) * M.initial t
    have ht := h.2 t
    change (∑ a, x (t, a)) = (1 - γ) * M.initial t +
      γ * (∑ s, ∑ a, x (s, a) * M.transition s a t) at ht
    linarith

theorem actual_flow_extreme_point_is_flat_affine_extreme_point
    (M : Model S A) (γ : ℝ) (ρ : S → A → ℝ)
    (hext : ρ ∈ Set.extremePoints ℝ {y | FlowFeasible M γ y}) :
    (fun p : S × A => ρ p.1 p.2) ∈ Set.extremePoints ℝ
      {x | AffineFeasible (flowLinearMap M γ) (fun t => (1 - γ) * M.initial t) x} := by
  refine ⟨(actual_flat_affine_feasibility_iff_true_bellman_flow M γ _).mpr hext.1, ?_⟩
  intro x hx y hy hsegment
  rcases hsegment with ⟨u, v, hu, hv, huv, he⟩
  have hcurried : ρ ∈ openSegment ℝ (fun s a => x (s, a)) (fun s a => y (s, a)) := by
    refine ⟨u, v, hu, hv, huv, ?_⟩
    funext s a
    exact congrArg (fun z : (S × A) → ℝ => z (s, a)) he
  have hc := hext.2
    ((actual_flat_affine_feasibility_iff_true_bellman_flow M γ x).mp hx)
    ((actual_flat_affine_feasibility_iff_true_bellman_flow M γ y).mp hy) hcurried
  funext p
  exact congrArg (fun z : S → A → ℝ => z p.1 p.2) hc

theorem actual_inactive_target_has_zero_discounted_supported_transition
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ)
    (t : S) (ht : stateMarginal ρ t = 0) (s : S) (a : A) (ha : 0 < ρ s a) :
    γ * M.transition s a t = 0 := by
  have hcoord₁ := Finset.single_le_sum (s := Finset.univ)
    (fun b _ => mul_nonneg (hρ.1 s b) (M.transition_nonneg s b t)) (Finset.mem_univ a)
  have hcoord₂ := Finset.single_le_sum (s := Finset.univ)
    (f := fun z => ∑ b, ρ z b * M.transition z b t)
    (fun z _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (hρ.1 z b) (M.transition_nonneg z b t))) (Finset.mem_univ s)
  have hflow := hρ.2 t
  rw [ht] at hflow
  have hstart : 0 ≤ (1 - γ) * M.initial t :=
    mul_nonneg (by linarith) (M.initial_nonneg t)
  have htotal : γ * (∑ z, ∑ b, ρ z b * M.transition z b t) ≤ 0 := by linarith
  have hupper := (mul_le_mul_of_nonneg_left (hcoord₁.trans hcoord₂) hγ0).trans htotal
  have hz : γ * (ρ s a * M.transition s a t) = 0 :=
    le_antisymm hupper (mul_nonneg hγ0 (mul_nonneg ha.le (M.transition_nonneg s a t)))
  have hfactor : ρ s a * (γ * M.transition s a t) = 0 := by nlinarith [hz]
  exact (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt ha)

theorem actual_supported_direction_flow_is_zero_on_inactive_rows
    (M : Model S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ) (δ : (S × A) → ℝ)
    (hsupport : ∀ p, ¬ 0 < ρ p.1 p.2 → δ p = 0)
    (t : S) (ht : stateMarginal ρ t = 0) : flowLinearMap M γ δ t = 0 := by
  have hrow : (∑ a, δ (t, a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hz := actual_zero_nonnegative_row_has_zero_coordinates ρ hρ.1 t ht a
    exact hsupport (t, a) (by simp [hz])
  have hterm (s : S) (a : A) : γ * (δ (s, a) * M.transition s a t) = 0 := by
    by_cases ha : 0 < ρ s a
    · have hz := actual_inactive_target_has_zero_discounted_supported_transition
        M γ hγ0 hγ1 ρ hρ t ht s a ha
      calc
        _ = δ (s, a) * (γ * M.transition s a t) := by ring
        _ = 0 := by rw [hz, mul_zero]
    · rw [hsupport (s, a) ha, zero_mul, mul_zero]
  have hincoming : γ * (∑ s, ∑ a, δ (s, a) * M.transition s a t) = 0 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro s _
    exact Finset.sum_eq_zero (fun a _ => hterm s a)
  change (∑ a, δ (t, a)) - γ * (∑ s, ∑ a, δ (s, a) * M.transition s a t) = 0
  rw [hrow, hincoming, sub_self]

end SafeLearning.CompleteFiniteCMDPActiveFlow
