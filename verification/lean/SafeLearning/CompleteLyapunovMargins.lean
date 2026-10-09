import Mathlib

namespace SafeLearning.CompleteLyapunovMargins

open Set
variable {E : Type*} [TopologicalSpace E]

theorem uniform_strict_descent_on_compact (F : E → E) (V : E → ℝ) (A : Set E)
    (hA : IsCompact A) (hne : A.Nonempty) (hF : Continuous F) (hV : Continuous V)
    (hstrict : ∀ x ∈ A, V (F x) < V x) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ A, V (F x) ≤ V x-η := by
  obtain ⟨a,ha,hmax⟩ := hA.exists_isMaxOn hne ((hV.comp hF).sub hV).continuousOn
  refine ⟨V a-V (F a), by linarith [hstrict a ha], ?_⟩
  intro x hx
  have hh := hmax hx
  change V (F x)-V x ≤ V (F a)-V a at hh
  linarith

theorem positive_minimum_on_compact (V : E → ℝ) (A : Set E)
    (hA : IsCompact A) (hne : A.Nonempty) (hV : Continuous V)
    (hpos : ∀ x ∈ A, 0 < V x) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ x ∈ A, ν ≤ V x := by
  obtain ⟨a,ha,hmin⟩ := hA.exists_isMinOn hne hV.continuousOn
  exact ⟨V a,hpos a ha,fun _ hx => hmin hx⟩

theorem compact_positive_value_slice (V : E → ℝ) (c lower : ℝ)
    (hV : Continuous V) (hc : IsCompact {x : E | V x ≤ c}) :
    IsCompact {x : E | V x ≤ c ∧ lower ≤ V x} := by
  exact hc.inter_right (isClosed_le continuous_const hV)

theorem linear_lyapunov_descent_bound (y : ℕ → ℝ) (η : ℝ)
    (hstep : ∀ n, y (n+1) ≤ y n-η) :
    ∀ n, y n ≤ y 0-(n : ℝ)*η := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep n
    simp only [Nat.cast_add, Nat.cast_one] at *
    nlinarith

theorem uniform_descent_incompatible_with_nonnegative_values (y : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η) (hnonneg : ∀ n, 0 ≤ y n) (hstep : ∀ n, y (n+1) ≤ y n-η) : False := by
  obtain ⟨n,hn⟩ := exists_nat_gt (y 0/η)
  have hm : y 0 < (n : ℝ)*η := (div_lt_iff₀ hη).mp hn
  have hb := linear_lyapunov_descent_bound y η hstep n
  linarith [hnonneg n]

end SafeLearning.CompleteLyapunovMargins
