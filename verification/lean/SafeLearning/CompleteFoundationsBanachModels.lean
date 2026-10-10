import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsBanachModels

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem actual_closed_nonempty_subset_banach
    (X : Set E) (hclosed : IsClosed X) (hne : X.Nonempty)
    (g : X → X) (L : NNReal) (hL : L < 1)
    (hbound : ∀ x y : X, ‖(g x : E) - (g y : E)‖ ≤ (L : ℝ) * ‖(x : E) - (y : E)‖) :
    ∃ p : X, g p = p ∧ (∀ q : X, g q = q → q = p) ∧
      (∀ x : X, Tendsto (fun n : ℕ => g^[n] x) atTop (𝓝 p)) ∧
      (∀ (x : X) (n : ℕ), ‖((g^[n] x : X) : E) - (p : E)‖ ≤
        (L : ℝ)^n * ‖(x : E) - (p : E)‖) ∧
      (∀ (x : X) (n : ℕ), ‖((g^[n] x : X) : E) - (p : E)‖ ≤
        (L : ℝ)^n / (1 - (L : ℝ)) * ‖(g x : E) - (x : E)‖) := by
  let : Nonempty X := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let : CompleteSpace X := hclosed.isComplete.completeSpace_coe
  have hg : ContractingWith L g := by
    constructor
    · exact hL
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm] using hbound x y
  let p : X := hg.fixedPoint
  have hp : g p = p := hg.fixedPoint_isFixedPt
  refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hg.fixedPoint_unique hq
  · intro x
    exact hg.tendsto_iterate_fixedPoint x
  · intro x n
    have hh := hg.toLipschitzWith.iterate n |>.dist_le_mul x p
    have hi : g^[n] p = p := (show Function.IsFixedPt g p from hp).iterate n
    simpa only [hi, Subtype.dist_eq, dist_eq_norm, NNReal.coe_pow] using hh
  · intro x n
    have hh := hg.apriori_dist_iterate_fixedPoint_le x n
    have hh' : ‖((g^[n] x : X) : E) - (p : E)‖ ≤
        ‖(x : E) - (g x : E)‖ * (L : ℝ)^n / (1 - (L : ℝ)) := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hh
    calc
      _ ≤ ‖(x : E) - (g x : E)‖ * (L : ℝ)^n / (1 - (L : ℝ)) := hh'
      _ = _ := by rw [norm_sub_rev]; ring

theorem actual_complete_ambient_banach
    (g : E → E) (L : NNReal) (hg : ContractingWith L g) :
    ∃ p : E, g p = p ∧ (∀ q, g q = q → q = p) ∧
      ∀ x, Tendsto (fun n : ℕ => g^[n] x) atTop (𝓝 p) := by
  refine ⟨hg.fixedPoint, hg.fixedPoint_isFixedPt, ?_, ?_⟩
  · intro q hq; exact hg.fixedPoint_unique hq
  · intro x; exact hg.tendsto_iterate_fixedPoint x

theorem actual_factor_one_translation_has_no_fixed_point :
    LipschitzWith 1 (fun x : ℝ => x + 1) ∧ ¬∃ x : ℝ, x + 1 = x := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  · rintro ⟨x, hx⟩; linarith

theorem actual_factor_one_negation_and_two_cycle (x : ℝ) :
    LipschitzWith 1 (fun x : ℝ => -x) ∧
      (fun y : ℝ => -y)^[2] x = x ∧
      (∀ n : ℕ, (fun y : ℝ => -y)^[2*n] x = x) ∧
      (∀ n : ℕ, (fun y : ℝ => -y)^[2*n+1] x = -x) := by
  have he : ∀ n : ℕ, (fun y : ℝ => -y)^[n] x = (-1 : ℝ)^n * x := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro a b; simp [Real.dist_eq, ←abs_neg (a-b)]
  · simp [he]
  · intro n; simp [he, pow_mul]
  · intro n; simp [he, pow_succ, pow_mul]

theorem actual_contraction_without_self_map_has_fixed_point_outside :
    (∀ x y : ℝ, |(x/2+1)-(y/2+1)| = (1/2 : ℝ)*|x-y|) ∧
      (∀ x : ℝ, x/2+1=x ↔ x=2) ∧ (2 : ℝ)∉Icc 0 1 ∧
      (1/2+1 : ℝ)∉Icc 0 1 := by
  constructor
  · intro x y
    rw [show (x/2+1)-(y/2+1)=(1/2)*(x-y) by ring, abs_mul]
    norm_num
  constructor
  · intro x; constructor <;> intro h <;> linarith
  norm_num

theorem actual_nonclosed_half_interval_self_map_and_no_fixed_point :
    (∀ x∈Ioc (0 : ℝ) 1, x/2∈Ioc (0 : ℝ) 1) ∧
      (∀ x y : ℝ, |x/2-y/2| = (1/2 : ℝ)*|x-y|) ∧
      ¬∃ x∈Ioc (0 : ℝ) 1, x/2=x := by
  constructor
  · intro x hx; constructor <;> linarith [hx.1, hx.2]
  constructor
  · intro x y
    rw [show x/2-y/2=(1/2)*(x-y) by ring, abs_mul]
    norm_num
  · rintro ⟨x, hx, he⟩; linarith [hx.1]

theorem actual_nonclosed_interval_iterates_tend_to_excluded_zero :
    (∀ n : ℕ, (1/2 : ℝ)^n∈Ioc (0 : ℝ) 1) ∧
      (∀ n : ℕ, (1/2 : ℝ)^(n+1)=(1/2 : ℝ)^n/2) ∧
      Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) ∧
      (0 : ℝ)∉Ioc 0 1 ∧ ¬IsClosed (Ioc (0 : ℝ) 1) := by
  have hmem : ∀ n : ℕ, (1/2 : ℝ)^n∈Ioc (0 : ℝ) 1 := by
    intro n
    exact ⟨pow_pos (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨hmem, ?_, ht, by norm_num, ?_⟩
  · intro n; rw [pow_succ]; ring
  · intro hc
    have hz := hc.mem_of_tendsto ht (Filter.Eventually.of_forall hmem)
    norm_num at hz

end SafeLearning.CompleteFoundationsBanachModels
