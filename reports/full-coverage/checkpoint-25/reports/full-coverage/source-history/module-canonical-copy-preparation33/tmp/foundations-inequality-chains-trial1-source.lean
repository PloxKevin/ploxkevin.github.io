import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsInequalityChains

theorem actual_triangle_and_reverse_triangle_bounds
    {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ≤ ‖a‖ + ‖b‖ ∧ |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
  ⟨norm_add_le a b, abs_norm_sub_norm_le a b⟩

theorem actual_nonnegative_multiplication_preserves_weak_order
    (a b c : ℝ) (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b ∧ a * c ≤ b * c :=
  ⟨mul_le_mul_of_nonneg_left hab hc, mul_le_mul_of_nonneg_right hab hc⟩

theorem actual_negative_multiplication_reverses_order
    (a b c : ℝ) (hc : c < 0) :
    (a ≤ b ↔ c * b ≤ c * a) ∧ (a < b ↔ c * b < c * a) := by
  constructor <;> constructor <;> intro h <;> nlinarith

theorem actual_positive_multiplication_preserves_strict_order
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    c * a < c * b ∧ a * c < b * c :=
  ⟨mul_lt_mul_of_pos_left hab hc, mul_lt_mul_of_pos_right hab hc⟩

theorem actual_monotone_function_preserves_weak_order
    {A B : Type*} [Preorder A] [Preorder B]
    (f : A → B) (hf : Monotone f) (a b : A) (hab : a ≤ b) : f a ≤ f b :=
  hf hab

theorem actual_strictly_increasing_function_preserves_strict_order
    {A B : Type*} [Preorder A] [Preorder B]
    (f : A → B) (hf : StrictMono f) (a b : A) (hab : a < b) : f a < f b :=
  hf hab

theorem actual_exponential_preserves_weak_and_strict_order (a b : ℝ) :
    (Real.exp a ≤ Real.exp b ↔ a ≤ b) ∧
      (Real.exp a < Real.exp b ↔ a < b) :=
  ⟨Real.exp_le_exp, Real.exp_lt_exp⟩

theorem actual_logarithm_preserves_order_on_its_positive_domain
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.log a ≤ Real.log b ↔ a ≤ b) ∧
      (Real.log a < Real.log b ↔ a < b) :=
  ⟨Real.log_le_log_iff ha hb, Real.log_lt_log_iff ha hb⟩

theorem actual_square_root_preserves_order_on_its_nonnegative_domain
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a ≤ Real.sqrt b ↔ a ≤ b) ∧
      (Real.sqrt a < Real.sqrt b ↔ a < b) :=
  ⟨Real.sqrt_le_sqrt_iff hb, Real.sqrt_lt_sqrt_iff ha⟩

theorem actual_finite_weak_order_chain_bounds_its_endpoints
    {A : Type*} [Preorder A] (values : ℕ → A) (length : ℕ)
    (hlinks : ∀ k < length, values k ≤ values (k + 1)) :
    values 0 ≤ values length := by
  induction length with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih fun k hk => hlinks k (by omega)).trans (hlinks n (by omega))

theorem actual_one_strict_link_makes_the_finite_chain_strict
    {A : Type*} [Preorder A] (values : ℕ → A) (length : ℕ)
    (hlinks : ∀ k < length, values k ≤ values (k + 1))
    (hstrict : ∃ k < length, values k < values (k + 1)) :
    values 0 < values length := by
  obtain ⟨index, hi, hs⟩ := hstrict
  have hp : values 0 ≤ values index :=
    actual_finite_weak_order_chain_bounds_its_endpoints values index
      (fun k hk => hlinks k (by omega))
  have ht : values (index + 1) ≤ values length := by
    have htail := actual_finite_weak_order_chain_bounds_its_endpoints
      (fun k => values (index + 1 + k)) (length - (index + 1))
      (fun k hk => by
        simpa only [Nat.add_assoc] using hlinks (index + 1 + k) (by omega))
    have he : index + 1 + (length - (index + 1)) = length := by omega
    simpa only [Nat.add_zero, he] using htail
  exact lt_of_lt_of_le (lt_of_le_of_lt hp hs) ht

end SafeLearning.CompleteFoundationsInequalityChains
