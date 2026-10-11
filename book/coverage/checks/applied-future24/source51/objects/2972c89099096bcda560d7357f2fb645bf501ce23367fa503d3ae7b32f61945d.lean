import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsConvergenceConsequences

theorem actual_sum_and_product_rules_require_no_nonzero_limit
    (a b : ℕ→ℝ) (x y : ℝ) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n=>a n+b n) atTop (𝓝 (x+y)) ∧
      Tendsto (fun n=>a n*b n) atTop (𝓝 (x*y)) := ⟨ha.add hb,ha.mul hb⟩

theorem actual_order_of_limits_requires_no_nonzero_limit
    (a b : ℕ→ℝ) (x y : ℝ) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (hle : ∀ n,a n≤b n) : x≤y :=
  le_of_tendsto_of_tendsto ha hb (Eventually.of_forall hle)

theorem actual_alternating_signs_fail_the_literal_epsilon_one_test :
    ¬ ∃ limit : ℝ, ∃ T : ℕ, ∀ t≥T, |(-1:ℝ)^t-limit|<1 := by
  rintro ⟨limit,T,hT⟩
  have he := hT (2*T) (by omega)
  have ho := hT (2*T+1) (by omega)
  have htri := abs_sub_le (1:ℝ) limit (-1)
  have heq : (-1:ℝ)^(2*T)=1 := by simp [pow_mul]
  rw [heq] at he
  rw [pow_succ,heq,one_mul] at ho
  norm_num at htri
  have habs : |limit+1|=|-1-limit| := by
    rw [show -1-limit= -(limit+1) by ring,abs_neg]
  rw [habs] at htri
  linarith

theorem actual_alternating_sign_sequence_has_no_real_limit :
    ¬ ∃ limit : ℝ,Tendsto (fun n : ℕ=>(-1:ℝ)^n) atTop (𝓝 limit) := by
  rintro ⟨limit,hlimit⟩
  obtain ⟨T,hT⟩ := (Metric.tendsto_atTop.mp hlimit) 1 (by norm_num)
  exact actual_alternating_signs_fail_the_literal_epsilon_one_test
    ⟨limit,T,by simpa only [Real.dist_eq] using hT⟩

end SafeLearning.CompleteFoundationsConvergenceConsequences
