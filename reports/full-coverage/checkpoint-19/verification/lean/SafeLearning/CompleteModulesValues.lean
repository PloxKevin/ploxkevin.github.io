import SafeLearning.Modules
import SafeLearning.BookApplications

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesValues

theorem finite_discounted_doomed_bound (reward : ℕ → ℝ) (discount bound penalty : ℝ)
    (failure horizon : ℕ) (hd : 0 ≤ discount) (hd1 : discount < 1)
    (hb : 0 ≤ bound) (hp : 0 ≤ penalty) (ht : failure ≤ horizon)
    (hr : ∀ t < failure+1, reward t ≤ bound) :
    (∑ t ∈ Finset.range (failure+1), discount^t*reward t)-penalty*discount^failure ≤
      bound*(1-discount^(horizon+1))/(1-discount)-penalty*discount^horizon := by
  have hreward : (∑ t ∈ Finset.range (failure+1), discount^t*reward t) ≤
      ∑ t ∈ Finset.range (horizon+1), discount^t*bound := by
    calc
      _ ≤ ∑ t ∈ Finset.range (failure+1), discount^t*bound := by
        apply Finset.sum_le_sum
        intro t hm
        exact mul_le_mul_of_nonneg_left (hr t (Finset.mem_range.mp hm)) (pow_nonneg hd t)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.add_le_add_right ht 1)) (by intros; positivity)
  have hpenalty : penalty*discount^horizon ≤ penalty*discount^failure :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hd (le_of_lt hd1) ht) hp
  have hgeom : (∑ t ∈ Finset.range (horizon+1), discount^t*bound)=
      bound*(1-discount^(horizon+1))/(1-discount) := by
    rw [← Finset.sum_mul,geom_sum_eq (ne_of_lt hd1)]
    rw [show discount-1=-(1-discount) by ring,div_neg]
    ring
  rw [hgeom] at hreward
  linarith

theorem supremum_doomed_bound {X : Type*} (returns : X → ℝ) (upper : ℝ)
    (hne : (Set.range returns).Nonempty) (h : ∀ x, returns x ≤ upper) :
    sSup (Set.range returns) ≤ upper := by
  apply csSup_le hne
  rintro _ ⟨x,rfl⟩
  exact h x

theorem doomed_example :
    (1:ℝ)*(1-(9/10)^3)/(1-9/10)-20*(9/10)^2 = -1349/100 := by norm_num

theorem negative_reward_extension_reverses :
    -(1:ℝ)-(9/10) > -(1:ℝ)-(9/10)-(9/10)^2 := by norm_num

theorem two_step_slope_bound (discount cost penalty : ℝ)
    (hd : 0 ≤ discount) (hd1 : discount ≤ 1) (hc : 0 ≤ cost) (hp : 0 ≤ penalty) :
    max (-cost-discount*penalty) (-cost-discount*cost-discount^2*penalty) ≤
      -penalty*discount^2 := by
  have hprod := mul_nonneg hp (mul_nonneg hd (sub_nonneg.mpr hd1))
  have hdc := mul_nonneg hd hc
  apply max_le <;> nlinarith

theorem slow_slope_strictly_better (discount cost penalty : ℝ) (hd : 0 < discount) :
    -cost-discount*penalty < -cost-discount*cost-discount^2*penalty ↔
      cost < penalty*(1-discount) := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem negative_reward_slope_bound_false (discount cost penalty : ℝ)
    (hd : 0 < discount) (hc : 0 < cost) :
    -cost*(1+discount+discount^2)-penalty*discount^2 <
      -cost-discount*cost-discount^2*penalty := by
  have h := mul_pos hc (sq_pos_of_pos hd)
  nlinarith

def binaryValue (penalty : ℝ) (isUnsafe : Bool) : ℝ := if isUnsafe then 1-penalty else 0

theorem every_binary_optimizer_safe_iff (penalty : ℝ) :
    (∀ action, (∀ other, binaryValue penalty other ≤ binaryValue penalty action) →
      action=false) ↔ 1 < penalty := by
  constructor
  · intro h
    by_contra hn
    have hp : penalty ≤ 1 := le_of_not_gt hn
    have ht : ∀ other, binaryValue penalty other ≤ binaryValue penalty true := by
      intro other
      cases other <;> simp [binaryValue] <;> linarith
    have := h true ht
    contradiction
  · intro hp action hmax
    cases action
    · rfl
    · have := hmax false
      simp only [binaryValue,Bool.false_eq_true,if_false,if_true] at this
      linarith

theorem equality_retains_unsafe_optimizer :
    ∀ other, binaryValue 1 other ≤ binaryValue 1 true := by
  intro other
  cases other <;> norm_num [binaryValue]

theorem arrival_time_example : -(20:ℝ)*(9/10)^3 = -729/50 ∧
    -(20:ℝ)*(9/10)^0 = -20 ∧ -(20:ℝ) < -(20:ℝ)*(9/10)^3 := by norm_num

theorem contraction_residual_bound {X : Type*} [PseudoMetricSpace X]
    (operator : X → X) (fixed approximate : X) (discount residual : ℝ)
    (hd1 : discount < 1)
    (hcontract : ∀ x y, dist (operator x) (operator y) ≤ discount*dist x y)
    (hfixed : operator fixed=fixed) (hresidual : dist approximate (operator approximate) ≤ residual) :
    dist approximate fixed ≤ residual/(1-discount) := by
  have htriangle := dist_triangle approximate (operator approximate) fixed
  have hc := hcontract approximate fixed
  rw [hfixed] at hc
  apply (le_div_iff₀ (by linarith : 0 < 1-discount)).mpr
  nlinarith

theorem bellman_residual_example : (2/1000:ℝ)/(1-95/100)=1/25 := by norm_num

end SafeLearning.CompleteModulesValues
