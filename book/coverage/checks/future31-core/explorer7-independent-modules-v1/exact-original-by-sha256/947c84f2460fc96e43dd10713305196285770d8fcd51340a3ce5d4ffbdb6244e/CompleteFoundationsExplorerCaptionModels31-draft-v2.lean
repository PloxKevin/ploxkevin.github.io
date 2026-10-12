import Mathlib
import SafeLearning.CompleteFoundationsBanachModels
import SafeLearning.CompleteFoundationsGeometricExample

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal

namespace SafeLearning.CompleteFoundationsExplorerCaptionModels31

def geometricPrefix (gamma : ℝ) (T : ℕ) : ℝ := ∑ t ∈ Finset.range T,gamma^t
def geometricTail (gamma : ℝ) (T : ℕ) : ℝ := ∑' t : ℕ,gamma^(t+T)
def geometricLimit (gamma : ℝ) : ℝ := 1/(1-gamma)

theorem actual_generic_discount_series_prefix_tail_and_full_limit
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (T : ℕ) :
    HasSum (fun t : ℕ => gamma^t) (geometricLimit gamma) ∧
      geometricPrefix gamma T=geometricLimit gamma*(1-gamma^T) ∧
      HasSum (fun t : ℕ => gamma^(t+T)) (geometricLimit gamma*gamma^T) ∧
      geometricTail gamma T=geometricLimit gamma*gamma^T ∧
      geometricPrefix gamma T+geometricTail gamma T=geometricLimit gamma := by
  have hsum : HasSum (fun t : ℕ => gamma^t) (geometricLimit gamma) :=
    by simpa only [geometricLimit,one_div] using hasSum_geometric_of_lt_one hg0 hg1
  have hp : geometricPrefix gamma T=geometricLimit gamma*(1-gamma^T) := by
    dsimp [geometricPrefix,geometricLimit]
    rw [geom_sum_eq hg1.ne]
    field_simp [(sub_pos.mpr hg1).ne',sub_ne_zero.mpr hg1.ne]
    ring
  have ht : HasSum (fun t : ℕ => gamma^(t+T)) (geometricLimit gamma*gamma^T) := by
    convert hsum.mul_right (gamma^T) using 1
    funext t
    rw [pow_add]
  refine ⟨hsum,hp,ht,ht.tsum_eq,?_⟩
  rw [hp,show geometricTail gamma T=geometricLimit gamma*gamma^T from ht.tsum_eq]
  ring

theorem actual_collected_and_remaining_fractions_of_the_positive_limit
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (T : ℕ) :
    0 < geometricLimit gamma ∧
      geometricPrefix gamma T/geometricLimit gamma=1-gamma^T ∧
      geometricTail gamma T/geometricLimit gamma=gamma^T ∧
      0 ≤ 1-gamma^T ∧ 1-gamma^T ≤ 1 ∧ 0 ≤ gamma^T ∧ gamma^T ≤ 1 := by
  have h := actual_generic_discount_series_prefix_tail_and_full_limit gamma hg0 hg1 T
  have hp : 0 < geometricLimit gamma := by unfold geometricLimit;positivity
  have hs : 0 ≤ gamma^T := pow_nonneg hg0 T
  have hu : gamma^T ≤ 1 := pow_le_one₀ hg0 hg1.le
  refine ⟨hp,?_,?_,by linarith,by linarith,hs,hu⟩
  · rw [h.2.1]
    field_simp
  · rw [h.2.2.2.1]
    field_simp

theorem actual_first_one_percent_horizon_exists_and_is_a_true_minimum
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, gamma^t ≤ 1/100 ↔ T ≤ t := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hg0 hg1
  have ht : ∀ᶠ t : ℕ in atTop,gamma^t < 1/100 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/100))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ht
  have hex : ∃ T : ℕ,gamma^T ≤ 1/100 := ⟨N,(hN N le_rfl).le⟩
  let T : ℕ := Nat.find hex
  have hT : gamma^T ≤ 1/100 := Nat.find_spec hex
  have hpos : 0 < T := by
    by_contra hh
    have hz : T=0 := by omega
    norm_num [hz] at hT
  refine ⟨T,hpos,?_⟩
  intro t
  constructor
  · intro h
    exact Nat.find_min' hex h
  · intro h
    exact (pow_le_pow_of_le_one hg0 hg1.le h).trans hT

theorem actual_zero_discount_one_percent_horizon_is_exactly_one (T : ℕ) :
    (0 : ℝ)^T ≤ 1/100 ↔ 1 ≤ T := by
  cases T with
  | zero => norm_num
  | succ T => simp

theorem actual_positive_discount_one_percent_horizon_logarithmic_criterion
    (gamma : ℝ) (hg0 : 0 < gamma) (hg1 : gamma < 1) (T : ℕ) :
    gamma^T ≤ 1/100 ↔ Real.log (1/100)/Real.log gamma ≤ (T : ℝ) :=
  SafeLearning.CompleteFoundationsGeometricExample.actual_generic_positive_discount_tolerance_iff_log_cutoff
    gamma (1/100) hg0 hg1 (by norm_num) T

/-- The displayed shifted bound is the actual Banach bound on a closed invariant
complete domain, started at the real iterate k0. A trajectory limit is not assumed. -/
theorem actual_shifted_banach_bound_for_the_caption
    (X : Set ℝ) (hclosed : IsClosed X) (hne : X.Nonempty)
    (g : X → X) (L : ℝ≥0) (hL : L < 1)
    (hbound : ∀ x y : X, |(g x : ℝ)-(g y : ℝ)| ≤
      (L : ℝ)*|(x : ℝ)-(y : ℝ)|) :
    ∃ p : X,g p=p ∧ ∀ (x : X) (k0 k : ℕ),k0 ≤ k →
      |((g^[k] x : X) : ℝ)-(p : ℝ)| ≤
        (L : ℝ)^(k-k0)*
          |((g^[k0+1] x : X) : ℝ)-((g^[k0] x : X) : ℝ)|/(1-(L : ℝ)) := by
  obtain ⟨p,hp,_,_,_,he⟩ :=
    SafeLearning.CompleteFoundationsBanachModels.actual_closed_nonempty_subset_banach
      X hclosed hne g L hL (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨p,hp,?_⟩
  intro x k0 k hk
  have hh := he (g^[k0] x) (k-k0)
  have hi : g^[k-k0] (g^[k0] x)=g^[k] x := by
    rw [← Function.iterate_add_apply,Nat.sub_add_cancel hk]
  have hs : g (g^[k0] x)=g^[k0+1] x := by rw [Function.iterate_succ_apply']
  simp only [hi,hs,Real.norm_eq_abs] at hh
  convert hh using 1
  ring

theorem actual_cobweb_transition_and_fixed_point_diagonal
    (g : ℝ → ℝ) (x p : ℝ) (hp : g p=p) (k : ℕ) :
    (g^[k] x,g (g^[k] x))=(g^[k] x,g^[k+1] x) ∧
      (p,g p)=(p,p) := by
  simp [Function.iterate_succ_apply',hp]

end SafeLearning.CompleteFoundationsExplorerCaptionModels31
