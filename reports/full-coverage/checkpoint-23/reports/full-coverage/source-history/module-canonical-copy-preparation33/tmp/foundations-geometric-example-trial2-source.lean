import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteFoundationsGeometricExample

def sourceDiscount : ℝ := 9/10
def sourcePrefix (T : ℕ) : ℝ := ∑ t ∈ Finset.range T,sourceDiscount^t
def sourceTail (T : ℕ) : ℝ := ∑' t : ℕ,sourceDiscount^(t+T)
def sourceExactCutoff : ℝ := Real.log (1/100)/Real.log sourceDiscount
def sourceCoarseCutoff : ℝ := Real.log 100/(1-sourceDiscount)

theorem actual_source_geometric_limit_prefix_and_tail (T : ℕ) :
    HasSum (fun t : ℕ => sourceDiscount^t) 10 ∧
    sourcePrefix T=10*(1-sourceDiscount^T) ∧
    HasSum (fun t : ℕ => sourceDiscount^(t+T)) (10*sourceDiscount^T) ∧
    sourceTail T=10*sourceDiscount^T ∧ sourcePrefix T+sourceTail T=10 := by
  have hg : HasSum (fun t : ℕ => sourceDiscount^t) 10 := by
    convert hasSum_geometric_of_lt_one
      (by norm_num [sourceDiscount] : 0 ≤ sourceDiscount)
      (by norm_num [sourceDiscount] : sourceDiscount<1) using 1 <;>
        norm_num [sourceDiscount]
  have hp : sourcePrefix T=10*(1-sourceDiscount^T) := by
    dsimp [sourcePrefix]
    rw [geom_sum_eq (by norm_num [sourceDiscount] : sourceDiscount≠1)]
    norm_num [sourceDiscount]
    ring
  have ht : HasSum (fun t : ℕ => sourceDiscount^(t+T)) (10*sourceDiscount^T) := by
    convert hg.mul_left (sourceDiscount^T) using 1
    · funext t;rw [pow_add];ring
    · ring
  refine ⟨hg,hp,ht,ht.tsum_eq,?_⟩
  rw [hp,show sourceTail T=10*sourceDiscount^T from ht.tsum_eq]
  ring

theorem actual_source_ten_term_values_have_true_display_roundings :
    |sourceDiscount^10-(3487/10000:ℝ)|<1/20000 ∧
    |sourcePrefix 10-(6513/1000:ℝ)|<1/2000 ∧
    |sourceTail 10-(3487/1000:ℝ)|<1/2000 := by
  have h := actual_source_geometric_limit_prefix_and_tail 10
  rw [h.2.1,h.2.2.2.1]
  norm_num [sourceDiscount]

theorem actual_source_ten_term_values_differ_strictly_from_the_printed_decimals :
    sourceDiscount^10<(3487/10000:ℝ) ∧
    (6513/1000:ℝ)<sourcePrefix 10 ∧
    sourceTail 10<(3487/1000:ℝ) := by
  have h := actual_source_geometric_limit_prefix_and_tail 10
  rw [h.2.1,h.2.2.2.1]
  norm_num [sourceDiscount]

theorem actual_generic_positive_discount_tolerance_iff_log_cutoff
    (gamma epsilon : ℝ) (hg0 : 0<gamma) (hg1 : gamma<1)
    (he0 : 0<epsilon) (T : ℕ) :
    gamma^T≤epsilon ↔ Real.log epsilon/Real.log gamma≤(T:ℝ) := by
  have hl : Real.log gamma<0 := Real.log_neg hg0 hg1
  rw [←Real.log_le_log_iff (pow_pos hg0 T) he0,Real.log_pow,
    div_le_iff_of_neg hl]

theorem actual_source_first_integer_one_percent_horizon_is_forty_four (T : ℕ) :
    sourceDiscount^T≤1/100 ↔ 44≤T := by
  have h43 : (1/100:ℝ)<sourceDiscount^43 := by norm_num [sourceDiscount]
  have h44 : sourceDiscount^44≤1/100 := by norm_num [sourceDiscount]
  constructor
  · intro h
    by_contra hn
    have hi : T≤43 := by omega
    have hp := pow_le_pow_of_le_one (by norm_num [sourceDiscount] : 0 ≤ sourceDiscount)
      (by norm_num [sourceDiscount] : sourceDiscount≤1) hi
    exact not_le_of_gt h43 (hp.trans h)
  · intro h
    exact (pow_le_pow_of_le_one (by norm_num [sourceDiscount] : 0 ≤ sourceDiscount)
      (by norm_num [sourceDiscount] : sourceDiscount≤1) h).trans h44

theorem actual_source_discount_log_and_hundred_log_enclosures :
    (105360515/1000000000:ℝ)<Real.log (10/9) ∧
    Real.log (10/9)<105360516/1000000000 ∧
    (4605170185/1000000000:ℝ)<Real.log 100 ∧
    Real.log 100<4605170188/1000000000 := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0:ℝ)≤1/19)
    (by norm_num : (1/19:ℝ)<1) 4
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0:ℝ)≤1/19)
    (by norm_num : (1/19:ℝ)<1) 4
  norm_num [Finset.sum_range_succ] at hl hu
  have he : Real.log (100:ℝ)=2*(Real.log 2+Real.log 5) := by
    rw [show (100:ℝ)=(2*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  refine ⟨by linarith,by linarith,?_,?_⟩
  · rw [he];linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]
  · rw [he];linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]

theorem actual_source_exact_log_cutoff_rounds_to_forty_three_point_seven :
    (437/10:ℝ)<sourceExactCutoff ∧ sourceExactCutoff<4371/100 ∧
    |sourceExactCutoff-(437/10:ℝ)|<1/20 ∧
    sourceExactCutoff≠(437/10:ℝ) := by
  have hs := actual_source_discount_log_and_hundred_log_enclosures
  have hd : 0<Real.log (10/9:ℝ) := by linarith [hs.1]
  have he : sourceExactCutoff=Real.log 100/Real.log (10/9) := by
    unfold sourceExactCutoff sourceDiscount
    rw [show (1/100:ℝ)=(100:ℝ)⁻¹ by norm_num,Real.log_inv,
      show (9/10:ℝ)=(10/9:ℝ)⁻¹ by norm_num,Real.log_inv]
    ring
  have hl : (437/10:ℝ)<sourceExactCutoff := by
    rw [he,lt_div_iff₀ hd]
    linarith [hs.2.1,hs.2.2.1]
  have hu : sourceExactCutoff<(4371/100:ℝ) := by
    rw [he,div_lt_iff₀ hd]
    linarith [hs.1,hs.2.2.2]
  refine ⟨hl,hu,?_,ne_of_gt hl⟩
  rw [abs_lt];constructor <;>linarith

theorem actual_generic_conservative_log_budget_certifies_geometric_tolerance
    (gamma epsilon : ℝ) (hg0 : 0<gamma) (hg1 : gamma<1)
    (he0 : 0<epsilon) (T : ℕ)
    (hbudget : Real.log (1/epsilon)/(1-gamma)≤(T:ℝ)) :
    1-gamma≤Real.log (1/gamma) ∧ gamma^T≤epsilon := by
  have hl := Real.log_le_sub_one_of_pos hg0
  have hlog : 1-gamma≤Real.log (1/gamma) := by
    rw [one_div,Real.log_inv];linarith
  have hb : gamma≤Real.exp (-(1-gamma)) := by
    linarith [Real.add_one_le_exp (-(1-gamma))]
  have hp := pow_le_pow_left₀ hg0.le hb T
  rw [←Real.exp_nat_mul] at hp
  have hd : 0<1-gamma := by linarith
  have ht := (div_le_iff₀ hd).mp hbudget
  rw [one_div,Real.log_inv] at ht
  refine ⟨hlog,hp.trans ?_⟩
  calc
    Real.exp ((T:ℝ)*(-(1-gamma)))≤Real.exp (Real.log epsilon) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _=epsilon := Real.exp_log he0

theorem actual_source_conservative_log_budget_asks_for_forty_seven (T : ℕ) :
    (46:ℝ)<sourceCoarseCutoff ∧ sourceCoarseCutoff<47 ∧
    (sourceCoarseCutoff≤(T:ℝ) ↔ 47≤T) ∧
    (47≤T → sourceDiscount^T≤1/100) := by
  have hs := actual_source_discount_log_and_hundred_log_enclosures
  have hl : (46:ℝ)<sourceCoarseCutoff := by
    unfold sourceCoarseCutoff sourceDiscount
    norm_num
    linarith [hs.2.2.1]
  have hu : sourceCoarseCutoff<(47:ℝ) := by
    unfold sourceCoarseCutoff sourceDiscount
    norm_num
    linarith [hs.2.2.2]
  have hi : sourceCoarseCutoff≤(T:ℝ) ↔ 47≤T := by
    constructor
    · intro h
      by_contra hn
      have ht : T≤46 := by omega
      have hr : (T:ℝ)≤46 := by exact_mod_cast ht
      linarith
    · intro h
      have hr : (47:ℝ)≤T := by exact_mod_cast h
      exact hu.le.trans hr
  refine ⟨hl,hu,hi,?_⟩
  intro h
  apply (actual_generic_conservative_log_budget_certifies_geometric_tolerance
    sourceDiscount (1/100) (by norm_num [sourceDiscount])
      (by norm_num [sourceDiscount]) (by norm_num) T ?_).2
  simpa [sourceCoarseCutoff] using hi.mpr h

end SafeLearning.CompleteFoundationsGeometricExample
