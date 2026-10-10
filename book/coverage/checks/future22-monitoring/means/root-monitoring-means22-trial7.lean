import SafeLearning.CompleteFiniteMarkovPathCorrespondence
import SafeLearning.CompleteMonitoringGeometry21

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteFiniteCMDPOccupancy

/-- The fixed source monitoring MDP, starting at R0. -/
def model : Model (Fin 3) Bool where
  initial s := if s=0 then 1 else 0
  initial_nonneg s := by split_ifs <;> norm_num
  initial_sum := by simp
  transition s a t := if t=(if s=0 then (if a then 2 else 1) else (if a then s else 0)) then 1 else 0
  transition_nonneg s a t := by split_ifs <;> norm_num
  transition_sum s a := by simp

/-- At R0 choose R1 with probability q; at either region return with probability b. -/
def policy (q b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Policy (Fin 3) Bool where
  action _ s a := if s=0 then (if a then 1-q else q) else (if a then 1-b else b)
  action_nonneg _ s a := by cases a <;> split_ifs <;> linarith
  action_sum _ s := by by_cases h : s=0 <;> simp [h,Fintype.sum_bool]

variable (q b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
local notation "mass" => stateMass model (policy q b hq0 hq1 hb0 hb1)

theorem actual_source_chain_marginal_recurrences (n : ℕ) :
    mass (n+1) 0 = b*(mass n 1+mass n 2) ∧
    mass (n+1) 1 = q*mass n 0+(1-b)*mass n 1 ∧
    mass (n+1) 2 = (1-q)*mass n 0+(1-b)*mass n 2 := by
  simp [stateMass,model,policy,Fin.sum_univ_succ,Fintype.sum_bool]
  constructor; ring
  constructor <;> ring

theorem actual_source_chain_closed_marginals (n : ℕ) :
    mass n 0 = (b+(-b)^n)/(1+b) ∧
    mass n 1 = q*(1-(b+(-b)^n)/(1+b)) ∧
    mass n 2 = (1-q)*(1-(b+(-b)^n)/(1+b)) := by
  have hden : 1+b ≠ 0 := by linarith
  induction n with
  | zero =>
    have hr : (b+1)/(1+b) = 1 := by field_simp [hden];ring
    simp [stateMass,model,hr]
  | succ n ih =>
    obtain ⟨ha,hb,hc⟩ := actual_source_chain_marginal_recurrences q b hq0 hq1 hb0 hb1 n
    simp only [ih.1,ih.2.1,ih.2.2] at ha hb hc
    rw [ha,hb,hc,pow_succ]
    constructor
    · field_simp [hden] <;> ring
    constructor <;> (field_simp;ring)

def averageState (N : ℕ) (s : Fin 3) : ℝ := (∑ n ∈ Finset.range N, mass n s)/(N:ℝ)

theorem actual_average_zero_state_formula (N : ℕ) (hN : N ≠ 0) :
    averageState q b hq0 hq1 hb0 hb1 N 0 =
      b/(1+b) + (∑ n ∈ Finset.range N, (-b)^n)/((1+b)*(N:ℝ)) := by
  have hden : 1+b ≠ 0 := by linarith
  have hcast : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  have hm : ∀ n, mass n 0 = (b+(-b)^n)/(1+b) := fun n => (actual_source_chain_closed_marginals q b hq0 hq1 hb0 hb1 n).1
  simp_rw [averageState,hm]
  rw [← Finset.sum_div,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp [hden,hcast] <;> ring

include hb0 hb1 in
theorem actual_geometric_partial_sum_uniform_bound (N : ℕ) :
    |∑ n ∈ Finset.range N, (-b)^n| ≤ 2 := by
  have hnorm : |(-b)^N| ≤ 1 := by
    rw [abs_pow,abs_neg,abs_of_nonneg hb0]
    exact pow_le_one₀ hb0 hb1
  have hn : -b ≠ 1 := by linarith
  have he:=geom_sum_eq hn N
  have hden : 0 < 1+b := by linarith
  have hid : (∑ n ∈ Finset.range N, (-b)^n)*(1+b)=1-(-b)^N := by
    rw [he];field_simp;ring
  have hprod : |∑ n ∈ Finset.range N, (-b)^n| * (1+b) ≤ 2 := by
    rw [← abs_of_pos hden,← abs_mul,hid]
    calc |1-(-b)^N| ≤ |(1:ℝ)|+|(-b)^N| := abs_sub _ _
      _ ≤ 2 := by norm_num at *;linarith
  have hnonneg:=abs_nonneg (∑ n ∈ Finset.range N, (-b)^n)
  nlinarith

theorem actual_expected_zero_state_fraction_limit :
    Tendsto (fun N => averageState q b hq0 hq1 hb0 hb1 N 0) atTop (𝓝 (b/(1+b))) := by
  have hden : 0 < 1+b := by linarith
  have herror : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (-b)^n)/((1+b)*(N:ℝ))) atTop (𝓝 0) := by
    have hbound : ∀ N : ℕ, |(∑ n ∈ Finset.range N, (-b)^n)/((1+b)*(N:ℝ))| ≤ 2/(N:ℝ) := by
      intro N;by_cases hN : N=0
      · simp [hN]
      have hpos : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
      rw [abs_div,abs_of_pos (mul_pos hden hpos)]
      apply (div_le_div_iff₀ (mul_pos hden hpos) hpos).mpr
      have hh:=actual_geometric_partial_sum_uniform_bound b hb0 hb1 N
      nlinarith
    apply squeeze_zero_norm (fun N => hbound N) (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ))
  have hconst : Tendsto (fun _ : ℕ => b/(1+b)) atTop (𝓝 (b/(1+b))) := tendsto_const_nhds
  have hfinal := hconst.add herror
  simp only [add_zero] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
  exact (actual_average_zero_state_formula q b hq0 hq1 hb0 hb1 N hN).symm

private theorem average_of_proportional_complement (N : ℕ) (hN : N ≠ 0)
    (s : Fin 3) (x : ℝ) (hx : ∀ n, mass n s = x*(1-mass n 0)) :
    averageState q b hq0 hq1 hb0 hb1 N s = x*(1-averageState q b hq0 hq1 hb0 hb1 N 0) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  have hs : (∑ n ∈ Finset.range N, mass n s) = x*((N:ℝ)-(∑ n ∈ Finset.range N, mass n 0)) := by
    simp_rw [hx,mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  unfold averageState
  rw [hs]
  field_simp [hn] <;> ring

theorem actual_other_state_average_formulas (N : ℕ) (hN : N ≠ 0) :
    averageState q b hq0 hq1 hb0 hb1 N 1 = q*(1-averageState q b hq0 hq1 hb0 hb1 N 0) ∧
    averageState q b hq0 hq1 hb0 hb1 N 2 = (1-q)*(1-averageState q b hq0 hq1 hb0 hb1 N 0) := by
  constructor
  · apply average_of_proportional_complement q b hq0 hq1 hb0 hb1 N hN 1 q
    intro n;obtain ⟨h0,h1,h2⟩:=actual_source_chain_closed_marginals q b hq0 hq1 hb0 hb1 n
    rw [h1,h0]
  · apply average_of_proportional_complement q b hq0 hq1 hb0 hb1 N hN 2 (1-q)
    intro n;obtain ⟨h0,h1,h2⟩:=actual_source_chain_closed_marginals q b hq0 hq1 hb0 hb1 n
    rw [h2,h0]

theorem actual_expected_first_region_fraction_limit :
    Tendsto (fun N => averageState q b hq0 hq1 hb0 hb1 N 1) atTop (𝓝 (q/(1+b))) := by
  have hd : 1+b ≠ 0 := by linarith
  have hz:=actual_expected_zero_state_fraction_limit q b hq0 hq1 hb0 hb1
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he : q*(1-b/(1+b))=q/(1+b) := by field_simp [hd];ring
  have hl:=(hone.sub hz).const_mul q
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
  exact (actual_other_state_average_formulas q b hq0 hq1 hb0 hb1 N hN).1.symm

theorem actual_expected_second_region_fraction_limit :
    Tendsto (fun N => averageState q b hq0 hq1 hb0 hb1 N 2) atTop (𝓝 ((1-q)/(1+b))) := by
  have hd : 1+b ≠ 0 := by linarith
  have hz:=actual_expected_zero_state_fraction_limit q b hq0 hq1 hb0 hb1
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he : (1-q)*(1-b/(1+b))=(1-q)/(1+b) := by field_simp [hd];ring
  have hl:=(hone.sub hz).const_mul (1-q)
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
  exact (actual_other_state_average_formulas q b hq0 hq1 hb0 hb1 N hN).2.symm

open SafeLearning.CompleteMonitoringGeometry21

theorem actual_every_source_polytope_fraction_has_a_markov_average_realization
    (v : Fractions) (hv : AchievablePolytope v) :
    ∃ (q' b' : ℝ) (hq'0 : 0 ≤ q') (hq'1 : q' ≤ 1) (hb'0 : 0 ≤ b') (hb'1 : b' ≤ 1),
      Tendsto (fun N => averageState q' b' hq'0 hq'1 hb'0 hb'1 N 0) atTop (𝓝 v.v0) ∧
      Tendsto (fun N => averageState q' b' hq'0 hq'1 hb'0 hb'1 N 1) atTop (𝓝 v.v1) ∧
      Tendsto (fun N => averageState q' b' hq'0 hq'1 hb'0 hb'1 N 2) atTop (𝓝 v.v2) := by
  obtain ⟨h0,h1,h2,hs,hh⟩:=hv
  have hd : 0 < 1-v.v0 := by linarith
  let q' := v.v1/(1-v.v0)
  let b' := v.v0/(1-v.v0)
  have hq'0 : 0 ≤ q' := div_nonneg h1 hd.le
  have hq'1 : q' ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hb'0 : 0 ≤ b' := div_nonneg h0 hd.le
  have hb'1 : b' ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hr0 : b'/(1+b')=v.v0 := by dsimp [b'];field_simp [ne_of_gt hd] <;> ring
  have hr1 : q'/(1+b')=v.v1 := by dsimp [q',b'];field_simp [ne_of_gt hd] <;> ring
  have hr2 : (1-q')/(1+b')=v.v2 := by dsimp [q',b'];field_simp [ne_of_gt hd] <;> nlinarith
  refine ⟨q',b',hq'0,hq'1,hb'0,hb'1,?_,?_,?_⟩
  · simpa only [hr0] using actual_expected_zero_state_fraction_limit q' b' hq'0 hq'1 hb'0 hb'1
  · simpa only [hr1] using actual_expected_first_region_fraction_limit q' b' hq'0 hq'1 hb'0 hb'1
  · simpa only [hr2] using actual_expected_second_region_fraction_limit q' b' hq'0 hq'1 hb'0 hb'1

theorem actual_fair_coin_policy_has_all_three_expected_fractions_one_third :
    Tendsto (fun N => averageState (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 0) atTop (𝓝 (1/3)) ∧
    Tendsto (fun N => averageState (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 1) atTop (𝓝 (1/3)) ∧
    Tendsto (fun N => averageState (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 2) atTop (𝓝 (1/3)) := by
  constructor
  · convert actual_expected_zero_state_fraction_limit (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  constructor
  · convert actual_expected_first_region_fraction_limit (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert actual_expected_second_region_fraction_limit (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

end SafeLearning.CompleteMonitoringMeans22
