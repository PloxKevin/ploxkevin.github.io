import Mathlib

set_option autoImplicit false

/-! Model-level proofs for the packing-machine application in Primer E.
`readyProbability` is the distribution of the stated two-state Markov chain,
started ready. Production and maintenance are expected discounted sums, not
uninterpreted solutions of Bellman equations. -/
noncomputable section
namespace SafeLearning.CompleteAppliedPolicy
open Filter
open scoped Topology

def readyProbability (wear : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => 1-wear*readyProbability wear n

theorem readyProbability_is_probability (wear : ℝ) (hw : wear ∈ Set.Icc 0 1) :
    ∀ n, readyProbability wear n ∈ Set.Icc 0 1 := by
  intro n
  induction n with
  | zero => norm_num [readyProbability]
  | succ n ih =>
    simp only [readyProbability, Set.mem_Icc] at *
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ih.2 hw.1]
    · nlinarith [mul_nonneg hw.1 ih.1]

/-- The update adds the disjoint R→R and W→R paths of the specified chain. -/
theorem readyProbability_transition (wear : ℝ) (n : ℕ) :
    readyProbability wear (n+1)=
      readyProbability wear n*(1-wear)+(1-readyProbability wear n)*1 := by
  simp only [readyProbability]; ring

theorem readyProbability_closed (wear : ℝ) (hw : 0 ≤ wear) (n : ℕ) :
    readyProbability wear n=1/(1+wear)+wear/(1+wear)*(-wear)^n := by
  have hd : 1+wear ≠ 0 := by positivity
  induction n with
  | zero => simp [readyProbability]; field_simp
  | succ n ih =>
    rw [readyProbability, ih, pow_succ]
    field_simp
    ring

theorem geometric_discounted_probability (wear : ℝ) (hw : 0 ≤ wear)
    (hw1 : wear ≤ 1) (n : ℕ) :
    (4/5:ℝ)^n*readyProbability wear n=
      (1/(1+wear))*(4/5:ℝ)^n+
      (wear/(1+wear))*(-(4/5)*wear)^n := by
  rw [readyProbability_closed wear hw n, mul_add]
  have hm : (-(4/5:ℝ)*wear)^n=(4/5:ℝ)^n*(-wear)^n := by rw [← mul_pow]; congr 1; ring
  rw [hm]
  ring

theorem wear_discount_small (wear : ℝ) (hw : wear ∈ Set.Icc 0 1) :
    |-(4/5:ℝ)*wear|<1 := by
  rw [abs_mul, abs_of_nonneg hw.1]
  norm_num
  linarith [hw.2]

theorem discounted_ready_summable (wear : ℝ) (hw : wear ∈ Set.Icc 0 1) :
    Summable (fun n => (4/5:ℝ)^n*readyProbability wear n) := by
  have h1 := (summable_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1)).mul_left
    (1/(1+wear))
  have h2 := (summable_geometric_of_abs_lt_one (wear_discount_small wear hw)).mul_left
    (wear/(1+wear))
  exact (h1.add h2).congr fun n => (geometric_discounted_probability wear hw.1 hw.2 n).symm

theorem discounted_ready_sum (wear : ℝ) (hw : wear ∈ Set.Icc 0 1) :
    (∑' n : ℕ, (4/5:ℝ)^n*readyProbability wear n)=5/(1+(4/5)*wear) := by
  have h1 := (summable_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1)).mul_left
    (1/(1+wear))
  have h2 := (summable_geometric_of_abs_lt_one (wear_discount_small wear hw)).mul_left
    (wear/(1+wear))
  simp_rw [geometric_discounted_probability wear hw.1 hw.2]
  rw [h1.tsum_add h2, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1),
    tsum_geometric_of_abs_lt_one (wear_discount_small wear hw)]
  have hw0 := hw.1
  have hd : 1+wear ≠ 0 := by positivity
  have he : 1+(4/5)*wear ≠ 0 := by positivity
  have h5 : 5+wear*4 ≠ 0 := by positivity
  field_simp
  ring_nf
  field_simp [h5]
  ring

def productionReturn (p rho : ℝ) : ℝ :=
  ∑' n : ℕ, (4/5:ℝ)^n*((2+2*p)*readyProbability (rho*p) n)

def maintenanceReturn (p rho : ℝ) : ℝ :=
  ∑' n : ℕ, (4/5:ℝ)^n*(1-readyProbability (rho*p) n)

theorem productionReturn_formula (p rho : ℝ)
    (hw : rho*p ∈ Set.Icc 0 1) :
    productionReturn p rho=(2+2*p)/(1/5+(4/25)*rho*p) := by
  unfold productionReturn
  simp_rw [show ∀ n : ℕ, (4/5:ℝ)^n*((2+2*p)*readyProbability (rho*p) n)=
    (2+2*p)*((4/5:ℝ)^n*readyProbability (rho*p) n) by intro n; ring]
  rw [tsum_mul_left, discounted_ready_sum (rho*p) hw]
  have hw0 := hw.1
  have hd : 1+(4/5)*(rho*p) ≠ 0 := by positivity
  have he : 1/5+(4/25)*rho*p ≠ 0 := by nlinarith [hw.1]
  have h5 : 5+p*rho*4 ≠ 0 := by nlinarith [hw0]
  have h25 : 25+p*rho*20 ≠ 0 := by nlinarith [hw0]
  field_simp
  ring_nf
  field_simp [h5,h25]
  ring

theorem maintenanceReturn_formula (p rho : ℝ)
    (hw : rho*p ∈ Set.Icc 0 1) :
    maintenanceReturn p rho=((4/5)*rho*p)/(1/5+(4/25)*rho*p) := by
  unfold maintenanceReturn
  simp_rw [mul_sub, mul_one]
  rw [(summable_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1)).tsum_sub
    (discounted_ready_summable (rho*p) hw),
    tsum_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1),
    discounted_ready_sum (rho*p) hw]
  have hw0 := hw.1
  have hd : 1+(4/5)*(rho*p) ≠ 0 := by positivity
  have he : 1/5+(4/25)*rho*p ≠ 0 := by nlinarith [hw.1]
  have h5 : 5+rho*p*4 ≠ 0 := by nlinarith [hw0]
  have h25 : 25+rho*p*20 ≠ 0 := by nlinarith [hw0]
  field_simp
  ring_nf
  field_simp [h5,h25]
  ring

def J (p : ℝ) : ℝ := (2+2*p)/(1/5+p/25)
def C (p : ℝ) : ℝ := p/(1+p/5)

theorem nominal_production_semantics (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    productionReturn p (1/4)=J p := by
  rw [productionReturn_formula p (1/4) (by constructor <;> nlinarith [hp.1,hp.2])]
  unfold J
  congr 1 <;> ring

theorem nominal_maintenance_semantics (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    maintenanceReturn p (1/4)=C p := by
  rw [maintenanceReturn_formula p (1/4) (by constructor <;> nlinarith [hp.1,hp.2])]
  unfold C
  have hp0 := hp.1
  have hd : 1+p/5 ≠ 0 := by positivity
  have he : 1/5+(4/25)*(1/4)*p ≠ 0 := by nlinarith [hp.1]
  field_simp
  ring

theorem nominal_reward_bellman (p : ℝ) (hp : 0≤p) :
    J p=2+2*p+(4/5)*((1-p/4)*J p+(p/4)*((4/5)*J p)) := by
  unfold J
  have hd : (1/5:ℝ)+p/25≠0 := by positivity
  field_simp
  ring

theorem nominal_cost_bellman (p : ℝ) (hp : 0≤p) :
    C p=(4/5)*((1-p/4)*C p+(p/4)*(1+(4/5)*C p)) := by
  unfold C
  have hd : (1:ℝ)+p/5≠0 := by positivity
  field_simp
  ring

theorem reward_bellman_coefficient (p VR : ℝ) :
    (4/5)*((1-p/4)*VR+(p/4)*((4/5)*VR))=(4/5-p/25)*VR := by ring

theorem immediate_policy_reward (p : ℝ) : 2*(1-p)+4*p=2+2*p := by ring

theorem J_strictMono : StrictMonoOn J (Set.Icc 0 1) := by
  intro p hp q hq hpq
  unfold J
  apply (div_lt_div_iff₀ (by nlinarith [hp.1] : 0<(1/5:ℝ)+p/25)
    (by nlinarith [hq.1] : 0<(1/5:ℝ)+q/25)).2
  nlinarith

theorem J_derivative (p : ℝ) (hp : 0≤p) :
    HasDerivAt J ((8/25)/(1/5+p/25)^2) p := by
  have hd : (1/5:ℝ)+p/25≠0 := by positivity
  have hh := ((hasDerivAt_const p (2:ℝ)).add ((hasDerivAt_id p).const_mul 2)).div
    ((hasDerivAt_const p (1/5:ℝ)).add ((hasDerivAt_id p).div_const 25)) hd
  convert hh using 1 <;> (try ext q) <;>
    simp only [J,Pi.add_apply,Pi.div_apply,id_eq] <;> field_simp <;> ring

theorem wear_cost_derivative (z : ℝ) (hz : 0≤z) :
    HasDerivAt (fun a : ℝ => ((4/5)*a)/(1/5+(4/25)*a))
      ((4/25)/(1/5+(4/25)*z)^2) z := by
  have hd : (1/5:ℝ)+(4/25)*z≠0 := by positivity
  have hh := ((hasDerivAt_id z).const_mul (4/5:ℝ)).div
    ((hasDerivAt_const z (1/5:ℝ)).add ((hasDerivAt_id z).const_mul (4/25:ℝ))) hd
  convert hh using 1 <;> (try ext q) <;>
    simp only [Pi.add_apply,Pi.div_apply,id_eq] <;> field_simp <;> ring

theorem half_budget (p : ℝ) (hp : 0 ≤ p) : C p ≤ 1/2 ↔ p ≤ 5/9 := by
  unfold C
  rw [div_le_iff₀ (by positivity : 0<(1:ℝ)+p/5)]
  constructor <;> intro h <;> linarith

theorem quarter_budget (p : ℝ) (hp : 0 ≤ p) : C p ≤ 1/4 ↔ p ≤ 5/19 := by
  unfold C
  rw [div_le_iff₀ (by positivity : 0<(1:ℝ)+p/5)]
  constructor <;> intro h <;> linarith

theorem nominal_optimal (p : ℝ) (hp : p ∈ Set.Icc 0 1) (hc : C p ≤ 1/2) :
    J p ≤ J (5/9) := by
  exact J_strictMono.monotoneOn hp (by norm_num) ((half_budget p hp.1).1 hc)

theorem tightened_optimal (p : ℝ) (hp : p ∈ Set.Icc 0 1) (hc : C p ≤ 1/4) :
    J p ≤ J (5/19) := by
  exact J_strictMono.monotoneOn hp (by norm_num) ((quarter_budget p hp.1).1 hc)

theorem policy_values :
    C (5/9)=1/2 ∧ J (5/9)=14 ∧ C (5/19)=1/4 ∧ J (5/19)=12 ∧
    J 0=10 ∧ J 1=50/3 ∧ C 1=5/6 ∧
    C (2/5)=10/27 ∧ J (2/5)=350/27 ∧ C (4/5)=20/29 ∧
    C (2/5)<1/2 ∧ 1/2<C (4/5) := by norm_num [C,J]

theorem robust_budget_equivalence (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∀ rho ∈ Set.Icc (1/5:ℝ) (3/10), maintenanceReturn p rho ≤ 1/2) ↔
      p ≤ 25/54 := by
  have hformula : ∀ rho ∈ Set.Icc (1/5:ℝ) (3/10),
      maintenanceReturn p rho ≤ 1/2 ↔ (18/25:ℝ)*rho*p ≤ 1/10 := by
    intro rho hr
    have hprod : rho*p ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact mul_nonneg (by linarith [hr.1]) hp.1
      · have hh := mul_le_mul_of_nonneg_left hp.2 (by linarith [hr.1] : 0≤rho)
        nlinarith [hr.2]
    rw [maintenanceReturn_formula p rho hprod,
      div_le_iff₀ (by nlinarith [hprod.1] : 0<(1/5:ℝ)+(4/25)*rho*p)]
    constructor <;> intro h <;> nlinarith
  constructor
  · intro h
    have hh := (hformula (3/10) (by norm_num)).1 (h (3/10) (by norm_num))
    linarith
  · intro h rho hr
    apply (hformula rho hr).2
    nlinarith [mul_le_mul_of_nonneg_right hr.2 hp.1]

theorem robust_half_fails : maintenanceReturn (1/2) (3/10)=15/28 ∧
    1/2 < maintenanceReturn (1/2) (3/10) := by
  rw [maintenanceReturn_formula (1/2) (3/10) (by norm_num)]
  norm_num

theorem stationary_balance_unique (w : ℝ) :
    w=(1-w)*(5/36) ↔ w=5/41 := by constructor <;> intro h <;> linarith

theorem stationary_values :
    (36/41:ℝ)*(1-5/36)+5/41=36/41 ∧
    (36/41:ℝ)*(5/36)=5/41 ∧
    (36/41:ℝ)*(2+2*(5/9))=112/41 ∧
    (20:ℝ)*(5/41)=100/41 ∧ (1/2:ℝ) ≠ 100/41 := by norm_num

end SafeLearning.CompleteAppliedPolicy
