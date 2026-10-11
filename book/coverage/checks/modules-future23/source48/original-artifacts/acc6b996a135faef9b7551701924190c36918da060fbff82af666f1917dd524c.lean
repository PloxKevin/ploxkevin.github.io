import Mathlib

open Filter
open scoped Topology

namespace SafeLearning.CompleteModulesNNInvariantPractices22

noncomputable section

def localStep (x : ℝ) : ℝ := if |x| ≤ 1 then x / 2 else 2 * x
def localOrbit (x : ℝ) (n : ℕ) : ℝ := (localStep^[n]) x

theorem actual_energy_domain_iff (x : ℝ) : x ^ 2 ≤ 1 ↔ |x| ≤ 1 := by
  constructor
  · intro h
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x-1), sq_nonneg (x+1)]
  · intro h
    have hh := abs_le.mp h
    nlinarith [hh.1, hh.2]

theorem actual_local_one_step_energy_and_invariance (x : ℝ) (hx : x ^ 2 ≤ 1) :
    localStep x = x / 2 ∧ (localStep x) ^ 2 = x ^ 2 / 4 ∧
      (localStep x) ^ 2 ≤ 1 / 4 ∧ (localStep x) ^ 2 ≤ 1 := by
  have hd := (actual_energy_domain_iff x).mp hx
  rw [localStep, if_pos hd]
  constructor
  · rfl
  constructor
  · ring
  constructor <;> nlinarith

theorem actual_every_local_iterate_and_invariant_energy (x : ℝ) (hx : x ^ 2 ≤ 1)
    (n : ℕ) :
    localOrbit x n = (1 / 2 : ℝ) ^ n * x ∧ (localOrbit x n) ^ 2 ≤ 1 := by
  induction n with
  | zero => simp [localOrbit, hx]
  | succ n ih =>
    have hs := actual_local_one_step_energy_and_invariance (localOrbit x n) ih.2
    have hn : localOrbit x (n+1) = localStep (localOrbit x n) := by
      simp [localOrbit, Function.iterate_succ_apply']
    refine ⟨?_, by simpa only [hn] using hs.2.2.2⟩
    rw [hn, hs.1, ih.1, pow_succ]
    ring

theorem actual_local_energy_formula_and_convergence (x : ℝ) (hx : x ^ 2 ≤ 1) :
    (∀ n : ℕ, (localOrbit x n) ^ 2 = (1 / 4 : ℝ) ^ n * x ^ 2) ∧
      Tendsto (localOrbit x) atTop (𝓝 0) := by
  constructor
  · intro n
    rw [(actual_every_local_iterate_and_invariant_energy x hx n).1, mul_pow,
      ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  · have h : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [zero_mul] using (h.mul_const x).congr
      (fun n => (actual_every_local_iterate_and_invariant_energy x hx n).1.symm)

theorem actual_source_exterior_orbit (n : ℕ) :
    localOrbit (11 / 10) n = (11 / 10 : ℝ) * 2 ^ n ∧
      1 < localOrbit (11 / 10) n := by
  induction n with
  | zero => norm_num [localOrbit]
  | succ n ih =>
    have hn : localOrbit (11/10) (n+1) = localStep (localOrbit (11/10) n) := by
      simp [localOrbit, Function.iterate_succ_apply']
    have hd : ¬ |localOrbit (11/10) n| ≤ 1 := by
      intro h
      have hh := (abs_le.mp h).2
      linarith [ih.2]
    rw [hn, localStep, if_neg hd]
    constructor
    · rw [ih.1, pow_succ];ring
    · linarith [ih.2]

theorem actual_source_exterior_trajectory_diverges :
    Tendsto (localOrbit (11/10)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc := h.const_mul_atTop (show (0:ℝ)<11/10 by norm_num)
  exact hc.congr (fun n => (actual_source_exterior_orbit n).1.symm)

def disturbanceEnvelope (v0 : ℝ) (n : ℕ) : ℝ :=
  (1/2:ℝ)^n * v0 + (1/25:ℝ)*(1-(1/2:ℝ)^n)

theorem actual_disturbance_term_bound (d : ℝ) (hd : |d| ≤ 1/10) :
    2*d^2 ≤ 1/50 := by
  have hh := abs_le.mp hd
  nlinarith [sq_nonneg (d-1/10),sq_nonneg (d+1/10)]

theorem actual_finite_geometric_envelope_identity (v0 : ℝ) (n : ℕ) :
    disturbanceEnvelope v0 n = (1/2:ℝ)^n*v0+
      (1/50:ℝ)*∑ j ∈ Finset.range n, (1/2:ℝ)^j := by
  have h := geom_sum_mul_neg (1/2:ℝ) n
  unfold disturbanceEnvelope
  nlinarith

theorem actual_envelope_bounds_every_admitted_disturbance (v d : ℕ → ℝ)
    (hd : ∀ n, |d n| ≤ 1/10)
    (hrec : ∀ n, v (n+1) ≤ (1/2)*v n+2*(d n)^2) :
    ∀ n, v n ≤ disturbanceEnvelope (v 0) n := by
  intro n
  induction n with
  | zero => simp [disturbanceEnvelope]
  | succ n ih =>
    have hterm := actual_disturbance_term_bound (d n) (hd n)
    have hr := hrec n
    unfold disturbanceEnvelope at *
    rw [pow_succ]
    nlinarith

theorem actual_all_time_storage_invariance (v d : ℕ → ℝ)
    (h0 : v 0 ≤ 1/4) (hd : ∀ n, |d n| ≤ 1/10)
    (hrec : ∀ n, v (n+1) ≤ (1/2)*v n+2*(d n)^2) :
    ∀ n, v n ≤ 1/4 ∧ v (n+1) ≤ 29/200 := by
  have inv : ∀ n, v n ≤ 1/4 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hr := hrec n
      have ht := actual_disturbance_term_bound (d n) (hd n)
      linarith
  intro n
  refine ⟨inv n, ?_⟩
  have hr := hrec n
  have ht := actual_disturbance_term_bound (d n) (hd n)
  linarith [inv n]

theorem actual_envelope_tends_to_the_nonzero_storage_floor (v0 : ℝ) :
    Tendsto (disturbanceEnvelope v0) atTop (𝓝 (1/25:ℝ)) := by
  have h : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ho : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa [disturbanceEnvelope] using
    (h.mul_const v0).add ((ho.sub h).const_mul (1/25:ℝ))

theorem actual_state_norm_limit_superior_bound {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (d : ℕ → ℝ)
    (hd : ∀ n, |d n| ≤ 1/10)
    (hrec : ∀ n, ‖x (n+1)‖^2 ≤ (1/2)*‖x n‖^2+2*(d n)^2) :
    limsup (fun n => (‖x n‖ : EReal)) atTop ≤ (1/5:ℝ) := by
  have hb := actual_envelope_bounds_every_admitted_disturbance
    (fun n => ‖x n‖^2) d hd hrec
  have hlim := (actual_envelope_tends_to_the_nonzero_storage_floor (‖x 0‖^2)).sqrt
  have hs : Real.sqrt (1/25:ℝ) = 1/5 := by norm_num
  rw [hs] at hlim
  have he := EReal.tendsto_coe.mpr hlim
  rw [← he.limsup_eq]
  apply limsup_le_limsup (Eventually.of_forall fun n => ?_)
  apply EReal.coe_le_coe_iff.mpr
  exact Real.le_sqrt_of_sq_le (hb n)

theorem actual_energy_limit_superior_bound (v d : ℕ → ℝ)
    (hd : ∀ n, |d n| ≤ 1/10)
    (hrec : ∀ n, v (n+1) ≤ (1/2)*v n+2*(d n)^2) :
    limsup (fun n => (v n : EReal)) atTop ≤ (1/25:ℝ) := by
  have hb := actual_envelope_bounds_every_admitted_disturbance v d hd hrec
  have he := EReal.tendsto_coe.mpr (actual_envelope_tends_to_the_nonzero_storage_floor (v 0))
  rw [← he.limsup_eq]
  exact limsup_le_limsup (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hb n))

theorem actual_persistent_disturbance_can_prevent_convergence_to_zero :
    (∀ n : ℕ, |(1/10:ℝ)| ≤ 1/10 ∧
      (1/5:ℝ)^2 = (1/2)*(1/5:ℝ)^2+2*(1/10:ℝ)^2) ∧
      (1/5:ℝ)^2 ≤ 1/4 ∧ ¬ Tendsto (fun _ : ℕ => (1/5:ℝ)) atTop (𝓝 0) := by
  refine ⟨fun _ => by norm_num, by norm_num, ?_⟩
  intro h
  have hc : Tendsto (fun _ : ℕ => (1/5:ℝ)) atTop (𝓝 (1/5:ℝ)) := tendsto_const_nhds
  have := tendsto_nhds_unique hc h
  norm_num at this

end
end SafeLearning.CompleteModulesNNInvariantPractices22
