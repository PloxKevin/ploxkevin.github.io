import SafeLearning.CompleteDualPILinearModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology
open SafeLearning.CompleteDualPILinearModel
namespace SafeLearning.CompleteDualPIAmplitude

theorem actual_pure_trajectory_energy_constant (gain : ℝ) (state : ℕ→ℝ×ℝ)
    (hrec : ∀ n,state (n+1)=((1-gain)*(state n).1-gain*(state n).2,
      (state n).2+(state n).1)) (n : ℕ) :
    oscillatorEnergy gain (state n).1 (state n).2=
      oscillatorEnergy gain (state 0).1 (state 0).2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hrec];simpa only [actual_pure_integral_energy_conserved] using ih

theorem actual_pure_trajectories_have_bounded_amplitudes
    (gain : ℝ) (hgain : 0<gain ∧ gain<4) (state : ℕ→ℝ×ℝ)
    (hrec : ∀ n,state (n+1)=((1-gain)*(state n).1-gain*(state n).2,
      (state n).2+(state n).1)) :
    ∃ bound : ℝ,0<bound ∧ ∀ n,(state n).1^2+(state n).2^2<bound := by
  let E := oscillatorEnergy gain (state 0).1 (state 0).2
  let A := gain*(1-gain/4)
  have hA : 0<A := mul_pos hgain.1 (by linarith)
  have hid (e delta : ℝ) : oscillatorEnergy gain e delta=(e+gain*delta/2)^2+A*delta^2 := by
    dsimp [oscillatorEnergy,A]
    ring
  have hE : 0≤E := by
    dsimp [E]
    rw [hid]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hA.le (sq_nonneg _))
  have hEA : 0≤E/A := div_nonneg hE hA.le
  refine ⟨2*E+(1+gain^2/2)*(E/A)+1,?_,?_⟩
  · have hm := mul_nonneg (by nlinarith [sq_nonneg gain] : 0≤1+gain^2/2) hEA
    linarith
  · intro n
    have hc := actual_pure_trajectory_energy_constant gain state hrec n
    change oscillatorEnergy gain (state n).1 (state n).2=E at hc
    rw [hid] at hc
    have hdelta : (state n).2^2≤E/A := by
      apply (le_div_iff₀ hA).mpr
      nlinarith [sq_nonneg ((state n).1+gain*(state n).2/2)]
    have hm := mul_le_mul_of_nonneg_left hdelta
      (by nlinarith [sq_nonneg gain] : 0≤1+gain^2/2)
    have hs : ((state n).1+gain*(state n).2/2)^2≤E := by
      nlinarith [mul_nonneg hA.le (sq_nonneg (state n).2)]
    nlinarith [sq_nonneg ((state n).1+gain*(state n).2)]

theorem actual_nonzero_pure_state_has_neither_coordinate_decay
    (gain : ℝ) (hgain : 0<gain ∧ gain<4) (state : ℕ→ℝ×ℝ)
    (hrec : ∀ n,state (n+1)=((1-gain)*(state n).1-gain*(state n).2,
      (state n).2+(state n).1)) (hnonzero : (state 0).1≠0 ∨ (state 0).2≠0) :
    ¬Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
      ¬Tendsto (fun n=>(state n).2) atTop (𝓝 0) := by
  have hnotboth : ¬(Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
      Tendsto (fun n=>(state n).2) atTop (𝓝 0)) := by
    rintro ⟨he,hd⟩
    have hp := actual_pure_integral_energy_positive gain (state 0).1 (state 0).2 hgain hnonzero
    have hl : Tendsto (fun n=>oscillatorEnergy gain (state n).1 (state n).2) atTop (𝓝 0) := by
      simpa [oscillatorEnergy] using ((he.pow 2).add ((he.const_mul gain).mul hd)).add
        ((hd.pow 2).const_mul gain)
    have heq : (fun n=>oscillatorEnergy gain (state n).1 (state n).2)=
        (fun _ : ℕ=>oscillatorEnergy gain (state 0).1 (state 0).2) := by
      funext n
      exact actual_pure_trajectory_energy_constant gain state hrec n
    rw [heq] at hl
    have hz : oscillatorEnergy gain (state 0).1 (state 0).2=0 :=
      tendsto_nhds_unique tendsto_const_nhds hl
    linarith
  constructor
  · intro he
    have hd : Tendsto (fun n=>(state n).2) atTop (𝓝 0) := by
      have hf := ((he.const_mul (1-gain)).sub (he.comp (tendsto_add_atTop_nat 1))).div_const gain
      have hid (n : ℕ) : ((1-gain)*(state n).1-(state (n+1)).1)/gain=(state n).2 := by
        rw [hrec]
        field_simp [hgain.1.ne']
        ring
      simpa only [Function.comp_def,hid,mul_zero,sub_self,zero_div] using hf
    exact hnotboth ⟨he,hd⟩
  · intro hd
    have he : Tendsto (fun n=>(state n).1) atTop (𝓝 0) := by
      have hf := (hd.comp (tendsto_add_atTop_nat 1)).sub hd
      have hid (n : ℕ) : (state (n+1)).2-(state n).2=(state n).1 := by
        rw [hrec]
        simp
      simpa only [Function.comp_def,hid,sub_self] using hf
    exact hnotboth ⟨he,hd⟩

end SafeLearning.CompleteDualPIAmplitude
