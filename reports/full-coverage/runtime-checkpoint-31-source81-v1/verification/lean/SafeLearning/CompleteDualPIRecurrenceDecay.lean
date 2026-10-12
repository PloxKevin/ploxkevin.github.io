import SafeLearning.CompleteDualPILinearModel

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped Topology
open SafeLearning.CompleteDualPILinearModel
namespace SafeLearning.CompleteDualPIRecurrenceDecay

theorem actual_quadratic_root_pair (trace determinant : ℝ) :
    ∃ r s : ℂ,r+s=(trace:ℂ) ∧ r*s=(determinant:ℂ) ∧
      characteristic trace determinant r=0 ∧ characteristic trace determinant s=0 := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq
    ((trace:ℂ)^2-4*(determinant:ℂ)) (by norm_num : 0<(2:ℕ))
  refine ⟨((trace:ℂ)+w)/2,((trace:ℂ)-w)/2,?_,?_,?_,?_⟩
  · ring
  · linear_combination -hw/4
  · unfold characteristic
    linear_combination hw/4
  · unfold characteristic
    linear_combination hw/4

theorem every_complex_factored_recurrence_decays (r s : ℂ)
    (hr : ‖r‖<1) (hs : ‖s‖<1) (x : ℕ→ℂ)
    (hrec : ∀ n,x (n+2)=(r+s)*x (n+1)-r*s*x n) :
    Tendsto x atTop (𝓝 0) := by
  let y : ℕ→ℂ := fun n=>x (n+1)-r*x n
  have hyrec (n : ℕ) : y (n+1)=s*y n := by
    dsimp [y]
    rw [show n+1+1=n+2 by omega,hrec]
    ring
  have hyformula (n : ℕ) : y n=s^n*y 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [hyrec,ih,pow_succ];ring
  let R : ℝ := max ‖r‖ ‖s‖
  have hR0 : 0≤R := (norm_nonneg r).trans (le_max_left _ _)
  have hR1 : R<1 := max_lt hr hs
  have hrR : ‖r‖≤R := le_max_left _ _
  have hsR : ‖s‖≤R := le_max_right _ _
  have hynorm (n : ℕ) : ‖y n‖≤R^n*‖y 0‖ := by
    rw [hyformula,norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg s) hsR n) (norm_nonneg _)
  have hxstep (n : ℕ) : ‖x (n+1)‖≤R*‖x n‖+R^n*‖y 0‖ := by
    have hid : x (n+1)=r*x n+y n := by dsimp [y];ring
    rw [hid]
    calc
      ‖r*x n+y n‖≤‖r*x n‖+‖y n‖ := norm_add_le _ _
      _ ≤ R*‖x n‖+R^n*‖y 0‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hrR (norm_nonneg _)) (hynorm n)
  have hbound (n : ℕ) : ‖x (n+1)‖≤R^(n+1)*‖x 0‖+((n:ℝ)+1)*R^n*‖y 0‖ := by
    induction n with
    | zero => simpa using hxstep 0
    | succ n ih =>
      have hh := hxstep (n+1)
      have hm := mul_le_mul_of_nonneg_left ih hR0
      simp only [Nat.cast_add,Nat.cast_one,pow_succ] at hh hm ⊢
      nlinarith
  have hpow : Tendsto (fun n : ℕ=>R^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1
  have hnpow : Tendsto (fun n : ℕ=>(n:ℝ)*R^n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hR0 hR1
  have hupper : Tendsto (fun n : ℕ=>R^(n+1)*‖x 0‖+((n:ℝ)+1)*R^n*‖y 0‖) atTop (𝓝 0) := by
    have h1 := (hpow.mul_const R).mul_const ‖x 0‖
    have h2 := (hnpow.add hpow).mul_const ‖y 0‖
    convert h1.add h2 using 1
    · funext n
      rw [pow_succ]
      ring
    · simp
  have hnorm : Tendsto (fun n : ℕ=>‖x (n+1)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n=>norm_nonneg _) hbound hupper
  have hshift : Tendsto (fun n : ℕ=>x (n+1)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

theorem every_quadratic_recurrence_with_stable_roots_decays
    (trace determinant : ℝ)
    (hstable : ∀ z : ℂ,characteristic trace determinant z=0 → ‖z‖<1)
    (x : ℕ→ℂ) (hrec : ∀ n,x (n+2)=(trace:ℂ)*x (n+1)-(determinant:ℂ)*x n) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨r,s,hsum,hprod,hr,hs⟩ := actual_quadratic_root_pair trace determinant
  apply every_complex_factored_recurrence_decays r s (hstable r hr) (hstable s hs) x
  simpa [hsum,hprod] using hrec

theorem actual_every_control_loop_coordinate_decays_when_roots_stable
    (a c kp ki : ℝ)
    (hstable : ∀ z : ℂ,characteristic (1+a-c*(kp+ki)) (a-c*kp) z=0 → ‖z‖<1)
    (state : ℕ→ℝ×ℝ)
    (hloop : ∀ n,state (n+1)=loopStep a c kp ki (state n).1 (state n).2) :
    Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
      Tendsto (fun n=>(state n).2) atTop (𝓝 0) := by
  have hreal (n : ℕ) : (state (n+2)).2=
      (1+a-c*(kp+ki))*(state (n+1)).2-(a-c*kp)*(state n).2 := by
    rw [show n+2=n+1+1 by omega,hloop (n+1),hloop n]
    simp [loopStep]
    ring
  have hc : Tendsto (fun n=>((state n).2:ℂ)) atTop (𝓝 0) := by
    apply every_quadratic_recurrence_with_stable_roots_decays _ _ hstable
    intro n
    exact_mod_cast hreal n
  have hd : Tendsto (fun n=>(state n).2) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
      (Complex.continuous_re.tendsto 0).comp hc
  have hdelta (n : ℕ) : (state n).1=(state (n+1)).2-(state n).2 := by
    rw [hloop]
    simp [loopStep]
  have he := (hd.comp (tendsto_add_atTop_nat 1)).sub hd
  refine ⟨?_,hd⟩
  simpa only [Function.comp_def,sub_self,hdelta] using he

end SafeLearning.CompleteDualPIRecurrenceDecay
