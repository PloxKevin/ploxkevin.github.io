import SafeLearning.CompleteAppliedSystems
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDynamics
open SafeLearning.CompleteAppliedSystems

theorem thermalA_precise : (778800783071/1000000000000:ℝ) ≤ thermalA ∧
    thermalA ≤ 778800783072/1000000000000 := by
  have h := Real.exp_bound (x := -(1/4:ℝ)) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hh := abs_le.mp h
  unfold thermalA
  constructor <;> linarith

theorem thermal_rounded_coefficients :
    |thermalA-(778801/1000000:ℝ)| ≤ 1/2000000 ∧
    |thermalB-(884797/1000000:ℝ)| ≤ 1/2000000 ∧
    |thermalQ-(336402/1000000:ℝ)| ≤ 1/2000000 ∧
    |thermalQ^2-(113167/1000000:ℝ)| ≤ 1/2000000 := by
  obtain ⟨hl,hu⟩ := thermalA_precise
  have hql : (336402349213/1000000000000:ℝ) ≤ thermalQ := by
    unfold thermalQ thermalB; linarith
  have hqu : thermalQ ≤ (336402349216/1000000000000:ℝ) := by
    unfold thermalQ thermalB; linarith
  constructor
  · rw [abs_le]; constructor <;> linarith
  constructor
  · rw [abs_le]; unfold thermalB; constructor <;> linarith
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (thermalQ-(336402349213/1000000000000:ℝ)),
      sq_nonneg (thermalQ-(336402349216/1000000000000:ℝ)),
      mul_self_le_mul_self (by norm_num : 0 ≤ (336402349213/1000000000000:ℝ)) hql,
      mul_self_le_mul_self thermal_coefficients.2.2.2.1.le hqu]

theorem thermal_displayed_readings :
    |thermalQ*(-2)+(672805/1000000:ℝ)| ≤ 1/2000000 ∧
    |thermalQ^2*(-2)+(226333/1000000:ℝ)| ≤ 1/2000000 ∧
    |22+thermalQ*(-2)-(213272/10000:ℝ)| ≤ 1/20000 ∧
    |22+thermalQ^2*(-2)-(217737/10000:ℝ)| ≤ 1/20000 ∧
    |1+thermalQ-(1336402/1000000:ℝ)| ≤ 1/2000000 ∧
    (20:ℝ)-22 = -2 ∧ 1-(-2:ℝ)/2=2 ∧ (2:ℝ)*5=10 := by
  obtain ⟨hl,hu⟩ := thermalA_precise
  have hql : (336402349213/1000000000000:ℝ) ≤ thermalQ := by
    unfold thermalQ thermalB; linarith
  have hqu : thermalQ ≤ (336402349216/1000000000000:ℝ) := by
    unfold thermalQ thermalB; linarith
  have hsql := mul_self_le_mul_self (by norm_num : 0 ≤ (336402349213/1000000000000:ℝ)) hql
  have hsqu := mul_self_le_mul_self thermal_coefficients.2.2.2.1.le hqu
  refine ⟨?_,?_,?_,?_,?_,by norm_num,by norm_num,by norm_num⟩ <;>
    rw [abs_le] <;> constructor <;> nlinarith

theorem thermal_gain_rounding :
    |(thermalA-1/2)/thermalB-(315101/1000000:ℝ)| ≤ 1/2000000 := by
  obtain ⟨hl,hu⟩ := thermalA_precise
  have hb := thermal_coefficients.2.2.1
  rw [abs_le]
  constructor
  · have hh : (630201/2000000:ℝ) ≤ (thermalA-1/2)/thermalB := by
      rw [le_div_iff₀ hb]; unfold thermalB; linarith
    linarith
  · have hh : (thermalA-1/2)/thermalB ≤ (630203/2000000:ℝ) := by
      rw [div_le_iff₀ hb]; unfold thermalB; linarith
    linarith

theorem clipped_first_update :
    saturatedDeviation (-2)=1 ∧ (1:ℝ)-(-2)=3 ∧
    thermalA*(-2)+thermalB*saturatedDeviation (-2)=thermalQ*(-2) ∧
    |(thermalA-thermalB)*(-2)-(211992/1000000:ℝ)| ≤ 1/2000000 := by
  obtain ⟨hl,hu⟩ := thermalA_precise
  refine ⟨by norm_num [saturatedDeviation],by norm_num,?_,?_⟩
  · norm_num [saturatedDeviation,thermalQ]; ring
  · rw [abs_le]; unfold thermalB; constructor <;> linarith

theorem saturated_invariant_all (x : ℕ → ℝ)
    (hstep : ∀ n, x (n+1)=thermalA*x n+thermalB*saturatedDeviation (x n))
    (h0 : |x 0| ≤ 2) : ∀ n, |x n| ≤ 2 := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih => rw [hstep]; exact saturated_map_invariant _ ih

theorem first_qualifying_reading (n : ℕ) (hn : n < 2) :
    (3/10:ℝ) < |thermalQ^n*(-2)| := by
  have hh := deadline_readings
  have hc : n=0 ∨ n=1 := by omega
  rcases hc with rfl | rfl
  · simpa using hh.1
  · simpa using hh.2.1

theorem saturated_branches (x : ℝ) :
    (x ≤ -1 → thermalA*x+thermalB*saturatedDeviation x=thermalA*x+thermalB) ∧
    (-1 ≤ x → x ≤ 1 → thermalA*x+thermalB*saturatedDeviation x=(thermalA-thermalB)*x) ∧
    (1 ≤ x → thermalA*x+thermalB*saturatedDeviation x=thermalA*x-thermalB) := by
  refine ⟨?_,?_,?_⟩
  · intro hx; unfold saturatedDeviation
    rw [min_eq_right (by linarith),max_eq_right (by norm_num)]; ring
  · intro hl hu; unfold saturatedDeviation
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]; ring
  · intro hx; unfold saturatedDeviation
    rw [min_eq_left (by linarith),max_eq_left (by linarith)]; ring

theorem saturated_branch_ranges (x : ℝ) :
    (x ∈ Set.Icc (-2:ℝ) (-1) →
      thermalA*x+thermalB*saturatedDeviation x ∈ Set.Icc (-2*thermalA+thermalB) (-thermalA+thermalB)) ∧
    (x ∈ Set.Icc (-1:ℝ) 1 →
      thermalA*x+thermalB*saturatedDeviation x ∈ Set.Icc (thermalA-thermalB) (thermalB-thermalA)) ∧
    (x ∈ Set.Icc (1:ℝ) 2 →
      thermalA*x+thermalB*saturatedDeviation x ∈ Set.Icc (thermalA-thermalB) (2*thermalA-thermalB)) := by
  have ha := thermal_coefficients.1
  have hd : thermalA-thermalB ≤ 0 := by
    have hh := thermalA_precise; unfold thermalB; linarith [hh.2]
  refine ⟨?_,?_,?_⟩
  · intro hx; rw [(saturated_branches x).1 hx.2]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 ha.le,mul_le_mul_of_nonneg_left hx.2 ha.le]
  · intro hx; rw [(saturated_branches x).2.1 hx.1 hx.2]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 hd,mul_le_mul_of_nonpos_left hx.2 hd]
  · intro hx; rw [(saturated_branches x).2.2 hx.1]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 ha.le,mul_le_mul_of_nonneg_left hx.2 ha.le]

theorem saturated_range_rounding :
    |(thermalB-thermalA)-(105996/1000000:ℝ)| ≤ 1/2000000 := by
  have hh := thermalA_precise
  rw [abs_le]; unfold thermalB; constructor <;> linarith [hh.1,hh.2]

/-- Uniqueness on a sampling interval, obtained by an integrating factor. -/
theorem heldThermal_unique (f : ℝ → ℝ) (x v s : ℝ) (hs : s ∈ Set.Icc 0 5)
    (h0 : f 0=x)
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 5, HasDerivAt f (-(1/20)*f t+(1/5)*v) t) :
    f s=heldThermal x v s := by
  let g : ℝ → ℝ := fun t => Real.exp (t/20)*(f t-4*v)
  have hg : ∀ t ∈ Set.Icc (0:ℝ) 5, HasDerivAt g 0 t := by
    intro t ht
    have he := ((hasDerivAt_id t).div_const 20).exp
    have hh := he.mul ((hf t ht).sub_const (4*v))
    convert hh using 1 <;> (try ext y) <;>
      simp only [g,Pi.mul_apply,Pi.sub_apply,Pi.div_apply,id_eq] <;> ring
  have hdiff : ∀ t ∈ Set.Icc (0:ℝ) 5, DifferentiableAt ℝ g t :=
    fun t ht => (hg t ht).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 5, ‖deriv g t‖ ≤ (0:ℝ) := by
    intro t ht; rw [(hg t ht).deriv]; simp
  have hc := (convex_Icc (0:ℝ) 5).norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 5) hs
  have heq : g s=g 0 := by
    have hz : ‖g s-g 0‖=0 := le_antisymm (by simpa using hc) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hprod : Real.exp (-s/20)*Real.exp (s/20)=1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
  have hh := congrArg (fun z : ℝ => Real.exp (-s/20)*z) heq
  simp only [g,h0,zero_div,Real.exp_zero,one_mul] at hh
  have hh' : f s-4*v=Real.exp (-s/20)*(x-4*v) := by
    simpa only [← mul_assoc,hprod,one_mul] using hh
  unfold heldThermal
  linarith

theorem thermal_multiplier_antitone :
    Antitone (fun s : ℝ => 3*Real.exp (-s/20)-2) := by
  intro s t hst
  have he : Real.exp (-t/20) ≤ Real.exp (-s/20) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem sampled_invariant_all (x : ℕ → ℝ)
    (hstep : ∀ n, x (n+1)=thermalQ*x n) (h0 : |x 0| ≤ 2) :
    ∀ n, |x n| ≤ 2 := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih => rw [hstep]; exact sampled_thermal_invariant _ ih

theorem held_convex_endpoints (x v s : ℝ) (hs : s ∈ Set.Icc 0 5) :
    ∃ theta ∈ Set.Icc (0:ℝ) 1,
      heldThermal x v s=(1-theta)*x+theta*(thermalA*x+thermalB*v) := by
  let theta := (1-Real.exp (-s/20))/(1-thermalA)
  have ha := thermal_coefficients
  have helo : thermalA ≤ Real.exp (-s/20) := by
    apply Real.exp_le_exp.mpr; change -(1/4:ℝ) ≤ -s/20; linarith [hs.2]
  have hehi : Real.exp (-s/20) ≤ 1 := by
    rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr; linarith [hs.1]
  have hd : 0 < 1-thermalA := by linarith [ha.2.1]
  refine ⟨theta,⟨div_nonneg (by linarith) hd.le,?_⟩,?_⟩
  · dsimp [theta]; rw [div_le_one hd]; linarith
  · dsimp [theta]; unfold heldThermal thermalB
    field_simp
    ring

theorem saturated_intersample_invariant (x s : ℝ)
    (hx : |x| ≤ 2) (hs : s ∈ Set.Icc 0 5) :
    |heldThermal x (saturatedDeviation x) s| ≤ 2 := by
  obtain ⟨theta,ht,he⟩ := held_convex_endpoints x (saturatedDeviation x) s hs
  rw [he]
  calc
    |(1-theta)*x+theta*(thermalA*x+thermalB*saturatedDeviation x)|
      ≤ |(1-theta)*x|+|theta*(thermalA*x+thermalB*saturatedDeviation x)| := abs_add_le _ _
    _=(1-theta)*|x|+theta*|thermalA*x+thermalB*saturatedDeviation x| := by
      rw [abs_mul,abs_mul,abs_of_nonneg ht.1,abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-theta)]
    _≤2 := by nlinarith [mul_le_mul_of_nonneg_left hx (by linarith [ht.2] : 0 ≤ 1-theta),
      mul_le_mul_of_nonneg_left (saturated_map_invariant x hx) ht.1]

def stoppedSpeed (v a t : ℝ) : ℝ := if t ≤ v/a then brakeSpeed v a t else 0
def stoppedDistance (d v a t : ℝ) : ℝ :=
  if t ≤ v/a then brakeDistance d v a t else stoppingClearance d v a

theorem stopped_at_join (d v a : ℝ) (ha : 0 < a) :
    stoppedSpeed v a (v/a)=0 ∧
    stoppedDistance d v a (v/a)=stoppingClearance d v a := by
  simp only [stoppedSpeed,stoppedDistance,le_refl,ite_true]
  simpa only [stoppingClearance] using stopping_distance d v a ha

theorem stopped_phase (d v a t : ℝ) (ht : v/a ≤ t) (ha : 0 < a) :
    stoppedSpeed v a t=0 ∧ stoppedDistance d v a t=stoppingClearance d v a := by
  by_cases he : t=v/a
  · subst t; exact stopped_at_join d v a ha
  · have hlt : ¬ t ≤ v/a := fun h => he (le_antisymm h ht)
    simp [stoppedSpeed,stoppedDistance,hlt]

theorem stopped_speed_nonnegative (v a t : ℝ) (ha : 0 < a) :
    0 ≤ stoppedSpeed v a t := by
  unfold stoppedSpeed brakeSpeed
  split_ifs with h
  · have := (le_div_iff₀ ha).mp h; nlinarith
  · exact le_rfl

theorem constant_on_interval (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivAt f 0 s) : f t=f 0 := by
  have hh := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun s hs => (hf s hs).differentiableAt)
    (fun s hs => by simpa only [(hf s hs).deriv,norm_zero] using (le_refl (0:ℝ)))
    (by simp [ht] : (0:ℝ) ∈ Set.Icc (0:ℝ) t) (by simp [ht] : t ∈ Set.Icc (0:ℝ) t)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hh) (norm_nonneg _)))

theorem brakeSpeed_unique (f : ℝ → ℝ) (v a t : ℝ) (ht : 0 ≤ t)
    (h0 : f 0=v) (hf : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivAt f (-a) s) :
    f t=brakeSpeed v a t := by
  have hh := constant_on_interval (fun s => f s-brakeSpeed v a s) t ht (by
    intro s hs
    convert (hf s hs).sub (brake_dynamics 0 v a s).1 using 1 <;> simp)
  simp only [h0,brakeSpeed,mul_zero,sub_zero,sub_self] at hh
  change f t=v-a*t
  linarith

theorem brakeDistance_unique (f : ℝ → ℝ) (d v a t : ℝ) (ht : 0 ≤ t)
    (h0 : f 0=d) (hf : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivAt f (-(brakeSpeed v a s)) s) :
    f t=brakeDistance d v a t := by
  have hh := constant_on_interval (fun s => f s-brakeDistance d v a s) t ht (by
    intro s hs
    convert (hf s hs).sub (brake_dynamics d v a s).2 using 1 <;> simp)
  norm_num [h0,brakeDistance] at hh
  unfold brakeDistance
  linarith

theorem stopped_clearance_constant (d v a t : ℝ) (ha : 0 < a) :
    stoppingClearance (stoppedDistance d v a t) (stoppedSpeed v a t) a=
      stoppingClearance d v a := by
  unfold stoppedDistance stoppedSpeed
  split_ifs
  · exact brake_clearance_constant d v a t ha
  · simp [stoppingClearance]

theorem stopped_clearance_derivative (d v a t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s => stoppingClearance (stoppedDistance d v a s)
      (stoppedSpeed v a s) a) 0 t := by
  have he : (fun s => stoppingClearance (stoppedDistance d v a s)
      (stoppedSpeed v a s) a)=(fun _ : ℝ => stoppingClearance d v a) :=
    funext (fun s => stopped_clearance_constant d v a s ha)
  rw [he]; exact hasDerivAt_const t _

theorem stopped_safe_iff (d v a : ℝ) (hv : 0 ≤ v) (ha : 0 < a) :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ stoppedDistance d v a t) ↔
      0 ≤ stoppingClearance d v a := by
  constructor
  · intro h
    have hh := h (v/a) (div_nonneg hv ha.le)
    rwa [(stopped_at_join d v a ha).2] at hh
  · intro h t ht
    unfold stoppedDistance
    split_ifs
    · exact braking_all_time_safe d v a t ha h
    · exact h

theorem brake_speed_integral (v a : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..v/a, brakeSpeed v a t)=v^2/(2*a) := by
  unfold brakeSpeed
  have hic : IntervalIntegrable (fun t : ℝ => a*t) MeasureTheory.volume 0 (v/a) :=
    (by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub
    (f := fun _ : ℝ => v) (g := fun t : ℝ => a*t) intervalIntegrable_const hic,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [smul_eq_mul,sub_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  field_simp
  ring

def delayedDistance (d v a tau t : ℝ) : ℝ :=
  if t ≤ tau then d-v*t else stoppedDistance (d-v*tau) v a (t-tau)

theorem delayed_safe_iff (d v a tau : ℝ) (hv : 0 ≤ v) (ha : 0 < a) (htau : 0 ≤ tau) :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ delayedDistance d v a tau t) ↔
      v*tau+v^2/(2*a) ≤ d := by
  constructor
  · intro h
    have ht := h (tau+v/a) (by positivity)
    have hd : delayedDistance d v a tau (tau+v/a)=stoppingClearance (d-v*tau) v a := by
      unfold delayedDistance
      split_ifs with hcase
      · have hz : v/a=0 := by have hp := div_nonneg hv ha.le; linarith
        have hvz : v=0 := (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt ha)
        simp [hvz,stoppingClearance]
      · convert (stopped_at_join (d-v*tau) v a ha).2 using 1 <;> ring
    rw [hd] at ht
    unfold stoppingClearance at ht
    linarith
  · intro h t ht
    have hc : 0 ≤ stoppingClearance (d-v*tau) v a := by
      unfold stoppingClearance; linarith
    unfold delayedDistance
    split_ifs with hcase
    · have hp : 0 ≤ v^2/(2*a) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hcase hv
      unfold stoppingClearance at hc
      linarith
    · exact (stopped_safe_iff (d-v*tau) v a hv ha).2 hc (t-tau) (by linarith)

theorem nominal_delay_endpoint (tau : ℝ) (htau : 0 ≤ tau) :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ delayedDistance (4/5) 1 1 tau t) ↔ tau ≤ 3/10 := by
  rw [delayed_safe_iff _ _ _ _ (by norm_num) (by norm_num) htau]
  constructor <;> intro h <;> norm_num at * <;> linarith

theorem robust_delayed_safe (d v a tau : ℝ)
    (hd : d ∈ Set.Icc (18/25) (39/50)) (hv : v ∈ Set.Icc (9/10) (11/10))
    (ha : 1 ≤ a) (ht : tau ∈ Set.Icc 0 (23/220)) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ delayedDistance d v a tau t := by
  exact (delayed_safe_iff d v a tau (by linarith [hv.1]) (by linarith) ht.1).2
    (uncertain_braking_guarantee d v a tau hd hv ha ht)

theorem robust_delay_necessary (tau : ℝ) (ht : 0 ≤ tau)
    (hsafe : ∀ d ∈ Set.Icc (18/25:ℝ) (39/50),
      ∀ v ∈ Set.Icc (9/10:ℝ) (11/10), ∀ a : ℝ, 1 ≤ a →
      ∀ t : ℝ, 0 ≤ t → 0 ≤ delayedDistance d v a tau t) : tau ≤ 23/220 := by
  have hh := (delayed_safe_iff (18/25) (11/10) 1 tau (by norm_num) (by norm_num) ht).1
    (hsafe (18/25) (by norm_num) (11/10) (by norm_num) 1 (by norm_num))
  exact (worst_case_delay tau).1 (by norm_num at hh ⊢; exact hh)

theorem robust_delay_rounding : |(23/220:ℝ)-(104545/1000000)| ≤ 1/2000000 := by norm_num

end SafeLearning.CompleteAppliedDynamics
