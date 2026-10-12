import SafeLearning.CompleteMonitoringPolicyValues22
import Mathlib
import SafeLearning.CompleteCoreProjectedDualDrift29

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace SafeLearning.CompleteAppliedCMDPExponentialBridge30

/-- These constants are derived from a positive increment bound and negative
mean drift. No moment, tail, independence, or limiting-growth premise is used. -/
def driftTheta (h d : ℝ) : ℝ := min (1/h) (min (d/(2*h^2)) (1/d))
def driftQ (h d : ℝ) : ℝ := 1-driftTheta h d*d/2

theorem actual_drift_theta_is_positive (h d : ℝ) (hh : 0<h) (hd : 0<d) :
    0<driftTheta h d := by
  unfold driftTheta
  apply lt_min
  · positivity
  · apply lt_min <;> positivity

theorem actual_drift_theta_controls_the_increment (h d : ℝ)
    (hh : 0<h) : driftTheta h d*h≤1 := by
  have hle : driftTheta h d≤1/h := min_le_left _ _
  have hm:=mul_le_mul_of_nonneg_right hle hh.le
  have he : (1/h)*h=1 := by field_simp
  simpa only [he] using hm

theorem actual_drift_theta_controls_the_quadratic_remainder (h d : ℝ)
    (hh : 0<h) : driftTheta h d*h^2≤d/2 := by
  have hle : driftTheta h d≤d/(2*h^2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm:=mul_le_mul_of_nonneg_right hle (sq_nonneg h)
  have he : (d/(2*h^2))*h^2=d/2 := by field_simp
  simpa only [he] using hm

theorem actual_drift_theta_controls_the_contraction (h d : ℝ)
    (hd : 0<d) : driftTheta h d*d≤1 := by
  have hle : driftTheta h d≤1/d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hm:=mul_le_mul_of_nonneg_right hle hd.le
  have he : (1/d)*d=1 := by field_simp
  simpa only [he] using hm

theorem actual_contraction_is_between_half_and_one (h d : ℝ)
    (hh : 0<h) (hd : 0<d) : 1/2≤driftQ h d ∧ driftQ h d<1 := by
  have hp:=actual_drift_theta_is_positive h d hh hd
  have hc:=actual_drift_theta_controls_the_contraction h d hd
  unfold driftQ
  constructor <;> nlinarith

theorem actual_exponential_increment_is_bounded_by_its_linear_drift_and_remainder
    (theta h z : ℝ) (htheta : 0≤theta) (hh : 0≤h)
    (hsmall : theta*h≤1) (hz : |z|≤h) :
    Real.exp (theta*z)≤1+theta*z+theta^2*h^2 := by
  have htz : |theta*z|≤1 := by
    rw [abs_mul,abs_of_nonneg htheta]
    exact (mul_le_mul_of_nonneg_left hz htheta).trans hsmall
  have he:= (abs_le.mp (Real.abs_exp_sub_one_sub_id_le htz)).2
  have hzsq : z^2≤h^2 := by
    have ha:=abs_le.mp hz
    nlinarith [sq_nonneg (h-z),sq_nonneg (h+z)]
  have hs:=mul_le_mul_of_nonneg_left hzsq (sq_nonneg theta)
  nlinarith

theorem actual_bounded_increment_gives_a_finite_path_bound
    (X : ℕ→ℝ) (h : ℝ) (hincrement : ∀ n,|X (n+1)-X n|≤h) (n : ℕ) :
    X n≤X 0+(n:ℝ)*h := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu:= (abs_le.mp (hincrement n)).2
    push_cast
    linarith

theorem actual_nonnegative_norm_square_difference_dominates_twice_the_norm_increment
    (x y : ℝ) : 2*x*(y-x)≤y^2-x^2 := by
  nlinarith [sq_nonneg (y-x)]

theorem actual_energy_drift_implies_negative_norm_drift_outside_the_explicit_radius
    (eta C M h x delta : ℝ) (heta : 0<eta) (hC : 0<C)
    (hx : 0<x) (hlarge : h^2+2*eta*M≤eta*C*x)
    (henergy : 2*x*delta≤h^2+2*eta*M-2*eta*C*x) :
    delta≤-(eta*C/2) := by
  have hmul : 2*x*delta≤-(eta*C*x) := by linarith
  nlinarith

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

theorem actual_bounded_increment_exponential_is_integrable
    (P : Measure Ω) [IsProbabilityMeasure P] (z : Ω→ℝ)
    (hz : @Measurable Ω ℝ m0 Real.measurableSpace z) (theta h : ℝ) (htheta : 0≤theta)
    (hbound : ∀ᵐ w ∂P,|z w|≤h) :
    Integrable (fun w => Real.exp (theta*z w)) P := by
  apply (integrable_const (Real.exp (theta*h))).mono'
      ((measurable_const.mul hz).exp.aestronglyMeasurable)
  filter_upwards [hbound] with w hw
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hw) htheta)

theorem actual_negative_mean_drift_gives_exponential_contraction
    (P : Measure Ω) [IsProbabilityMeasure P] (z : Ω→ℝ)
    (hz : @Measurable Ω ℝ m0 Real.measurableSpace z) (hiz : Integrable z P) (h d : ℝ)
    (hh : 0<h) (hd : 0<d) (hbound : ∀ᵐ w ∂P,|z w|≤h)
    (hmean : (∫ w,z w ∂P)≤-d) :
    (∫ w,Real.exp (driftTheta h d*z w) ∂P)≤driftQ h d := by
  let theta:=driftTheta h d
  have ht : 0<theta := actual_drift_theta_is_positive h d hh hd
  have hi:=actual_bounded_increment_exponential_is_integrable P z hz theta h ht.le hbound
  have hpoly : Integrable (fun w => 1+theta*z w+theta^2*h^2) P :=
    ((integrable_const 1).add (hiz.const_mul theta)).add (integrable_const _)
  have hm:=integral_mono_ae hi hpoly (hbound.mono fun w hw =>
    actual_exponential_increment_is_bounded_by_its_linear_drift_and_remainder
      theta h (z w) ht.le hh.le
      (actual_drift_theta_controls_the_increment h d hh) hw)
  have hic : Integrable (fun _ : Ω => (1:ℝ)) P := integrable_const _
  have hit : Integrable (fun w => theta*z w) P := hiz.const_mul _
  have heval : (∫ w,1+theta*z w+theta^2*h^2 ∂P) =
      1+theta*(∫ w,z w ∂P)+theta^2*h^2 := by
    calc (∫ w,1+theta*z w+theta^2*h^2 ∂P) =
        (∫ w,1+theta*z w ∂P)+(∫ _w : Ω,theta^2*h^2 ∂P) :=
          integral_add (hic.add hit) (integrable_const _)
         _ = ((∫ _w : Ω,(1:ℝ) ∂P)+(∫ w,theta*z w ∂P))+
             (∫ _w : Ω,theta^2*h^2 ∂P) := by
           rw [integral_add hic hit]
         _ = 1+theta*(∫ w,z w ∂P)+theta^2*h^2 := by
           rw [integral_const_mul]
           simp
  rw [heval] at hm
  have hdmean:=mul_le_mul_of_nonneg_left hmean ht.le
  have hrem:=actual_drift_theta_controls_the_quadratic_remainder h d hh
  have hr:=mul_le_mul_of_nonneg_left hrem ht.le
  change (∫ w,Real.exp (theta*z w) ∂P)≤1-theta*d/2
  nlinarith

/-- This component uses conditioning on precisely the supplied sigma-algebra.
It does not strengthen it to a history filtration or assume independent increments. -/
theorem actual_conditional_bounded_increment_exponential_estimate
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : MeasurableSpace Ω) (hs : s ≤ m0)
    (z : Ω→ℝ) (hz : @Measurable Ω ℝ m0 Real.measurableSpace z) (hiz : Integrable z P)
    (theta h : ℝ) (htheta : 0≤theta) (hh : 0≤h)
    (hsmall : theta*h≤1) (hbound : ∀ᵐ w ∂P,|z w|≤h) :
    ∀ᵐ w ∂P,(P[fun v => Real.exp (theta*z v) | s]) w≤
      1+theta*(P[z | s]) w+theta^2*h^2 := by
  letI : MeasurableSpace Ω := m0
  have hi:=actual_bounded_increment_exponential_is_integrable P z hz theta h htheta hbound
  have hic : Integrable (fun _ : Ω => (1:ℝ)) P:=integrable_const _
  have hizt : Integrable (fun w => theta*z w) P:=hiz.const_mul _
  have hir : Integrable (fun _ : Ω => theta^2*h^2) P:=integrable_const _
  have hpoly:= (hic.add hizt).add hir
  have hmono:=condExp_mono (m:=s) hi hpoly (hbound.mono fun w hw =>
    actual_exponential_increment_is_bounded_by_its_linear_drift_and_remainder
      theta h (z w) htheta hh hsmall hw)
  have ha:=condExp_add (hic.add hizt) hir s
  have hb:=condExp_add hic hizt s
  have hc : P[fun w => theta*z w | s] =ᵐ[P]
      fun w => theta*(P[z | s]) w := condExp_smul theta z s (μ:=P)
  filter_upwards [hmono,ha,hb,hc] with w hw hwa hwb hwc
  simp only [Pi.add_apply,condExp_const hs] at hwa hwb hwc
  rw [hwa,hwb,hwc] at hw
  simpa only [condExp_const hs] using hw

theorem actual_conditional_negative_drift_gives_exponential_contraction
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : MeasurableSpace Ω) (hs : s ≤ m0)
    (z : Ω→ℝ) (hz : @Measurable Ω ℝ m0 Real.measurableSpace z) (hiz : Integrable z P)
    (h d : ℝ) (hh : 0<h) (hd : 0<d)
    (hbound : ∀ᵐ w ∂P,|z w|≤h) :
    ∀ᵐ w ∂P,(P[z | s]) w≤-d →
      (P[fun v => Real.exp (driftTheta h d*z v) | s]) w≤driftQ h d := by
  letI : MeasurableSpace Ω := m0
  let theta:=driftTheta h d
  have ht : 0<theta := actual_drift_theta_is_positive h d hh hd
  have ha:=actual_conditional_bounded_increment_exponential_estimate
    P s hs z hz hiz theta h ht.le hh.le
    (actual_drift_theta_controls_the_increment h d hh) hbound
  filter_upwards [ha] with w hw
  intro hdw
  have hm:=mul_le_mul_of_nonneg_left hdw ht.le
  have hr:=mul_le_mul_of_nonneg_left
    (actual_drift_theta_controls_the_quadratic_remainder h d hh) ht.le
  change (P[fun v => Real.exp (theta*z v) | s]) w≤1-theta*d/2
  nlinarith

/-- Deterministic affine recurrence; the stochastic application must first
derive this recurrence by conditional integration, as above. -/
theorem actual_affine_recurrence_gives_the_finite_geometric_moment_bound
    (A : ℕ→ℝ) (q K : ℝ) (hq : 0≤q)
    (hrec : ∀ n,A (n+1)≤q*A n+K) (n : ℕ) :
    A n≤q^n*A 0+K*∑ i ∈ Finset.range n,q^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm:=mul_le_mul_of_nonneg_left ih hq
    have hs : q*(∑ i ∈ Finset.range n,q^i)+1=
        ∑ i ∈ Finset.range (n+1),q^i := by
      rw [Finset.sum_range_succ',Finset.mul_sum]
      simp only [pow_succ',pow_zero]
    rw [← hs,pow_succ']
    nlinarith [hrec n]

theorem actual_affine_recurrence_gives_a_uniform_moment_bound
    (A : ℕ→ℝ) (q K : ℝ) (hq : 0≤q) (hqlt : q<1)
    (hA0 : 0≤A 0) (hK : 0≤K) (hrec : ∀ n,A (n+1)≤q*A n+K)
    (n : ℕ) : A n≤A 0+K/(1-q) := by
  have hden : 0<1-q := sub_pos.mpr hqlt
  induction n with
  | zero => exact le_add_of_nonneg_right (div_nonneg hK hden.le)
  | succ n ih =>
    have hm:=mul_le_mul_of_nonneg_left ih hq
    have hqa:=mul_le_mul_of_nonneg_right hqlt.le hA0
    have he : q*(A 0+K/(1-q))+K=q*A 0+K/(1-q) := by
      field_simp
      ring
    calc A (n+1)≤q*A n+K:=hrec n
         _≤q*(A 0+K/(1-q))+K:=by linarith
         _=q*A 0+K/(1-q):=he
         _≤A 0+K/(1-q):=by linarith

theorem actual_positive_epoch_boundaries_are_cofinal
    (T : ℕ) (hT : 0<T) : Tendsto (fun N : ℕ => N*T) atTop atTop := by
  apply tendsto_atTop_mono (fun N => ?_) tendsto_id
  exact Nat.le_mul_of_pos_right N hT

/-- The limit is explicitly for the actual switched expected-average sequence.
Fixed-policy value limits are not substituted for this hypothesis. -/
theorem actual_switched_expected_average_limit_inherits_the_derived_epoch_lower_bound
    (T : ℕ) (hT : 0<T) (a : ℕ→ℝ) (L Pstar error C : ℝ)
    (hlimit : Tendsto a atTop (𝓝 L))
    (hepoch : ∀ N : ℕ,0<N → Pstar-error-C/(N:ℝ)≤a (N*T)) :
    Pstar-error≤L := by
  have hsub:=hlimit.comp (actual_positive_epoch_boundaries_are_cofinal T hT)
  have hlow : Tendsto (fun N : ℕ => Pstar-error-C/(N:ℝ)) atTop
      (𝓝 (Pstar-error)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  exact le_of_tendsto_of_tendsto hlow hsub
    ((eventually_gt_atTop 0).mono fun N hN => hepoch N hN)

/-- The first true stochastic moment recurrence is derived from conditional
negative norm drift. The deterministic finite bound B, and no moment premise,
establishes every integrability obligation before conditional pull-out. -/
theorem actual_conditional_negative_norm_drift_derives_the_exponential_moment_recurrence
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : MeasurableSpace Ω) (hs : s ≤ m0)
    (X Y : Ω → ℝ) (hXs : Measurable[s] X) (hY : @Measurable Ω ℝ m0 Real.measurableSpace Y)
    (B h d R : ℝ) (hh : 0 < h) (hd : 0 < d)
    (hXnonnegative : ∀ᵐ w ∂P, 0 ≤ X w)
    (hYnonnegative : ∀ᵐ w ∂P, 0 ≤ Y w)
    (hXfinite : ∀ᵐ w ∂P, X w ≤ B)
    (hincrement : ∀ᵐ w ∂P, |Y w-X w| ≤ h)
    (hnegative : ∀ᵐ w ∂P, R ≤ X w →
      (P[fun v => Y v-X v | s]) w ≤ -d) :
    (∫ w,Real.exp (driftTheta h d*Y w) ∂P) ≤
      driftQ h d*(∫ w,Real.exp (driftTheta h d*X w) ∂P)+
      Real.exp (driftTheta h d*(R+h)) := by
  letI : MeasurableSpace Ω := m0
  let theta := driftTheta h d
  let q := driftQ h d
  let z : Ω → ℝ := fun w => Y w-X w
  have ht : 0 < theta := actual_drift_theta_is_positive h d hh hd
  have hq : 0 ≤ q := (by norm_num : (0:ℝ) ≤ 1/2).trans
    (actual_contraction_is_between_half_and_one h d hh hd).1
  have hX : Measurable X := hXs.mono hs le_rfl
  have hz : Measurable z := hY.sub hX
  have hbX : ∀ᵐ w ∂P, |X w| ≤ B := by
    filter_upwards [hXnonnegative,hXfinite] with w hw hb
    simpa only [abs_of_nonneg hw] using hb
  have hbY : ∀ᵐ w ∂P, |Y w| ≤ B+h := by
    filter_upwards [hYnonnegative,hXfinite,hincrement] with w hw hb hi
    rw [abs_of_nonneg hw]
    linarith [(abs_le.mp hi).2]
  have hiX := actual_bounded_increment_exponential_is_integrable P X hX theta B ht.le hbX
  have hiY := actual_bounded_increment_exponential_is_integrable P Y hY theta (B+h) ht.le hbY
  have hiz : Integrable z P := by
    apply (integrable_const h).mono' hz.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hincrement
  have hie := actual_bounded_increment_exponential_is_integrable P z hz theta h ht.le hincrement
  have hexp (w : Ω) : Real.exp (theta*Y w) =
      Real.exp (theta*X w)*Real.exp (theta*z w) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [z]
    ring
  have hiProduct : Integrable ((fun w => Real.exp (theta*X w)) *
      (fun w => Real.exp (theta*z w))) P :=
    hiY.congr (Eventually.of_forall hexp)
  have hf_s : StronglyMeasurable[s] (fun w => Real.exp (theta*X w)) :=
    (hXs.const_mul theta).exp.stronglyMeasurable
  have hpull : P[fun w => Real.exp (theta*X w)*Real.exp (theta*z w) | s] =ᵐ[P]
      fun w => Real.exp (theta*X w)*(P[fun v => Real.exp (theta*z v) | s]) w :=
    condExp_mul_of_stronglyMeasurable_left
      hf_s hiProduct hie
  have heY := condExp_congr_ae (m:=s) (μ:=P) (Eventually.of_forall hexp)
  have hcontract := actual_conditional_negative_drift_gives_exponential_contraction
    P s hs z hz hiz h d hh hd hincrement
  have hbExp : ∀ᵐ w ∂P, Real.exp (theta*z w) ≤ Real.exp (theta*h) := by
    filter_upwards [hincrement] with w hw
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hw) ht.le)
  have hupper := condExp_mono (m:=s) hie (integrable_const (Real.exp (theta*h))) hbExp
  have hglobal : ∀ᵐ w ∂P,
      (P[fun v => Real.exp (theta*Y v) | s]) w ≤
        q*Real.exp (theta*X w)+Real.exp (theta*(R+h)) := by
    filter_upwards [hpull,heY,hcontract,hupper,hnegative] with w hp he hc hu hn
    simp only [condExp_const hs] at hu
    rw [he,hp]
    by_cases hw : R ≤ X w
    · have hmul := mul_le_mul_of_nonneg_left (hc (hn hw)) (Real.exp_pos (theta*X w)).le
      dsimp [q] at hmul ⊢
      nlinarith [Real.exp_pos (theta*(R+h))]
    · have hXexp : Real.exp (theta*X w) ≤ Real.exp (theta*R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hw) ht.le)
      have hinside : Real.exp (theta*X w)*(P[fun v => Real.exp (theta*z v) | s]) w ≤
          Real.exp (theta*(R+h)) := by
        calc _ ≤ Real.exp (theta*X w)*Real.exp (theta*h) :=
                 mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
             _ ≤ Real.exp (theta*R)*Real.exp (theta*h) :=
                 mul_le_mul_of_nonneg_right hXexp (Real.exp_pos _).le
             _ = Real.exp (theta*(R+h)) := by rw [← Real.exp_add]; congr 1; ring
      exact hinside.trans (le_add_of_nonneg_left (mul_nonneg hq (Real.exp_pos _).le))
  have hiRight : Integrable (fun w => q*Real.exp (theta*X w)+Real.exp (theta*(R+h))) P :=
    (hiX.const_mul q).add (integrable_const _)
  calc (∫ w,Real.exp (theta*Y w) ∂P) =
      (∫ w,(P[fun v => Real.exp (theta*Y v) | s]) w ∂P) := (integral_condExp hs).symm
       _ ≤ (∫ w,q*Real.exp (theta*X w)+Real.exp (theta*(R+h)) ∂P) :=
         integral_mono_ae integrable_condExp hiRight hglobal
       _ = q*(∫ w,Real.exp (theta*X w) ∂P)+Real.exp (theta*(R+h)) := by
         rw [integral_add (hiX.const_mul q) (integrable_const _),integral_const_mul]
         simp


/-- Finite-time bounds are derived almost everywhere, one step at a time;
no uniform moment premise or filtration nesting is required. -/
theorem actual_ae_bounded_process_increments_derive_every_finite_path_bound
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (B h : ℝ)
    (hzero : ∀ᵐ w ∂P, X 0 w ≤ B)
    (hincrement : ∀ n, ∀ᵐ w ∂P, |X (n+1) w-X n w| ≤ h) :
    ∀ n, ∀ᵐ w ∂P, X n w ≤ B+(n:ℝ)*h := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    filter_upwards [ih,hincrement n] with w hw hi
    have hu := (abs_le.mp hi).2
    push_cast
    linarith

/-- Uniform exponential moments follow from the actual conditional negative
drift and bounded process increments. Conditioning remains on the supplied
current-state sigma spaces; neither independence nor history drift is assumed. -/
theorem actual_current_state_conditional_negative_drift_derives_uniform_process_moments
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n, s n ≤ m0)
    (X : ℕ → Ω → ℝ) (hXs : ∀ n, Measurable[s n] (X n))
    (B h d R : ℝ) (hh : 0 < h) (hd : 0 < d)
    (hnonnegative : ∀ n, ∀ᵐ w ∂P, 0 ≤ X n w)
    (hzero : ∀ᵐ w ∂P, X 0 w ≤ B)
    (hincrement : ∀ n, ∀ᵐ w ∂P, |X (n+1) w-X n w| ≤ h)
    (hnegative : ∀ n, ∀ᵐ w ∂P, R ≤ X n w →
      (P[fun v => X (n+1) v-X n v | s n]) w ≤ -d) :
    ∀ n, (∫ w,Real.exp (driftTheta h d*X n w) ∂P) ≤
      Real.exp (driftTheta h d*B)+
        Real.exp (driftTheta h d*(R+h))/(1-driftQ h d) := by
  let theta := driftTheta h d
  let q := driftQ h d
  let K := Real.exp (theta*(R+h))
  let A : ℕ → ℝ := fun n => ∫ w,Real.exp (theta*X n w) ∂P
  have ht : 0 < theta := actual_drift_theta_is_positive h d hh hd
  have hqhalf := actual_contraction_is_between_half_and_one h d hh hd
  have hq : 0 ≤ q := (by norm_num : (0:ℝ) ≤ 1/2).trans hqhalf.1
  have hb := actual_ae_bounded_process_increments_derive_every_finite_path_bound
    P X B h hzero hincrement
  have hrec : ∀ n, A (n+1) ≤ q*A n+K := by
    intro n
    exact actual_conditional_negative_norm_drift_derives_the_exponential_moment_recurrence
      P (s n) (hs n) (X n) (X (n+1)) (hXs n)
      ((hXs (n+1)).mono (hs (n+1)) le_rfl)
      (B+(n:ℝ)*h) h d R hh hd
      (hnonnegative n) (hnonnegative (n+1)) (hb n) (hincrement n) (hnegative n)
  have hA0 : 0 ≤ A 0 := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hbzero : ∀ᵐ w ∂P, |X 0 w| ≤ B := by
    filter_upwards [hnonnegative 0,hzero] with w hw hb0
    simpa only [abs_of_nonneg hw] using hb0
  have hi0 := actual_bounded_increment_exponential_is_integrable P (X 0)
    ((hXs 0).mono (hs 0) le_rfl) theta B ht.le hbzero
  have hA0upper : A 0 ≤ Real.exp (theta*B) := by
    have hu : ∀ᵐ w ∂P, Real.exp (theta*X 0 w) ≤ Real.exp (theta*B) :=
      hzero.mono (fun _ hw => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw ht.le))
    have hi := integral_mono_ae hi0 (integrable_const (Real.exp (theta*B))) hu
    simpa [A] using hi
  intro n
  have ha := actual_affine_recurrence_gives_a_uniform_moment_bound
    A q K hq hqhalf.2 hA0 (Real.exp_pos _).le hrec n
  exact ha.trans (add_le_add hA0upper le_rfl)


/-- Chernoff, a derived uniform moment bound, and the first Borel-Cantelli
lemma rule out infinitely many linear-size excursions. Independence is absent. -/
theorem actual_current_state_negative_drift_derives_summable_linear_escape_tails
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n, s n ≤ m0)
    (X : ℕ → Ω → ℝ) (hXs : ∀ n, Measurable[s n] (X n))
    (B h d R epsilon : ℝ) (hh : 0 < h) (hd : 0 < d) (hepsilon : 0 < epsilon)
    (hnonnegative : ∀ n, ∀ᵐ w ∂P, 0 ≤ X n w)
    (hzero : ∀ᵐ w ∂P, X 0 w ≤ B)
    (hincrement : ∀ n, ∀ᵐ w ∂P, |X (n+1) w-X n w| ≤ h)
    (hnegative : ∀ n, ∀ᵐ w ∂P, R ≤ X n w →
      (P[fun v => X (n+1) v-X n v | s n]) w ≤ -d) :
    (∑' n : ℕ, P {w | epsilon*(n:ℝ) ≤ X n w}) < ∞ ∧
      ∀ᵐ w ∂P, ∀ᶠ n in atTop, X n w < epsilon*(n:ℝ) := by
  let theta := driftTheta h d
  let C := Real.exp (theta*B)+Real.exp (theta*(R+h))/(1-driftQ h d)
  have ht : 0 < theta := actual_drift_theta_is_positive h d hh hd
  have hm := actual_current_state_conditional_negative_drift_derives_uniform_process_moments
    P s hs X hXs B h d R hh hd hnonnegative hzero hincrement hnegative
  have hb := actual_ae_bounded_process_increments_derive_every_finite_path_bound
    P X B h hzero hincrement
  have hi (n : ℕ) : Integrable (fun w => Real.exp (theta*X n w)) P := by
    apply actual_bounded_increment_exponential_is_integrable P (X n)
      ((hXs n).mono (hs n) le_rfl) theta (B+(n:ℝ)*h) ht.le
    filter_upwards [hnonnegative n,hb n] with w hn hw
    simpa only [abs_of_nonneg hn] using hw
  have htail (n : ℕ) : P.real {w | epsilon*(n:ℝ) ≤ X n w} ≤
      Real.exp (-theta*epsilon)^n*C := by
    have hc := measure_ge_le_exp_mul_mgf (μ:=P) (X:=X n)
      (epsilon*(n:ℝ)) ht.le (hi n)
    have hu := mul_le_mul_of_nonneg_left (hm n)
      (Real.exp_pos (-theta*(epsilon*(n:ℝ)))).le
    have he : Real.exp (-theta*(epsilon*(n:ℝ)))=Real.exp (-theta*epsilon)^n := by
      rw [show -theta*(epsilon*(n:ℝ))=(n:ℝ)*(-theta*epsilon) by ring,Real.exp_nat_mul]
    dsimp [mgf] at hc
    exact hc.trans (by simpa only [he] using hu)
  have hsmall : |Real.exp (-theta*epsilon)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _),←Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-theta*epsilon)^n*C) :=
    (summable_geometric_of_abs_lt_one hsmall).mul_right C
  have hsum : Summable (fun n : ℕ => P.real {w | epsilon*(n:ℝ) ≤ X n w}) :=
    hgeom.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) htail
  have hfinite : (∑' n : ℕ,P {w | epsilon*(n:ℝ) ≤ X n w}) ≠ ∞ := by
    have he (n : ℕ) : ENNReal.ofReal (P.real {w | epsilon*(n:ℝ) ≤ X n w})=
        P {w | epsilon*(n:ℝ) ≤ X n w} := ENNReal.ofReal_toReal (measure_ne_top P _)
    simpa only [he] using hsum.tsum_ofReal_ne_top
  refine ⟨lt_top_iff_ne_top.mpr hfinite,?_⟩
  have hbc := ae_eventually_notMem hfinite
  filter_upwards [hbc] with w hw
  exact hw.mono (fun n hn => lt_of_not_ge hn)


/-- Countably many derived Borel-Cantelli bounds give sublinear growth almost
everywhere. This is a conclusion, with no tightness/random-subsequence premise. -/
theorem actual_current_state_negative_drift_derives_ae_sublinear_norm_growth
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n, s n ≤ m0)
    (X : ℕ → Ω → ℝ) (hXs : ∀ n, Measurable[s n] (X n))
    (B h d R : ℝ) (hh : 0 < h) (hd : 0 < d)
    (hnonnegative : ∀ n, ∀ᵐ w ∂P, 0 ≤ X n w)
    (hzero : ∀ᵐ w ∂P, X 0 w ≤ B)
    (hincrement : ∀ n, ∀ᵐ w ∂P, |X (n+1) w-X n w| ≤ h)
    (hnegative : ∀ n, ∀ᵐ w ∂P, R ≤ X n w →
      (P[fun v => X (n+1) v-X n v | s n]) w ≤ -d) :
    ∀ᵐ w ∂P, Tendsto (fun n : ℕ => X n w/(n:ℝ)) atTop (nhds 0) := by
  have heps : ∀ j : ℕ, ∀ᵐ w ∂P, ∀ᶠ n in atTop,
      X n w < (1/((j:ℝ)+1))*(n:ℝ) := by
    intro j
    exact (actual_current_state_negative_drift_derives_summable_linear_escape_tails
      P s hs X hXs B h d R (1/((j:ℝ)+1)) hh hd (by positivity)
      hnonnegative hzero hincrement hnegative).2
  have hall := ae_all_iff.mpr heps
  have hnon := ae_all_iff.mpr hnonnegative
  filter_upwards [hall,hnon] with w hw hn
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      (div_nonneg (hn n) (Nat.cast_nonneg n)))
  · intro epsilon hepsilon
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt hepsilon
    filter_upwards [hw j,eventually_gt_atTop 0] with n hescape hnpos
    have hnp : 0 < (n:ℝ) := by exact_mod_cast hnpos
    exact ((div_lt_iff₀ hnp).mpr hescape).trans hj


/-- The negative conditional norm drift is derived from the actual projected
energy inequality and the conditional Slater pairing. Only current-state
measurability is used to pull out the finite-time norm. -/
theorem actual_conditional_projected_energy_and_slater_pairing_derive_negative_norm_drift
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : MeasurableSpace Ω) (hs : s ≤ m0)
    (X Y Z : Ω → ℝ) (hXs : Measurable[s] X)
    (hY : @Measurable Ω ℝ m0 Real.measurableSpace Y) (hiZ : Integrable Z P)
    (B h eta C M : ℝ) (hh : 0 < h) (heta : 0 < eta) (hC : 0 < C)
    (hXnonnegative : ∀ᵐ w ∂P,0 ≤ X w)
    (hXfinite : ∀ᵐ w ∂P,X w ≤ B)
    (hincrement : ∀ᵐ w ∂P,|Y w-X w| ≤ h)
    (henergy : ∀ᵐ w ∂P,Y w^2 ≤ X w^2+h^2-2*eta*Z w)
    (hpairing : ∀ᵐ w ∂P,C*X w-M ≤ (P[Z | s]) w) :
    ∀ᵐ w ∂P,max 1 ((h^2+2*eta*M)/(eta*C)) ≤ X w →
      (P[fun v => Y v-X v | s]) w ≤ -(eta*C/2) := by
  letI : MeasurableSpace Ω := m0
  let z : Ω → ℝ := fun w => Y w-X w
  have hX : Measurable X := hXs.mono hs le_rfl
  have hz : Measurable z := hY.sub hX
  have hiz : Integrable z P := by
    apply (integrable_const h).mono' hz.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hincrement
  have hiProduct : Integrable (fun w => 2*X w*z w) P := by
    apply (integrable_const (2*|B| *h)).mono'
      ((measurable_const.mul hX).mul hz).aestronglyMeasurable
    filter_upwards [hXnonnegative,hXfinite,hincrement] with w hn hb hi
    have hx : |X w| ≤ |B| := by rw [abs_of_nonneg hn]; exact hb.trans (le_abs_self B)
    change |2*X w*z w| ≤ 2*|B| *h
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hi
      (abs_nonneg _) (by positivity)
  have hiRight : Integrable (fun w => h^2-2*eta*Z w) P :=
    (integrable_const (h^2)).sub (hiZ.const_mul (2*eta))
  have hpoint : ∀ᵐ w ∂P,2*X w*z w ≤ h^2-2*eta*Z w := by
    filter_upwards [henergy] with w hw
    dsimp [z]
    nlinarith [sq_nonneg (Y w-X w)]
  have hm := condExp_mono (m:=s) hiProduct hiRight hpoint
  have hpull : P[fun w => 2*X w*z w | s] =ᵐ[P]
      fun w => 2*X w*(P[z | s]) w :=
    condExp_mul_of_stronglyMeasurable_left
      (hXs.const_mul 2).stronglyMeasurable hiProduct hiz
  have hsub : P[fun w => h^2-2*eta*Z w | s] =ᵐ[P]
      fun w => (P[fun _ : Ω => h^2 | s]) w-(P[fun v => 2*eta*Z v | s]) w := by
    convert (condExp_sub (integrable_const (h^2)) (hiZ.const_mul (2*eta)) s) using 1 <;> rfl
  have hconst : P[fun w => 2*eta*Z w | s] =ᵐ[P]
      fun w => 2*eta*(P[Z | s]) w := by
    convert (condExp_smul (2*eta) Z s (μ:=P)) using 1 <;> rfl
  filter_upwards [hm,hpull,hsub,hconst,hpairing] with w hw hp hs' hc hpair
  simp only [condExp_const hs] at hs'
  rw [hp,hs',hc] at hw
  intro hlarge
  have hpositive : 0 < X w := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    ((le_max_left _ _).trans hlarge)
  have hden : 0 < eta*C := mul_pos heta hC
  have hr : (h^2+2*eta*M)/(eta*C) ≤ X w := (le_max_right _ _).trans hlarge
  have hD : h^2+2*eta*M ≤ eta*C*X w := by
    have he := (div_le_iff₀ hden).mp hr
    simpa only [mul_comm] using he
  have hsl := mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ 2*eta)
  have he : 2*X w*(P[z | s]) w ≤ h^2+2*eta*M-2*eta*C*X w := by
    nlinarith
  exact actual_energy_drift_implies_negative_norm_drift_outside_the_explicit_radius
    eta C M h (X w) ((P[z | s]) w) heta hC hpositive hD he

end SafeLearning.CompleteAppliedCMDPExponentialBridge30

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedCMDPProjectedSlaterBridge30
open CompleteCoreProjectedDualDrift29
variable {m : ℕ}

theorem actual_coordinate_projection_increment_is_bounded
    (eta : ℝ) (l g : Fin m → ℝ) (hl : ∀ i,0 ≤ l i) (i : Fin m) :
    |step eta l g i-l i| ≤ |eta| *|g i| := by
  have h := abs_max_sub_max_le_abs (l i-eta*g i) (l i) 0
  have he : max (l i) 0=l i := max_eq_left (hl i)
  simpa only [step,max_comm,he,sub_sub_cancel_left,abs_neg,abs_mul] using h

theorem actual_euclidean_projected_increment_is_bounded
    (eta : ℝ) (l g : Fin m → ℝ) (hl : ∀ i,0 ≤ l i) :
    ‖WithLp.toLp 2 (step eta l g-l)‖ ≤ |eta| *‖WithLp.toLp 2 g‖ := by
  have hs : energy (step eta l g-l) ≤ eta^2*energy g := by
    calc energy (step eta l g-l) ≤ ∑ i,eta^2*(g i)^2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := actual_coordinate_projection_increment_is_bounded eta l g hl i
          change (step eta l g i-l i)^2 ≤ eta^2*(g i)^2
          have he : (|eta| *|g i|)^2=eta^2*(g i)^2 := by rw [mul_pow,sq_abs,sq_abs]
          have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg eta) (abs_nonneg (g i)))).mpr hi
          simpa only [sq_abs,he] using hsq
         _ = eta^2*energy g := by simp [energy,Finset.mul_sum]
  have heL : energy (step eta l g-l)=‖WithLp.toLp 2 (step eta l g-l)‖^2 :=
    actual_euclidean_energy_identity (WithLp.toLp 2 (step eta l g-l))
  have heG : energy g=‖WithLp.toLp 2 g‖^2 :=
    actual_euclidean_energy_identity (WithLp.toLp 2 g)
  rw [heL,heG] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg eta) (norm_nonneg _))).mp
  simpa only [mul_pow,sq_abs] using hs

theorem actual_projected_norm_increment_is_bounded
    (eta B : ℝ) (heta : 0 ≤ eta) (l g : Fin m → ℝ)
    (hl : ∀ i,0 ≤ l i) (hg : ‖WithLp.toLp 2 g‖ ≤ B) :
    |‖WithLp.toLp 2 (step eta l g)‖-‖WithLp.toLp 2 l‖| ≤ eta*B := by
  have hd := abs_norm_sub_norm_le (WithLp.toLp 2 (step eta l g)) (WithLp.toLp 2 l)
  have he : WithLp.toLp 2 (step eta l g)-WithLp.toLp 2 l =
      WithLp.toLp 2 (step eta l g-l) := rfl
  rw [he] at hd
  have hp := actual_euclidean_projected_increment_is_bounded eta l g hl
  rw [abs_of_nonneg heta] at hp
  exact hd.trans (hp.trans (mul_le_mul_of_nonneg_left hg heta))

theorem actual_nonnegative_euclidean_norm_is_bounded_by_coordinate_sum
    (l : Fin m → ℝ) (hl : ∀ i,0 ≤ l i) :
    ‖WithLp.toLp 2 l‖ ≤ ∑ i,l i := by
  have hsum : 0 ≤ ∑ i,l i := Finset.sum_nonneg (fun i _ => hl i)
  have hs : energy l ≤ (∑ i,l i)^2 := by
    unfold energy
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
      have ht := ih (fun i => l i.succ) (fun i => hl i.succ)
      have hn : 0 ≤ ∑ i : Fin m,l i.succ := Finset.sum_nonneg (fun i _ => hl i.succ)
      have htfull := ht hn
      nlinarith [mul_nonneg (hl 0) hn]
  rw [actual_euclidean_energy_identity] at hs
  nlinarith [norm_nonneg (WithLp.toLp 2 l)]

theorem actual_slater_maximizer_has_euclidean_pairing_lower_drift
    (C rChosen rSlater upper : ℝ) (hC : 0 ≤ C)
    (l gChosen gSlater : Fin m → ℝ) (hl : ∀ i,0 ≤ l i)
    (hs : ∀ i,C ≤ gSlater i) (hr : rChosen ≤ upper)
    (hmax : rSlater+pairing l gSlater ≤ rChosen+pairing l gChosen) :
    C*‖WithLp.toLp 2 l‖-(upper-rSlater) ≤ pairing l gChosen := by
  have hp := actual_slater_maximizer_pairing_drift C rChosen rSlater upper
    l gChosen gSlater hl hs hr hmax
  have hn := mul_le_mul_of_nonneg_left
    (actual_nonnegative_euclidean_norm_is_bounded_by_coordinate_sum l hl) hC
  linarith

theorem actual_zero_multiplier_global_maximizer_bounds_every_policy_value
    {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l))) :
    ∀ p : Policy,V p ≤ V (chosen 0) := by
  intro p
  have h := hmax 0 (by intro i; simp) p
  simpa [pairing] using h

theorem actual_global_policy_maximizers_and_slater_derive_the_norm_pairing_drift
    {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy) (C : ℝ) (hC : 0 ≤ C)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l))) :
    0 ≤ V (chosen 0)-V slater ∧
      ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) →
        C*‖WithLp.toLp 2 l‖-(V (chosen 0)-V slater) ≤ pairing l (g (chosen l)) := by
  have hu := actual_zero_multiplier_global_maximizer_bounds_every_policy_value V g chosen hmax
  refine ⟨sub_nonneg.mpr (hu slater),?_⟩
  intro l hl
  exact actual_slater_maximizer_has_euclidean_pairing_lower_drift C
    (V (chosen l)) (V slater) (V (chosen 0)) hC
    l (g (chosen l)) (g slater) hl hslater (hu (chosen l)) (hmax l hl slater)


variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Coordinatewise A3 is converted into conditional pairing for the actual
finite vector. Finite-time bounds derive the required product integrability. -/
theorem actual_coordinate_unbiasedness_derives_integrable_conditional_vector_pairing
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : MeasurableSpace Ω) (hs : s ≤ m0)
    (l g gbar : Ω → Fin m → ℝ)
    (hlmeas : ∀ i, Measurable[s] (fun w => l w i))
    (hgmeas : ∀ i, @Measurable Ω ℝ m0 Real.measurableSpace (fun w => g w i))
    (L B : ℝ) (hlbound : ∀ᵐ w ∂P,∀ i,|l w i| ≤ L)
    (hgbound : ∀ᵐ w ∂P,∀ i,|g w i| ≤ B)
    (hA3 : ∀ i, P[fun w => g w i | s] =ᵐ[P] fun w => gbar w i) :
    Integrable (fun w => pairing (l w) (g w)) P ∧
      P[fun w => pairing (l w) (g w) | s] =ᵐ[P]
        fun w => pairing (l w) (gbar w) := by
  letI : MeasurableSpace Ω := m0
  have hig (i : Fin m) : Integrable (fun w => g w i) P := by
    apply (integrable_const (|B|)).mono' (hgmeas i).aestronglyMeasurable
    filter_upwards [hgbound] with w hw
    exact (hw i).trans (le_abs_self B)
  have hip (i : Fin m) : Integrable (fun w => l w i*g w i) P := by
    apply (integrable_const (|L| * |B|)).mono'
      (((hlmeas i).mono hs le_rfl).mul (hgmeas i)).aestronglyMeasurable
    filter_upwards [hlbound,hgbound] with w hl hg
    change |l w i*g w i| ≤ |L| * |B|
    rw [abs_mul]
    exact mul_le_mul ((hl i).trans (le_abs_self L)) ((hg i).trans (le_abs_self B))
      (abs_nonneg _) (abs_nonneg _)
  have hiPair : Integrable (fun w => pairing (l w) (g w)) P := by
    have hi := integrable_finsetSum' Finset.univ (fun i _ => hip i)
    have he : (∑ i,fun w => l w i*g w i)=(fun w => ∑ i,l w i*g w i) := by
      ext w
      simp only [Finset.sum_apply]
    rw [he] at hi
    simpa only [pairing] using hi
  have hsum : P[fun w => ∑ i,l w i*g w i | s] =ᵐ[P]
      fun w => ∑ i,(P[fun v => l v i*g v i | s]) w := by
    have hc := condExp_finsetSum (s:=Finset.univ) (fun i _ => hip i) s
    have heLeft : (∑ i,fun w => l w i*g w i)=(fun w => ∑ i,l w i*g w i) := by
      ext w
      simp only [Finset.sum_apply]
    have heRight : (∑ i,P[fun w => l w i*g w i | s])=
        (fun w => ∑ i,(P[fun v => l v i*g v i | s]) w) := by
      ext w
      simp only [Finset.sum_apply]
    rw [heLeft,heRight] at hc
    exact hc
  have hp (i : Fin m) : P[fun w => l w i*g w i | s] =ᵐ[P]
      fun w => l w i*(P[fun v => g v i | s]) w :=
    condExp_mul_of_stronglyMeasurable_left (hlmeas i).stronglyMeasurable (hip i) (hig i)
  refine ⟨hiPair,?_⟩
  filter_upwards [hsum,ae_all_iff.mpr hp,ae_all_iff.mpr hA3] with w hw hpw haw
  change (P[fun v => ∑ i,l v i*g v i | s]) w=∑ i,l w i*gbar w i
  rw [hw]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpw i,haw i]

end SafeLearning.CompleteAppliedCMDPProjectedSlaterBridge30

namespace SafeLearning.CompleteAppliedCMDPA1A2A3ProcessBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPProjectedSlaterBridge30
open CompleteAppliedCMDPExponentialBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The multiplier is the actual coordinatewise projected recurrence. Slater,
scalar bounded constraints, global policy maximizers and A3 conditioned only on
the current multiplier derive sublinear growth; no conditional drift, moment,
tail or limit is supplied as a premise. -/
theorem actual_projected_multipliers_from_A1_A2_A3_are_ae_sublinear
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (sample : ℕ → Ω → Fin m → ℝ)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => sample k w) n i))
    (hsamplemeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace
      (fun w => sample n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|sample n w i| ≤ B)
    (hA3 : ∀ n i,P[fun w => sample n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => sample k w) n)) i) :
    ∀ᵐ w ∂P,Tendsto
      (fun n : ℕ => ‖WithLp.toLp 2 (multiplier eta l0 (fun k => sample k w) n)‖/(n:ℝ))
      atTop (nhds 0) := by
  letI : MeasurableSpace Ω := m0
  let l : ℕ → Ω → Fin m → ℝ := fun n w => multiplier eta l0 (fun k => sample k w) n
  let X : ℕ → Ω → ℝ := fun n w => ‖WithLp.toLp 2 (l n w)‖
  let Bv : ℝ := Real.sqrt (m:ℝ)*|B|
  let h : ℝ := eta*(1+Bv)
  let M : ℝ := V (chosen 0)-V slater
  let d : ℝ := eta*C/2
  let R : ℝ := max 1 ((h^2+2*eta*M)/(eta*C))
  have hBv : 0 ≤ Bv := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hh : 0 < h := mul_pos heta (by linarith)
  have hd : 0 < d := by dsimp [d]; positivity
  have hBvSq : Bv^2=(m:ℝ)*B^2 := by
    dsimp [Bv]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg m),sq_abs]
  have hl (n : ℕ) (w : Ω) (i : Fin m) : 0 ≤ l n w i :=
    actual_all_multiplier_coordinates_nonnegative eta l0 hl0 (fun k => sample k w) n i
  have hXm (n : ℕ) : Measurable[s n] (X n) := by
    letI : MeasurableSpace Ω := s n
    have hlm : Measurable (l n) := measurable_pi_iff.mpr (hlmeas n)
    exact ((MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp hlm).norm
  have hnonnegative (n : ℕ) : ∀ᵐ w ∂P,0 ≤ X n w :=
    Eventually.of_forall (fun w => norm_nonneg _)
  have hzero : ∀ᵐ w ∂P,X 0 w ≤ ‖WithLp.toLp 2 l0‖ :=
    Eventually.of_forall (fun w => le_rfl)
  have hnormSample (n : ℕ) : ∀ᵐ w ∂P,‖WithLp.toLp 2 (sample n w)‖ ≤ Bv := by
    filter_upwards [hA2 n] with w hw
    have hb := actual_scalar_violation_bounds_require_the_dimension_factor B (sample n w) hw
    have he := actual_euclidean_energy_identity (WithLp.toLp 2 (sample n w))
    rw [he,← hBvSq] at hb
    exact (sq_le_sq₀ (norm_nonneg _) hBv).mp hb
  have hincrement (n : ℕ) : ∀ᵐ w ∂P,|X (n+1) w-X n w| ≤ h := by
    filter_upwards [hnormSample n] with w hw
    have hp := actual_projected_norm_increment_is_bounded eta Bv heta.le
      (l n w) (sample n w) (hl n w) hw
    change |‖WithLp.toLp 2 (step eta (l n w) (sample n w))‖-‖WithLp.toLp 2 (l n w)‖| ≤ h
    exact hp.trans (by dsimp [h]; nlinarith)
  have hfinite := actual_ae_bounded_process_increments_derive_every_finite_path_bound
    P X ‖WithLp.toLp 2 l0‖ h hzero hincrement
  have hsl := actual_global_policy_maximizers_and_slater_derive_the_norm_pairing_drift
    V g chosen slater C hC.le hslater hmax
  have hnegative (n : ℕ) : ∀ᵐ w ∂P,R ≤ X n w →
      (P[fun v => X (n+1) v-X n v | s n]) w ≤ -d := by
    let Z : Ω → ℝ := fun w => pairing (l n w) (sample n w)
    have hlbound : ∀ᵐ w ∂P,∀ i,|l n w i| ≤ ‖WithLp.toLp 2 l0‖+(n:ℝ)*h := by
      filter_upwards [hfinite n] with w hw i
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 (l n w)) i
      have hc' : |l n w i| ≤ X n w := by simpa only [Real.norm_eq_abs] using hc
      exact hc'.trans hw
    have hp := actual_coordinate_unbiasedness_derives_integrable_conditional_vector_pairing
      P (s n) (hs n) (l n) (sample n) (fun w => g (chosen (l n w)))
      (hlmeas n) (hsamplemeas n) (‖WithLp.toLp 2 l0‖+(n:ℝ)*h) B
      hlbound (hA2 n) (hA3 n)
    have hpairing : ∀ᵐ w ∂P,C*X n w-M ≤ (P[Z | s n]) w := by
      filter_upwards [hp.2] with w hw
      rw [hw]
      exact hsl.2 (l n w) (hl n w)
    have henergy : ∀ᵐ w ∂P,(X (n+1) w)^2 ≤ (X n w)^2+h^2-2*eta*Z w := by
      filter_upwards [hnormSample n] with w hw
      have he := actual_projected_step_energy_bound eta (l n w) (sample n w)
      have hsq := actual_euclidean_violation_bound Bv hBv (WithLp.toLp 2 (sample n w)) hw
      have hLeft : energy (step eta (l n w) (sample n w))=(X (n+1) w)^2 :=
        actual_euclidean_energy_identity (WithLp.toLp 2 (l (n+1) w))
      have hRight : energy (l n w)=(X n w)^2 :=
        actual_euclidean_energy_identity (WithLp.toLp 2 (l n w))
      rw [hLeft,hRight] at he
      have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg eta)
      have hincbound : eta^2*Bv^2 ≤ h^2 := by dsimp [h]; nlinarith [sq_nonneg eta]
      dsimp [Z]
      nlinarith
    exact actual_conditional_projected_energy_and_slater_pairing_derive_negative_norm_drift
      P (s n) (hs n) (X n) (X (n+1)) Z (hXm n)
      ((hXm (n+1)).mono (hs (n+1)) le_rfl) hp.1
      (‖WithLp.toLp 2 l0‖+(n:ℝ)*h) h eta C M hh heta hC
      (hnonnegative n) (hfinite n) (hincrement n) henergy hpairing
  exact actual_current_state_negative_drift_derives_ae_sublinear_norm_growth
    P s hs X hXm ‖WithLp.toLp 2 l0‖ h d R hh hd
    hnonnegative hzero hincrement hnegative

end SafeLearning.CompleteAppliedCMDPA1A2A3ProcessBridge30

namespace SafeLearning.CompleteAppliedCMDPExpectedEpochBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPProjectedSlaterBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

def feasiblePolicyValues {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ) : Set ℝ :=
  V '' {p | ∀ i,0 ≤ g p i}
def feasiblePolicySup {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ) : ℝ :=
  sSup (feasiblePolicyValues V g)

theorem actual_slater_and_zero_multiplier_maximizer_make_feasible_values_nonempty_bounded
    {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (C : ℝ) (hC : 0 ≤ C) (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l))) :
    (feasiblePolicyValues V g).Nonempty ∧ BddAbove (feasiblePolicyValues V g) := by
  have hu := actual_zero_multiplier_global_maximizer_bounds_every_policy_value V g chosen hmax
  refine ⟨⟨V slater,slater,?_,rfl⟩,V (chosen 0),?_⟩
  · intro i
    exact hC.trans (hslater i)
  · rintro b ⟨p,hp,rfl⟩
    exact hu p

theorem actual_feasible_policy_sup_is_bounded_by_each_global_maximizer_lagrangian
    {Policy : Type*} (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (hne : (feasiblePolicyValues V g).Nonempty)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (l : Fin m → ℝ) (hl : ∀ i,0 ≤ l i) :
    feasiblePolicySup V g ≤ V (chosen l)+pairing l (g (chosen l)) := by
  apply csSup_le hne
  rintro b ⟨p,hp,rfl⟩
  have hpair : 0 ≤ pairing l (g p) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (hp i))
  have h := hmax l hl p
  linarith

theorem actual_projected_A2_samples_derive_finite_time_coordinate_bounds
    (P : Measure Ω) (eta B : ℝ) (heta : 0 ≤ eta)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (sample : ℕ → Ω → Fin m → ℝ)
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|sample n w i| ≤ B) :
    ∀ n,∀ᵐ w ∂P,∀ i,
      |multiplier eta l0 (fun k => sample k w) n i| ≤
        ‖WithLp.toLp 2 l0‖+(n:ℝ)*eta*|B| := by
  intro n
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro w i
    simpa only [multiplier,Nat.cast_zero,zero_mul,add_zero,Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 l0) i)
  | succ n ih =>
    filter_upwards [ih,hA2 n] with w hw hs i
    let l := multiplier eta l0 (fun k => sample k w) n
    have hl (j : Fin m) : 0 ≤ l j :=
      actual_all_multiplier_coordinates_nonnegative eta l0 hl0 (fun k => sample k w) n j
    have hp := actual_coordinate_projection_increment_is_bounded eta l (sample n w) hl i
    rw [abs_of_nonneg heta] at hp
    have hgb := mul_le_mul_of_nonneg_left ((hs i).trans (le_abs_self B)) heta
    have ht : |step eta l (sample n w) i| ≤ |step eta l (sample n w) i-l i|+|l i| := by
      simpa only [sub_add_cancel] using abs_add_le (step eta l (sample n w) i-l i) (l i)
    change |step eta l (sample n w) i| ≤ ‖WithLp.toLp 2 l0‖+((n+1:ℕ):ℝ)*eta*|B|
    have hi : |l i| ≤ ‖WithLp.toLp 2 l0‖+(n:ℝ)*eta*|B| := hw i
    push_cast
    linarith

/-- Weak duality uses the actual nonempty feasible-policy cSup. The objective
sample has a well-defined finite expectation and current-multiplier A3.
Projected energy supplies the pairing budget; no near-optimality premise,
strong duality, objective sample bound or switched limit is assumed. -/
theorem actual_projected_energy_A3_and_feasible_policy_sup_derive_expected_epoch_lower_bound
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 ≤ C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (sample : ℕ → Ω → Fin m → ℝ) (objective : ℕ → Ω → ℝ)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => sample k w) n i))
    (hsamplemeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace
      (fun w => sample n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|sample n w i| ≤ B)
    (hA3 : ∀ n i,P[fun w => sample n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => sample k w) n)) i)
    (hiObjective : ∀ n,Integrable (objective n) P)
    (hA3Objective : ∀ n,P[objective n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0 (fun k => sample k w) n)))
    (N : ℕ) (hN : 0 < N) :
    feasiblePolicySup V g-eta*(m:ℝ)*B^2/2-energy l0/(2*eta*(N:ℝ)) ≤
      ∫ w,(∑ n ∈ Finset.range N,objective n w)/(N:ℝ) ∂P := by
  letI : MeasurableSpace Ω := m0
  let l : ℕ → Ω → Fin m → ℝ := fun n w => multiplier eta l0 (fun k => sample k w) n
  let Z : ℕ → Ω → ℝ := fun n w => pairing (l n w) (sample n w)
  let Zbar : ℕ → Ω → ℝ := fun n w => pairing (l n w) (g (chosen (l n w)))
  let W : ℕ → Ω → ℝ := fun n w => V (chosen (l n w))
  let Bv : ℝ := Real.sqrt (m:ℝ)*|B|
  have hBvSq : Bv^2=(m:ℝ)*B^2 := by
    dsimp [Bv]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg m),sq_abs]
  have hl (n : ℕ) (w : Ω) (i : Fin m) : 0 ≤ l n w i :=
    actual_all_multiplier_coordinates_nonnegative eta l0 hl0 (fun k => sample k w) n i
  have hfinite := actual_projected_A2_samples_derive_finite_time_coordinate_bounds
    P eta B heta.le l0 hl0 sample hA2
  have hp (n : ℕ) : Integrable (Z n) P ∧ P[Z n | s n] =ᵐ[P] Zbar n :=
    actual_coordinate_unbiasedness_derives_integrable_conditional_vector_pairing
      P (s n) (hs n) (l n) (sample n) (fun w => g (chosen (l n w)))
      (hlmeas n) (hsamplemeas n) (‖WithLp.toLp 2 l0‖+(n:ℝ)*eta*|B|) B
      (hfinite n) (hA2 n) (hA3 n)
  have hiZbar (n : ℕ) : Integrable (Zbar n) P := integrable_condExp.congr (hp n).2
  have hiW (n : ℕ) : Integrable (W n) P := integrable_condExp.congr (hA3Objective n)
  have hZIntegral (n : ℕ) : (∫ w,Zbar n w ∂P)=∫ w,Z n w ∂P :=
    (integral_congr_ae (hp n).2).symm.trans (integral_condExp (hs n))
  have hWIntegral (n : ℕ) : (∫ w,W n w ∂P)=∫ w,objective n w ∂P :=
    (integral_congr_ae (hA3Objective n)).symm.trans (integral_condExp (hs n))
  have hfeasible := actual_slater_and_zero_multiplier_maximizer_make_feasible_values_nonempty_bounded
    V g chosen slater C hC hslater hmax
  have hweak (n : ℕ) : feasiblePolicySup V g ≤
      (∫ w,objective n w ∂P)+(∫ w,Z n w ∂P) := by
    have hw : ∀ w,feasiblePolicySup V g ≤ W n w+Zbar n w := fun w =>
      actual_feasible_policy_sup_is_bounded_by_each_global_maximizer_lagrangian
        V g chosen hfeasible.1 hmax (l n w) (hl n w)
    have hi := integral_mono_ae (integrable_const (feasiblePolicySup V g))
      ((hiW n).add (hiZbar n)) (Eventually.of_forall hw)
    change (∫ w,feasiblePolicySup V g ∂P) ≤ (∫ w,W n w+Zbar n w ∂P) at hi
    rw [integral_add (hiW n) (hiZbar n)] at hi
    simpa only [integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul,
      hWIntegral n,hZIntegral n] using hi
  have hpairBudget : (∑ n ∈ Finset.range N,∫ w,Z n w ∂P)/(N:ℝ) ≤
      energy l0/(2*eta*(N:ℝ))+eta*(m:ℝ)*B^2/2 := by
    have hpath : ∀ᵐ w ∂P,(∑ n ∈ Finset.range N,Z n w)/(N:ℝ) ≤
        energy l0/(2*eta*(N:ℝ))+eta*(m:ℝ)*B^2/2 := by
      filter_upwards [ae_all_iff.mpr hA2] with w hw
      have henergy (n : ℕ) : energy (sample n w) ≤ Bv^2 := by
        rw [hBvSq]
        exact actual_scalar_violation_bounds_require_the_dimension_factor B (sample n w) (hw n)
      have hb := actual_finite_horizon_complementary_slackness eta Bv heta l0
        (fun k => sample k w) henergy N hN
      simpa only [hBvSq,mul_assoc] using hb
    have hiSum : Integrable (fun w => ∑ n ∈ Finset.range N,Z n w) P := by
      have hi := integrable_finsetSum' (Finset.range N) (fun n _ => (hp n).1)
      have he : (∑ n ∈ Finset.range N,Z n)=(fun w => ∑ n ∈ Finset.range N,Z n w) := by
        ext w
        simp only [Finset.sum_apply]
      rw [he] at hi
      exact hi
    have hi := integral_mono_ae (hiSum.div_const (N:ℝ))
      (integrable_const (energy l0/(2*eta*(N:ℝ))+eta*(m:ℝ)*B^2/2)) hpath
    simpa only [integral_div,integral_finsetSum (Finset.range N) (fun n _ => (hp n).1),
      integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul] using hi
  have hsum := Finset.sum_le_sum (s:=Finset.range N) (fun n _ => hweak n)
  have hsum' : (N:ℝ)*feasiblePolicySup V g ≤
      (∑ n ∈ Finset.range N,∫ w,objective n w ∂P)+(∑ n ∈ Finset.range N,∫ w,Z n w ∂P) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.sum_add_distrib] using hsum
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have havg : feasiblePolicySup V g ≤
      (∑ n ∈ Finset.range N,∫ w,objective n w ∂P)/(N:ℝ)+
        (∑ n ∈ Finset.range N,∫ w,Z n w ∂P)/(N:ℝ) := by
    have ht : feasiblePolicySup V g*(N:ℝ) ≤
        (∑ n ∈ Finset.range N,∫ w,objective n w ∂P)+(∑ n ∈ Finset.range N,∫ w,Z n w ∂P) := by
      simpa only [mul_comm] using hsum'
    have hdivide := (le_div_iff₀ hn).mpr ht
    simpa only [add_div] using hdivide
  rw [integral_div,integral_finsetSum (Finset.range N) (fun n _ => hiObjective n)]
  linarith

end SafeLearning.CompleteAppliedCMDPExpectedEpochBridge30

namespace SafeLearning.CompleteAppliedCMDPActualEpochBridge30
variable {Ω : Type*} [MeasurableSpace Ω]
def epochMean (T : ℕ) (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T,r (k*T+t))/(T:ℝ)
def switchedExpectedAverage (P : Measure Ω) (r : ℕ → Ω → ℝ) (N : ℕ) : ℝ :=
  ∫ w,(∑ t ∈ Finset.range N,r t w)/(N:ℝ) ∂P

theorem actual_epoch_means_are_the_actual_boundary_time_average (T N : ℕ) (r : ℕ → ℝ) :
    (∑ k ∈ Finset.range N,epochMean T r k)/(N:ℝ)=
      (∑ t ∈ Finset.range (N*T),r t)/((N*T:ℕ):ℝ) := by
  have hblocks (N : ℕ) : (∑ t ∈ Finset.range (N*T),r t)=
      ∑ k ∈ Finset.range N,∑ t ∈ Finset.range T,r (k*T+t) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Finset.sum_range_succ,ih]
  unfold epochMean
  rw [← Finset.sum_div,div_div,Nat.cast_mul,hblocks,mul_comm (T:ℝ) (N:ℝ)]

theorem actual_expected_epoch_average_equals_actual_switched_boundary_average
    (P : Measure Ω) (T N : ℕ) (r : ℕ → Ω → ℝ) :
    (∫ w,(∑ k ∈ Finset.range N,epochMean T (fun t => r t w) k)/(N:ℝ) ∂P)=
      switchedExpectedAverage P r (N*T) := by
  unfold switchedExpectedAverage
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => actual_epoch_means_are_the_actual_boundary_time_average T N (fun t => r t w))

end SafeLearning.CompleteAppliedCMDPActualEpochBridge30

namespace SafeLearning.CompleteAppliedCMDPActualEpochBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPExpectedEpochBridge30
open CompleteAppliedCMDPExponentialBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The primitive objective samples are the actual T-step means of r0. The
finite expected bound and the block-sum identity supply the epoch bound. A
finite limit for the ACTUAL switched expected-average sequence is an explicit
background hypothesis, distinct from each fixed-policy value limit. -/
theorem actual_switched_expected_objective_limit_from_projected_A1_A2_A3_is_near_optimal
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 ≤ C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (sample : ℕ → Ω → Fin m → ℝ) (r0 : ℕ → Ω → ℝ)
    (T : ℕ) (hT : 0 < T)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => sample k w) n i))
    (hsamplemeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace
      (fun w => sample n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|sample n w i| ≤ B)
    (hA3 : ∀ n i,P[fun w => sample n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => sample k w) n)) i)
    (hiObjective : ∀ n,Integrable (fun w => epochMean T (fun t => r0 t w) n) P)
    (hA3Objective : ∀ n,P[fun w => epochMean T (fun t => r0 t w) n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0 (fun k => sample k w) n)))
    (L : ℝ)
    (hActualSwitchedLimit : Tendsto (switchedExpectedAverage P r0) atTop (nhds L)) :
    feasiblePolicySup V g-eta*(m:ℝ)*B^2/2 ≤ L := by
  apply actual_switched_expected_average_limit_inherits_the_derived_epoch_lower_bound
    T hT (switchedExpectedAverage P r0) L (feasiblePolicySup V g)
    (eta*(m:ℝ)*B^2/2) (energy l0/(2*eta)) hActualSwitchedLimit
  intro N hN
  have hb := actual_projected_energy_A3_and_feasible_policy_sup_derive_expected_epoch_lower_bound
    P s hs eta C B heta hC l0 hl0 sample (fun n w => epochMean T (fun t => r0 t w) n)
    V g chosen slater hslater hmax hlmeas hsamplemeas hA2 hA3
    hiObjective hA3Objective N hN
  rw [actual_expected_epoch_average_equals_actual_switched_boundary_average] at hb
  simpa only [div_div] using hb

end SafeLearning.CompleteAppliedCMDPActualEpochBridge30

namespace SafeLearning.CompleteAppliedCMDPActualConstraintBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPActualEpochBridge30
variable {m : ℕ}

def timeAverage (r : ℕ → ℝ) (N : ℕ) : ℝ := (∑ t ∈ Finset.range N,r t)/(N:ℝ)

theorem actual_scalar_A2_bounds_each_epoch_mean
    (T : ℕ) (hT : 0 < T) (B : ℝ) (r : ℕ → ℝ)
    (hr : ∀ t,|r t| ≤ B) (k : ℕ) : |epochMean T r k| ≤ B := by
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  unfold epochMean
  rw [abs_div,abs_of_pos ht]
  calc
    |∑ t ∈ Finset.range T,r (k*T+t)|/(T:ℝ) ≤
        (∑ t ∈ Finset.range T,|r (k*T+t)|)/(T:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) ht.le
    _ ≤ ((T:ℝ)*B)/(T:ℝ) := by
      apply div_le_div_of_nonneg_right _ ht.le
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
        (Finset.sum_le_sum (s:=Finset.range T) (fun t _ => hr (k*T+t)))
    _ = B := by field_simp

theorem actual_epoch_means_sum_to_the_full_block_sum
    (T : ℕ) (hT : 0 < T) (K : ℕ) (r : ℕ → ℝ) :
    (T:ℝ)*(∑ k ∈ Finset.range K,epochMean T r k)=∑ t ∈ Finset.range (K*T),r t := by
  have ht : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hblocks (K : ℕ) : (∑ t ∈ Finset.range (K*T),r t)=
      ∑ k ∈ Finset.range K,∑ t ∈ Finset.range T,r (k*T+t) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Finset.sum_range_succ,ih]
  rw [hblocks,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold epochMean
  field_simp

theorem actual_A2_partial_epoch_and_projected_deficit_bound_every_time_sum
    (T : ℕ) (hT : 0 < T) (eta B : ℝ) (heta : 0 < eta)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i) (r : ℕ → Fin m → ℝ)
    (hr : ∀ t i,|r t i| ≤ B) (N : ℕ) (i : Fin m) :
    -(T:ℝ)*‖WithLp.toLp 2 (multiplier eta l0
      (fun k j => epochMean T (fun t => r t j) k) (N/T))‖/eta-(T:ℝ)*|B| ≤
      ∑ t ∈ Finset.range N,r t i := by
  let K := N/T
  let l := multiplier eta l0 (fun k j => epochMean T (fun t => r t j) k) K
  have hd := actual_projected_dual_cumulative_deficit eta l0
    (fun k j => epochMean T (fun t => r t j) k) K i
  have hc : l i ≤ ‖WithLp.toLp 2 l‖ := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 l) i))
  have hsum : -‖WithLp.toLp 2 l‖/eta ≤ ∑ k ∈ Finset.range K,epochMean T (fun t => r t i) k := by
    apply (div_le_iff₀ heta).mpr
    nlinarith [hl0 i]
  have hfull := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg T)
  rw [actual_epoch_means_sum_to_the_full_block_sum T hT K] at hfull
  have htail : -(T:ℝ)*|B| ≤ ∑ t ∈ Finset.range (N%T),r (K*T+t) i := by
    have hs : ∑ t ∈ Finset.range (N%T),- |B| ≤ ∑ t ∈ Finset.range (N%T),r (K*T+t) i :=
      Finset.sum_le_sum (fun t _ => by
        have hb := (hr (K*T+t) i).trans (le_abs_self B)
        exact (abs_le.mp hb).1)
    have hrem : ((N%T:ℕ):ℝ) ≤ T := by exact_mod_cast (Nat.mod_lt N hT).le
    have hm := mul_le_mul_of_nonneg_right hrem (abs_nonneg B)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_neg] at hs
    nlinarith
  have hdecomp : N=K*T+N%T := by
    dsimp [K]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N T).symm
  have he : (∑ t ∈ Finset.range N,r t i)=
      (∑ t ∈ Finset.range (K*T),r t i)+(∑ t ∈ Finset.range (N%T),r (K*T+t) i) := by
    conv_lhs => rw [hdecomp]
    rw [Finset.sum_range_add]
  rw [he]
  change -(T:ℝ)*‖WithLp.toLp 2 l‖/eta-(T:ℝ)*|B| ≤ _
  have heq : (T:ℝ)*(-‖WithLp.toLp 2 l‖/eta)=-(T:ℝ)*‖WithLp.toLp 2 l‖/eta := by ring
  rw [heq] at hfull
  linarith

theorem actual_centered_time_average_identity
    (r : ℕ → ℝ) (c : ℝ) (N : ℕ) (hN : 0 < N) :
    timeAverage (fun t => r t-c) N=timeAverage r N-c := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold timeAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp

/-- Actual bounded instantaneous constraints control every partial epoch. The
multiplier limit is used here as a component; the stochastic A1--A3 assembly
below derives it rather than assuming it for the full CMDP conclusion. -/
theorem actual_partial_epoch_bound_and_sublinear_projected_multipliers_imply_all_time_feasibility
    (T : ℕ) (hT : 0 < T) (eta B : ℝ) (heta : 0 < eta)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (r : ℕ → Fin m → ℝ) (c : Fin m → ℝ)
    (hr : ∀ t i,|r t i-c i| ≤ B)
    (hgrowth : Tendsto (fun k : ℕ => ‖WithLp.toLp 2 (multiplier eta l0
      (fun k j => epochMean T (fun t => r t j-c j) k) k)‖/(k:ℝ)) atTop (nhds 0))
    (i : Fin m) : c i ≤ Filter.liminf (timeAverage (fun t => r t i)) atTop := by
  let a : ℕ → ℝ := timeAverage (fun t => r t i)
  have hbound : ∀ᶠ N : ℕ in atTop,c i-B ≤ a N ∧ a N ≤ c i+B := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hb := actual_scalar_A2_bounds_each_epoch_mean N hN B
      (fun t => r t i-c i) (fun t => hr t i) 0
    have he : epochMean N (fun t => r t i-c i) 0=timeAverage (fun t => r t i-c i) N := by
      simp only [epochMean,timeAverage,zero_mul,zero_add]
    rw [he,actual_centered_time_average_identity _ _ N hN] at hb
    exact ⟨by linarith [(abs_le.mp hb).1],by linarith [(abs_le.mp hb).2]⟩
  have hupper : atTop.IsBoundedUnder (· ≤ ·) a := ⟨c i+B,hbound.mono (fun N h => h.2)⟩
  have hlower : atTop.IsBoundedUnder (· ≥ ·) a := ⟨c i-B,hbound.mono (fun N h => h.1)⟩
  apply (le_liminf_iff' hupper.isCoboundedUnder_ge hlower).mpr
  intro y hy
  have hfloor : Tendsto (fun N : ℕ => N/T) atTop atTop := le_of_eq (map_div_atTop_eq_nat T hT)
  have hfrac := hgrowth.comp hfloor
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖WithLp.toLp 2 (multiplier eta l0
        (fun k j => epochMean T (fun t => r t j-c j) k) (N/T))‖/((N/T:ℕ):ℝ)<(c i-y)*eta/2 :=
    hfrac.eventually (gt_mem_nhds (by nlinarith : (0:ℝ)<(c i-y)*eta/2))
  have htail : ∀ᶠ N : ℕ in atTop,(T:ℝ)*|B|/(N:ℝ)<(c i-y)/2 :=
    (tendsto_const_div_atTop_nhds_zero_nat ((T:ℝ)*|B|)).eventually
      (gt_mem_nhds (by linarith : (0:ℝ)<(c i-y)/2))
  have hpositive : ∀ᶠ N : ℕ in atTop,0 < N/T := hfloor.eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall,htail,hpositive,eventually_gt_atTop 0] with N hs ht hk hN
  let K := N/T
  let L := ‖WithLp.toLp 2 (multiplier eta l0
    (fun k j => epochMean T (fun t => r t j-c j) k) K)‖
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hkr : (0:ℝ)<K := by exact_mod_cast hk
  have hkn : (K:ℝ)*(T:ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N T
  have hscaled : (T:ℝ)*L/(N:ℝ) ≤ L/(K:ℝ) := by
    apply (div_le_div_iff₀ hn hkr).mpr
    nlinarith [norm_nonneg (WithLp.toLp 2 (multiplier eta l0
      (fun k j => epochMean T (fun t => r t j-c j) k) K))]
  have hmain : (T:ℝ)*L/(eta*(N:ℝ))<(c i-y)/2 := by
    have hq := (div_lt_iff₀ heta).mpr (show L/(K:ℝ)<((c i-y)/2)*eta by
      simpa only [mul_div_assoc,mul_comm,mul_left_comm,mul_assoc] using hs)
    have hm := div_le_div_of_nonneg_right hscaled heta.le
    have he : ((T:ℝ)*L/(N:ℝ))/eta=(T:ℝ)*L/(eta*(N:ℝ)) := by ring
    rw [he] at hm
    exact hm.trans_lt hq
  have hb := actual_A2_partial_epoch_and_projected_deficit_bound_every_time_sum
    T hT eta B heta l0 hl0 (fun t j => r t j-c j) hr N i
  have havg := div_le_div_of_nonneg_right hb hn.le
  have he : (-(T:ℝ)*L/eta-(T:ℝ)*|B|)/(N:ℝ)=
      -(T:ℝ)*L/(eta*(N:ℝ))-(T:ℝ)*|B|/(N:ℝ) := by ring
  change (-(T:ℝ)*L/eta-(T:ℝ)*|B|)/(N:ℝ) ≤ timeAverage (fun t => r t i-c i) N at havg
  rw [he,actual_centered_time_average_identity _ _ N hN] at havg
  change y ≤ timeAverage (fun t => r t i) N
  simp only [neg_mul,neg_div] at havg
  linarith

end SafeLearning.CompleteAppliedCMDPActualConstraintBridge30

namespace SafeLearning.CompleteAppliedCMDPActualConstraintBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPActualEpochBridge30
open CompleteAppliedCMDPA1A2A3ProcessBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

def actualConstraintEpochSample (T : ℕ) (r : ℕ → Ω → Fin m → ℝ) (c : Fin m → ℝ)
    (k : ℕ) (w : Ω) (i : Fin m) : ℝ := epochMean T (fun t => r t w i-c i) k

/-- The rewards and multipliers are the actual instantaneous trajectory and
projected epoch recurrence. Strict Slater, global policy maximizers, scalar A2
on instantaneous constraints and current-multiplier A3 derive feasibility for
EVERY time horizon almost surely. No multiplier limit, moment/tail bound,
feasibility limit, independence or filtration nesting is a premise. -/
theorem actual_instantaneous_A2_and_projected_A1_A3_derive_ae_all_time_constraint_feasibility
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (T : ℕ) (hT : 0 < T) (r : ℕ → Ω → Fin m → ℝ) (c : Fin m → ℝ)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n i))
    (hrmeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace (fun w => r n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|r n w i-c i| ≤ B)
    (hA3 : ∀ n i,P[fun w => actualConstraintEpochSample T r c n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n)) i) :
    ∀ᵐ w ∂P,∀ i,c i ≤ Filter.liminf (timeAverage (fun t => r t w i)) atTop := by
  letI : MeasurableSpace Ω := m0
  let sample := actualConstraintEpochSample T r c
  have hmeas (k : ℕ) (i : Fin m) : Measurable (fun w => sample k w i) := by
    unfold sample actualConstraintEpochSample epochMean
    exact ((Finset.range T).measurable_sum
      (fun t _ => (hrmeas (k*T+t) i).sub_const (c i))).div_const (T:ℝ)
  have hsampleBound (k : ℕ) : ∀ᵐ w ∂P,∀ i,|sample k w i| ≤ B := by
    filter_upwards [ae_all_iff.mpr hA2] with w hw i
    exact actual_scalar_A2_bounds_each_epoch_mean T hT B (fun t => r t w i-c i)
      (fun t => hw t i) k
  have hg := actual_projected_multipliers_from_A1_A2_A3_are_ae_sublinear
    P s hs eta C B heta hC l0 hl0 sample V g chosen slater hslater hmax
    hlmeas hmeas hsampleBound hA3
  filter_upwards [hg,ae_all_iff.mpr hA2] with w hw hb i
  exact actual_partial_epoch_bound_and_sublinear_projected_multipliers_imply_all_time_feasibility
    T hT eta B heta l0 hl0 (fun t => r t w) c hb hw i

end SafeLearning.CompleteAppliedCMDPActualConstraintBridge30

namespace SafeLearning.CompleteAppliedCMDPExpectedEpochBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPProjectedSlaterBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Global maximization at zero bounds policy VALUES. Objective A3 and the
conditional tower identity transfer this bound to expected epoch rewards;
individual instantaneous objective samples need not be bounded. -/
theorem actual_zero_multiplier_argmax_and_objective_A3_bound_all_expected_epoch_averages
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (l : ℕ → Ω → Fin m → ℝ) (objective : ℕ → Ω → ℝ)
    (hiObjective : ∀ n,Integrable (objective n) P)
    (hA3Objective : ∀ n,P[objective n | s n] =ᵐ[P] fun w => V (chosen (l n w)))
    (N : ℕ) (hN : 0 < N) :
    (∫ w,(∑ n ∈ Finset.range N,objective n w)/(N:ℝ) ∂P) ≤ V (chosen 0) := by
  have hu := actual_zero_multiplier_global_maximizer_bounds_every_policy_value V g chosen hmax
  have hper (n : ℕ) : (∫ w,objective n w ∂P) ≤ V (chosen 0) := by
    have hiV : Integrable (fun w => V (chosen (l n w))) P :=
      integrable_condExp.congr (hA3Objective n)
    have he : (∫ w,V (chosen (l n w)) ∂P)=∫ w,objective n w ∂P :=
      (integral_congr_ae (hA3Objective n)).symm.trans (integral_condExp (hs n))
    have hb := integral_mono_ae hiV (integrable_const (V (chosen 0)))
      (Eventually.of_forall (fun w => hu (chosen (l n w))))
    rw [he] at hb
    simpa only [integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul] using hb
  rw [integral_div,integral_finsetSum (Finset.range N) (fun n _ => hiObjective n)]
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  apply (div_le_iff₀ hn).mpr
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm] using
    (Finset.sum_le_sum (s:=Finset.range N) (fun n _ => hper n))

end SafeLearning.CompleteAppliedCMDPExpectedEpochBridge30

namespace SafeLearning.CompleteAppliedCMDPActualEpochBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPExpectedEpochBridge30
open CompleteAppliedCMDPExponentialBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- A finite limit of the actual switched sequence is NOT needed at epoch
boundaries. Weak duality and projected energy derive the lower estimate;
zero-multiplier maximality and A3 derive the upper boundedness needed for the
real liminf. No desired limiting reward is assumed. -/
theorem actual_derived_epoch_boundary_expected_objective_liminf_is_near_optimal
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 ≤ C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (sample : ℕ → Ω → Fin m → ℝ) (r0 : ℕ → Ω → ℝ)
    (T : ℕ) (hT : 0 < T)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => sample k w) n i))
    (hsamplemeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace
      (fun w => sample n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|sample n w i| ≤ B)
    (hA3 : ∀ n i,P[fun w => sample n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => sample k w) n)) i)
    (hiObjective : ∀ n,Integrable (fun w => epochMean T (fun t => r0 t w) n) P)
    (hA3Objective : ∀ n,P[fun w => epochMean T (fun t => r0 t w) n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0 (fun k => sample k w) n)))
    : feasiblePolicySup V g-eta*(m:ℝ)*B^2/2 ≤
      Filter.liminf (fun N : ℕ => switchedExpectedAverage P r0 (N*T)) atTop := by
  let a : ℕ → ℝ := fun N => switchedExpectedAverage P r0 (N*T)
  let Lbound := feasiblePolicySup V g-eta*(m:ℝ)*B^2/2
  let coeff := energy l0/(2*eta)
  have hcoeff : 0 ≤ coeff := div_nonneg
    (Finset.sum_nonneg (fun i _ => sq_nonneg (l0 i))) (by positivity)
  have hfinite (N : ℕ) (hN : 0 < N) : Lbound-coeff/(N:ℝ) ≤ a N := by
    have hb := actual_projected_energy_A3_and_feasible_policy_sup_derive_expected_epoch_lower_bound
      P s hs eta C B heta hC l0 hl0 sample (fun n w => epochMean T (fun t => r0 t w) n)
      V g chosen slater hslater hmax hlmeas hsamplemeas hA2 hA3
      hiObjective hA3Objective N hN
    rw [actual_expected_epoch_average_equals_actual_switched_boundary_average] at hb
    simpa only [Lbound,coeff,a,div_div] using hb
  have hupper : atTop.IsBoundedUnder (· ≤ ·) a := by
    refine ⟨V (chosen 0),?_⟩
    change ∀ᶠ N : ℕ in atTop,a N ≤ V (chosen 0)
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hb := actual_zero_multiplier_argmax_and_objective_A3_bound_all_expected_epoch_averages
      P s hs V g chosen hmax (fun n w => multiplier eta l0 (fun k => sample k w) n)
      (fun n w => epochMean T (fun t => r0 t w) n) hiObjective hA3Objective N hN
    rw [actual_expected_epoch_average_equals_actual_switched_boundary_average] at hb
    exact hb
  have hlower : atTop.IsBoundedUnder (· ≥ ·) a := by
    refine ⟨Lbound-coeff,?_⟩
    change ∀ᶠ N : ℕ in atTop,Lbound-coeff ≤ a N
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hb : coeff/(N:ℝ) ≤ coeff := div_le_self hcoeff hn
    exact (by linarith : Lbound-coeff ≤ Lbound-coeff/(N:ℝ)).trans (hfinite N hN)
  apply (le_liminf_iff' hupper.isCoboundedUnder_ge hlower).mpr
  intro y hy
  have hlow : Tendsto (fun N : ℕ => Lbound-coeff/(N:ℝ)) atTop (nhds Lbound) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat coeff)
  filter_upwards [hlow.eventually (lt_mem_nhds hy),eventually_gt_atTop 0] with N hlowN hN
  exact hlowN.le.trans (hfinite N hN)

end SafeLearning.CompleteAppliedCMDPActualEpochBridge30

namespace SafeLearning.CompleteAppliedCMDPActualConstraintBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPActualEpochBridge30
open CompleteAppliedCMDPExpectedEpochBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The complete actual projected CMDP route. All-time constraint feasibility
and epoch-boundary objective liminf are derived from A1--A3 with finite epoch
objective expectations. The all-time expected objective bound is conditional
on a finite limit of that ACTUAL switched expected-average sequence. Constraint
A2 is never used as a bound on individual objective samples. -/
theorem actual_projected_CMDP_A1_A2_A3_gives_feasibility_and_qualified_near_optimality
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (T : ℕ) (hT : 0 < T) (r : ℕ → Ω → Fin m → ℝ) (c : Fin m → ℝ)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n i))
    (hrmeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace (fun w => r n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|r n w i-c i| ≤ B)
    (hA3 : ∀ n i,P[fun w => actualConstraintEpochSample T r c n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n)) i)
    (r0 : ℕ → Ω → ℝ)
    (hiObjective : ∀ n,Integrable (fun w => epochMean T (fun t => r0 t w) n) P)
    (hA3Objective : ∀ n,P[fun w => epochMean T (fun t => r0 t w) n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n))) :
    (∀ᵐ w ∂P,∀ i,c i ≤ Filter.liminf (timeAverage (fun t => r t w i)) atTop) ∧
    (feasiblePolicySup V g-eta*(m:ℝ)*B^2/2 ≤
      Filter.liminf (fun N : ℕ => switchedExpectedAverage P r0 (N*T)) atTop) ∧
    (∀ L : ℝ,Tendsto (switchedExpectedAverage P r0) atTop (nhds L) →
      feasiblePolicySup V g-eta*(m:ℝ)*B^2/2 ≤ L) := by
  letI : MeasurableSpace Ω := m0
  let sample := actualConstraintEpochSample T r c
  have hmeas (k : ℕ) (i : Fin m) : Measurable (fun w => sample k w i) := by
    unfold sample actualConstraintEpochSample epochMean
    exact ((Finset.range T).measurable_sum
      (fun t _ => (hrmeas (k*T+t) i).sub_const (c i))).div_const (T:ℝ)
  have hsampleBound (k : ℕ) : ∀ᵐ w ∂P,∀ i,|sample k w i| ≤ B := by
    filter_upwards [ae_all_iff.mpr hA2] with w hw i
    exact actual_scalar_A2_bounds_each_epoch_mean T hT B (fun t => r t w i-c i)
      (fun t => hw t i) k
  refine ⟨actual_instantaneous_A2_and_projected_A1_A3_derive_ae_all_time_constraint_feasibility
    P s hs eta C B heta hC l0 hl0 T hT r c V g chosen slater hslater hmax
    hlmeas hrmeas hA2 hA3,?_,?_⟩
  · exact actual_derived_epoch_boundary_expected_objective_liminf_is_near_optimal
      P s hs eta C B heta hC.le l0 hl0 sample r0 T hT V g chosen slater
      hslater hmax hlmeas hmeas hsampleBound hA3 hiObjective hA3Objective
  · intro L hActualSwitchedLimit
    exact actual_switched_expected_objective_limit_from_projected_A1_A2_A3_is_near_optimal
      P s hs eta C B heta hC.le l0 hl0 sample r0 T hT V g chosen slater
      hslater hmax hlmeas hmeas hsampleBound hA3 hiObjective hA3Objective L hActualSwitchedLimit

end SafeLearning.CompleteAppliedCMDPActualConstraintBridge30

namespace SafeLearning.CompleteAppliedCMDPActualConstraintBridge30
open CompleteAppliedCMDPActualEpochBridge30
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Bounded INSTANTANEOUS objective samples control unfinished epochs. This
hypothesis is separate from the constraint-only A2. -/
theorem actual_bounded_scalar_rewards_control_all_partial_epoch_average_errors
    (T : ℕ) (hT : 0 < T) (B : ℝ) (r : ℕ → ℝ) (hr : ∀ t,|r t| ≤ B)
    (N : ℕ) (hN : 0 < N) (hK : 0 < N/T) :
    |timeAverage r N-timeAverage r ((N/T)*T)| ≤ 2*(T:ℝ)*B/(N:ℝ) := by
  let K := N/T
  let Q := K*T
  let J := N%T
  have hQ : 0 < Q := Nat.mul_pos hK hT
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hb : 0 ≤ B := (abs_nonneg (r 0)).trans (hr 0)
  have hdecomp : N=Q+J := by
    dsimp [Q,K,J]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N T).symm
  have hNr : (N:ℝ)=(Q:ℝ)+(J:ℝ) := by exact_mod_cast hdecomp
  have hsplit : (∑ t ∈ Finset.range N,r t)=
      (∑ t ∈ Finset.range Q,r t)+(∑ t ∈ Finset.range J,r (Q+t)) := by
    conv_lhs => rw [hdecomp]
    rw [Finset.sum_range_add]
  have ha : |timeAverage r Q| ≤ B := by
    simpa only [epochMean,timeAverage,zero_mul,zero_add] using
      (actual_scalar_A2_bounds_each_epoch_mean Q hQ B r hr 0)
  have htail : |∑ t ∈ Finset.range J,r (Q+t)| ≤ (J:ℝ)*B := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
        (Finset.sum_le_sum (s:=Finset.range J) (fun t _ => hr (Q+t))))
  have he : timeAverage r N-timeAverage r Q=
      ((∑ t ∈ Finset.range J,r (Q+t))-(J:ℝ)*timeAverage r Q)/(N:ℝ) := by
    unfold timeAverage
    rw [hsplit]
    field_simp
    rw [hNr]
    ring
  rw [show (N/T)*T=Q from rfl,he,abs_div,abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  have hmul : |(J:ℝ)*timeAverage r Q| ≤ (J:ℝ)*B := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg J)]
    exact mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg J)
  have ht : |(∑ t ∈ Finset.range J,r (Q+t))-(J:ℝ)*timeAverage r Q| ≤
      |∑ t ∈ Finset.range J,r (Q+t)|+|(J:ℝ)*timeAverage r Q| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      (abs_add_le (∑ t ∈ Finset.range J,r (Q+t)) (-((J:ℝ)*timeAverage r Q)))
  have hj : (J:ℝ) ≤ T := by exact_mod_cast (Nat.mod_lt N hT).le
  nlinarith

/-- The pointwise unfinished-epoch bound transfers to the actual expected
averages only after bounded measurable instantaneous objectives establish all
integrability obligations. -/
theorem actual_measurable_bounded_objectives_control_expected_partial_epoch_errors
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ) (hT : 0 < T)
    (B : ℝ) (r : ℕ → Ω → ℝ) (hrmeas : ∀ t,Measurable (r t))
    (hr : ∀ t,∀ᵐ w ∂P,|r t w| ≤ B)
    (N : ℕ) (hN : 0 < N) (hK : 0 < N/T) :
    |switchedExpectedAverage P r N-switchedExpectedAverage P r ((N/T)*T)| ≤
      2*(T:ℝ)*B/(N:ℝ) := by
  have hi (t : ℕ) : Integrable (r t) P := by
    apply (integrable_const B).mono' (hrmeas t).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hr t
  have hiAverage (K : ℕ) : Integrable (fun w => timeAverage (fun t => r t w) K) P := by
    exact ((integrable_finsetSum (Finset.range K) (fun t _ => hi t))).div_const (K:ℝ)
  let Q := (N/T)*T
  let error := 2*(T:ℝ)*B/(N:ℝ)
  have hpoint : ∀ᵐ w ∂P,|timeAverage (fun t => r t w) N-timeAverage (fun t => r t w) Q| ≤ error := by
    filter_upwards [ae_all_iff.mpr hr] with w hw
    exact actual_bounded_scalar_rewards_control_all_partial_epoch_average_errors T hT B
      (fun t => r t w) hw N hN hK
  have hip := (hiAverage N).sub (hiAverage Q)
  have hup := integral_mono_ae hip (integrable_const error) (hpoint.mono (fun w h => (abs_le.mp h).2))
  have hlo := integral_mono_ae (integrable_const (-error)) hip (hpoint.mono (fun w h => (abs_le.mp h).1))
  change (∫ w,timeAverage (fun t => r t w) N-timeAverage (fun t => r t w) Q ∂P) ≤
    (∫ _w : Ω,error ∂P) at hup
  change (∫ _w : Ω,-error ∂P) ≤
    (∫ w,timeAverage (fun t => r t w) N-timeAverage (fun t => r t w) Q ∂P) at hlo
  rw [integral_sub (hiAverage N) (hiAverage Q)] at hup hlo
  simp only [integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul] at hup hlo
  exact abs_le.mpr ⟨hlo,hup⟩

end SafeLearning.CompleteAppliedCMDPActualConstraintBridge30

namespace SafeLearning.CompleteAppliedCMDPActualConstraintBridge30
open CompleteCoreProjectedDualDrift29
open CompleteAppliedCMDPActualEpochBridge30
open CompleteAppliedCMDPExpectedEpochBridge30
variable {m : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Additional bounded INSTANTANEOUS objective samples supply the genuine
partial-epoch control missing from constraint A2. Under this extra hypothesis,
all-time expected objective liminf is derived without switched-limit existence.
The monitoring objective, an indicator, has this separate boundedness property. -/
theorem actual_projected_CMDP_with_bounded_objective_gives_ae_feasibility_and_all_time_expected_near_optimality
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C B : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin m → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (T : ℕ) (hT : 0 < T) (r : ℕ → Ω → Fin m → ℝ) (c : Fin m → ℝ)
    (V : Policy → ℝ) (g : Policy → Fin m → ℝ)
    (chosen : (Fin m → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin m → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n i))
    (hrmeas : ∀ n i,@Measurable Ω ℝ m0 Real.measurableSpace (fun w => r n w i))
    (hA2 : ∀ n,∀ᵐ w ∂P,∀ i,|r n w i-c i| ≤ B)
    (hA3 : ∀ n i,P[fun w => actualConstraintEpochSample T r c n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n)) i)
    (r0 : ℕ → Ω → ℝ)
    (B0 : ℝ) (hr0meas : ∀ t,@Measurable Ω ℝ m0 Real.measurableSpace (r0 t))
    (hObjectiveBound : ∀ t,∀ᵐ w ∂P,|r0 t w| ≤ B0)
    (hA3Objective : ∀ n,P[fun w => epochMean T (fun t => r0 t w) n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0 (fun k => actualConstraintEpochSample T r c k w) n))) :
    (∀ᵐ w ∂P,∀ i,c i ≤ Filter.liminf (timeAverage (fun t => r t w i)) atTop) ∧
    (feasiblePolicySup V g-eta*(m:ℝ)*B^2/2 ≤
      Filter.liminf (switchedExpectedAverage P r0) atTop) := by
  letI : MeasurableSpace Ω := m0
  let sample := actualConstraintEpochSample T r c
  have hmeas (k : ℕ) (i : Fin m) : Measurable (fun w => sample k w i) := by
    unfold sample actualConstraintEpochSample epochMean
    exact ((Finset.range T).measurable_sum
      (fun t _ => (hrmeas (k*T+t) i).sub_const (c i))).div_const (T:ℝ)
  have hsampleBound (k : ℕ) : ∀ᵐ w ∂P,∀ i,|sample k w i| ≤ B := by
    filter_upwards [ae_all_iff.mpr hA2] with w hw i
    exact actual_scalar_A2_bounds_each_epoch_mean T hT B (fun t => r t w i-c i)
      (fun t => hw t i) k
  have hiR0 (t : ℕ) : Integrable (r0 t) P := by
    apply (integrable_const B0).mono' (hr0meas t).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hObjectiveBound t
  have hiObjective (k : ℕ) : Integrable (fun w => epochMean T (fun t => r0 t w) k) P := by
    exact (integrable_finsetSum (Finset.range T) (fun t _ => hiR0 (k*T+t))).div_const (T:ℝ)
  refine ⟨actual_instantaneous_A2_and_projected_A1_A3_derive_ae_all_time_constraint_feasibility
    P s hs eta C B heta hC l0 hl0 T hT r c V g chosen slater hslater hmax
    hlmeas hrmeas hA2 hA3,?_⟩
  let a : ℕ → ℝ := switchedExpectedAverage P r0
  let Lbound := feasiblePolicySup V g-eta*(m:ℝ)*B^2/2
  let coeff := energy l0/(2*eta)
  have hiAverage (N : ℕ) : Integrable (fun w => timeAverage (fun t => r0 t w) N) P := by
    exact (integrable_finsetSum (Finset.range N) (fun t _ => hiR0 t)).div_const (N:ℝ)
  have hbounded (N : ℕ) (hN : 0 < N) : -B0 ≤ a N ∧ a N ≤ B0 := by
    have hpoint : ∀ᵐ w ∂P,|timeAverage (fun t => r0 t w) N| ≤ B0 := by
      filter_upwards [ae_all_iff.mpr hObjectiveBound] with w hw
      simpa only [epochMean,timeAverage,zero_mul,zero_add] using
        (actual_scalar_A2_bounds_each_epoch_mean N hN B0 (fun t => r0 t w) hw 0)
    have hl := integral_mono_ae (integrable_const (-B0)) (hiAverage N)
      (hpoint.mono (fun w h => (abs_le.mp h).1))
    have hu := integral_mono_ae (hiAverage N) (integrable_const B0)
      (hpoint.mono (fun w h => (abs_le.mp h).2))
    simp only [integral_const,probReal_univ,one_smul,smul_eq_mul,one_mul] at hl hu
    exact ⟨hl,hu⟩
  have hupper : atTop.IsBoundedUnder (· ≤ ·) a :=
    ⟨B0,(eventually_gt_atTop 0).mono (fun N hN => (hbounded N hN).2)⟩
  have hlower : atTop.IsBoundedUnder (· ≥ ·) a :=
    ⟨-B0,(eventually_gt_atTop 0).mono (fun N hN => (hbounded N hN).1)⟩
  have hfinite (K : ℕ) (hK : 0 < K) : Lbound-coeff/(K:ℝ) ≤ a (K*T) := by
    have hb := actual_projected_energy_A3_and_feasible_policy_sup_derive_expected_epoch_lower_bound
      P s hs eta C B heta hC.le l0 hl0 sample (fun n w => epochMean T (fun t => r0 t w) n)
      V g chosen slater hslater hmax hlmeas hmeas hsampleBound hA3
      hiObjective hA3Objective K hK
    rw [actual_expected_epoch_average_equals_actual_switched_boundary_average] at hb
    simpa only [Lbound,coeff,a,div_div] using hb
  have hfloor : Tendsto (fun N : ℕ => N/T) atTop atTop := le_of_eq (map_div_atTop_eq_nat T hT)
  have hlow : Tendsto (fun N : ℕ => Lbound-coeff/((N/T:ℕ):ℝ)-2*(T:ℝ)*B0/(N:ℝ))
      atTop (nhds Lbound) := by
    have hc := (tendsto_const_div_atTop_nhds_zero_nat coeff).comp hfloor
    have he := tendsto_const_div_atTop_nhds_zero_nat (2*(T:ℝ)*B0)
    simpa only [sub_zero,Function.comp_def] using (tendsto_const_nhds.sub hc).sub he
  apply (le_liminf_iff' hupper.isCoboundedUnder_ge hlower).mpr
  intro y hy
  filter_upwards [hlow.eventually (lt_mem_nhds hy),eventually_gt_atTop 0,
    hfloor.eventually (eventually_gt_atTop 0)] with N hlowN hN hK
  have hrem := actual_measurable_bounded_objectives_control_expected_partial_epoch_errors
    P T hT B0 r0 hr0meas hObjectiveBound N hN hK
  have hl := (abs_le.mp hrem).1
  have hb := hfinite (N/T) hK
  change - (2*(T:ℝ)*B0/(N:ℝ)) ≤ a N-a ((N/T)*T) at hl
  exact hlowN.le.trans (by linarith : Lbound-coeff/((N/T:ℕ):ℝ)-2*(T:ℝ)*B0/(N:ℝ) ≤ a N)

end SafeLearning.CompleteAppliedCMDPActualConstraintBridge30


namespace SafeLearning.CompleteAppliedMonitoringCMDPBounded55
open CompleteAppliedCMDPActualEpochBridge30 CompleteAppliedCMDPExpectedEpochBridge30
open Set Filter MeasureTheory
open CompleteCoreProjectedDualDrift29 CompleteAppliedCMDPA1A2A3ProcessBridge30
open CompleteAppliedCMDPActualConstraintBridge30
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The actual monitoring reward is the indicator of the visited physical region. -/
def monitoringIndicator (state : ℕ → Ω → Fin 3) (target : Fin 3)
    (t : ℕ) (w : Ω) : ℝ := if state t w=target then 1 else 0

theorem actual_monitoring_visit_indicator_is_measurable
    (state : ℕ → Ω → Fin 3) (target : Fin 3) (t : ℕ)
    (hstate : Measurable (state t)) : Measurable (monitoringIndicator state target t) := by
  unfold monitoringIndicator
  exact measurable_const.ite (measurableSet_eq_fun hstate measurable_const) measurable_const

theorem actual_monitoring_constraint_indicators_have_the_primitive_scalar_A2_bound
    (state : ℕ → Ω → Fin 3) (t : ℕ) (w : Ω) (i : Fin 2) :
    |monitoringIndicator state i.succ t w-(1/3:ℝ)| ≤ 2/3 := by
  unfold monitoringIndicator
  split_ifs <;> norm_num

theorem actual_monitoring_objective_indicator_has_a_separate_primitive_absolute_bound
    (state : ℕ → Ω → Fin 3) (t : ℕ) (w : Ω) :
    |monitoringIndicator state 0 t w| ≤ 1 := by
  unfold monitoringIndicator
  split_ifs <;> norm_num

/-- A3 remains an explicit current-multiplier conditional mean assumption.
The actual physical indicator rewards derive constraint A2 and the separate
objective bound needed for EVERY-time expected near-optimality. This theorem
does not assert unbiasedness of the concrete deterministic switching cycle. -/
theorem actual_monitoring_indicator_rewards_and_projected_A1_A3_give_every_time_guarantees
    {Policy : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin 2 → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (T : ℕ) (hT : 0 < T) (state : ℕ → Ω → Fin 3)
    (hstatemeas : ∀ t,Measurable (state t))
    (V : Policy → ℝ) (g : Policy → Fin 2 → ℝ)
    (chosen : (Fin 2 → ℝ) → Policy) (slater : Policy)
    (hslater : ∀ i,C ≤ g slater i)
    (hmax : ∀ l : Fin 2 → ℝ,(∀ i,0 ≤ l i) → ∀ p : Policy,
      V p+pairing l (g p) ≤ V (chosen l)+pairing l (g (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n i))
    (hA3 : ∀ n i,P[fun w => actualConstraintEpochSample T
      (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) n w i | s n] =ᵐ[P]
      fun w => g (chosen (multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n)) i)
    (hA3Objective : ∀ n,P[fun w => epochMean T
      (fun t => monitoringIndicator state 0 t w) n | s n] =ᵐ[P]
      fun w => V (chosen (multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n))) :
    (∀ᵐ w ∂P,∀ i : Fin 2,(1/3:ℝ) ≤
      Filter.liminf (timeAverage (fun t => monitoringIndicator state i.succ t w)) atTop) ∧
    (feasiblePolicySup V g-4*eta/9 ≤
      Filter.liminf (switchedExpectedAverage P (monitoringIndicator state 0)) atTop) := by
  have hconstraints := actual_projected_CMDP_with_bounded_objective_gives_ae_feasibility_and_all_time_expected_near_optimality
    P s hs eta C (2/3) heta hC l0 hl0 T hT
    (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ))
    V g chosen slater hslater hmax hlmeas
    (fun t i => actual_monitoring_visit_indicator_is_measurable state i.succ t (hstatemeas t))
    (fun t => Eventually.of_forall (fun w i =>
      actual_monitoring_constraint_indicators_have_the_primitive_scalar_A2_bound state t w i))
    hA3 (monitoringIndicator state 0) 1
    (fun t => actual_monitoring_visit_indicator_is_measurable state 0 t (hstatemeas t))
    (fun t => Eventually.of_forall (fun w =>
      actual_monitoring_objective_indicator_has_a_separate_primitive_absolute_bound state t w))
    hA3Objective
  convert hconstraints using 1 <;> norm_num <;> ring

end SafeLearning.CompleteAppliedMonitoringCMDPBounded55


namespace SafeLearning.CompleteAppliedMonitoringCMDPPhysical58
open Set Filter MeasureTheory
open CompleteAppliedCMDPA1A2A3ProcessBridge30
open CompleteAppliedCMDPActualEpochBridge30 CompleteAppliedCMDPExpectedEpochBridge30
open CompleteAppliedCMDPActualConstraintBridge30 CompleteCoreProjectedDualDrift29
open CompleteMonitoringGeometry21 CompleteMonitoringPolicyValues22
open CompleteAppliedMonitoringCMDPBounded55
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Every value class contains a genuine controlled history policy with all
three expected long-run fractions. No supplied polytope/optimum premise. -/
abbrev PhysicalPolicy := {v : Fractions // v ∈ actualPolicyValues}
def physicalValue (p : PhysicalPolicy) : ℝ := p.val.v0
def physicalViolation (p : PhysicalPolicy) (i : Fin 2) : ℝ :=
  if i=0 then p.val.v1-1/3 else p.val.v2-1/3

theorem actual_physical_feasible_policy_sup_is_the_selected_monitoring_primal_value :
    feasiblePolicySup physicalValue physicalViolation = actualPrimalValue := by
  unfold feasiblePolicySup feasiblePolicyValues actualPrimalValue
  congr 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨p.val,p.property,?_,?_,rfl⟩
    · have h := hp (0:Fin 2)
      dsimp [physicalViolation] at h
      linarith
    · have h := hp (1:Fin 2)
      norm_num [physicalViolation] at h
      linarith
  · rintro ⟨v,hv,h1,h2,rfl⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro i
    fin_cases i <;> norm_num [physicalViolation] <;> linarith

theorem actual_physical_monitoring_feasible_policy_sup_is_one_third :
    feasiblePolicySup physicalValue physicalViolation = (1/3:ℝ) := by
  rw [actual_physical_feasible_policy_sup_is_the_selected_monitoring_primal_value]
  exact actual_constrained_policy_optimum_is_attained_and_equal_to_one_third.1

theorem actual_physical_monitoring_A1_A3_give_all_time_feasibility_and_one_third_recovery
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → MeasurableSpace Ω) (hs : ∀ n,s n ≤ m0)
    (eta C : ℝ) (heta : 0 < eta) (hC : 0 < C)
    (l0 : Fin 2 → ℝ) (hl0 : ∀ i,0 ≤ l0 i)
    (T : ℕ) (hT : 0 < T) (state : ℕ → Ω → Fin 3)
    (hstatemeas : ∀ t,Measurable (state t))
    (chosen : (Fin 2 → ℝ) → PhysicalPolicy) (slater : PhysicalPolicy)
    (hslater : ∀ i,C ≤ physicalViolation slater i)
    (hmax : ∀ l : Fin 2 → ℝ,(∀ i,0 ≤ l i) → ∀ p : PhysicalPolicy,
      physicalValue p+pairing l (physicalViolation p) ≤ physicalValue (chosen l)+pairing l (physicalViolation (chosen l)))
    (hlmeas : ∀ n i,Measurable[s n]
      (fun w => multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n i))
    (hA3 : ∀ n i,P[fun w => actualConstraintEpochSample T
      (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) n w i | s n] =ᵐ[P]
      fun w => physicalViolation (chosen (multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n)) i)
    (hA3Objective : ∀ n,P[fun w => epochMean T
      (fun t => monitoringIndicator state 0 t w) n | s n] =ᵐ[P]
      fun w => physicalValue (chosen (multiplier eta l0
        (fun k => actualConstraintEpochSample T
          (fun t w i => monitoringIndicator state i.succ t w) (fun _ => (1/3:ℝ)) k w) n))) :
    (∀ᵐ w ∂P,∀ i : Fin 2,(1/3:ℝ) ≤
      Filter.liminf (timeAverage (fun t => monitoringIndicator state i.succ t w)) atTop) ∧
    ((1/3:ℝ)-4*eta/9 ≤
      Filter.liminf (switchedExpectedAverage P (monitoringIndicator state 0)) atTop) := by
  have h := actual_monitoring_indicator_rewards_and_projected_A1_A3_give_every_time_guarantees
    (Policy:=PhysicalPolicy) P s hs eta C heta hC l0 hl0 T hT state hstatemeas
    physicalValue physicalViolation chosen slater hslater hmax hlmeas hA3 hA3Objective
  rw [actual_physical_monitoring_feasible_policy_sup_is_one_third] at h
  exact h

end SafeLearning.CompleteAppliedMonitoringCMDPPhysical58
