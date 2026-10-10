import Mathlib
set_option autoImplicit false
/-! Exact source algebra and general implications for Primers C, D and E.
Probability/model assumptions not encoded here are recorded in the inventory. -/
namespace SafeLearning.PrimersApplied

def mean2 (p a b : ℝ) : ℝ := p*a+(1-p)*b
def variance2 (p a b : ℝ) : ℝ := p*(a-mean2 p a b)^2+(1-p)*(b-mean2 p a b)^2

theorem mean2_affine (p a b c d : ℝ) :
    mean2 p (c*a+d) (c*b+d)=c*mean2 p a b+d := by unfold mean2; ring

theorem variance2_closed_form (p a b : ℝ) :
    variance2 p a b=p*(1-p)*(a-b)^2 := by unfold variance2 mean2; ring

theorem variance2_nonnegative (p a b : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    0≤variance2 p a b := by
  rw [variance2_closed_form]
  exact mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) (sq_nonneg _)

theorem variance2_affine (p a b c d : ℝ) :
    variance2 p (c*a+d) (c*b+d)=c^2*variance2 p a b := by
  simp only [variance2_closed_form]; ring

theorem total_variance_two (p a b va vb : ℝ) :
    p*(va+a^2)+(1-p)*(vb+b^2)-(mean2 p a b)^2=
      p*va+(1-p)*vb+variance2 p a b := by simp only [variance2, mean2]; ring

theorem finite_covariance_quadratic_nonnegative (u v x₁ x₂ y₁ y₂ : ℝ) :
    0≤((u*x₁+v*x₂)^2+(u*y₁+v*y₂)^2)/2 := by positivity

theorem bayes_alarm_new :
    ((4:ℝ)/5*(1/10))/((4/5)*(1/10)+(1/5)*(9/10))=4/13 := by norm_num

theorem bayes_alarm_legacy :
    ((95:ℝ)/100*(1/100))/((95/100)*(1/100)+(5/100)*(99/100))=19/118 := by norm_num

theorem weighted_policy_costs :
    mean2 (7/10) 2 10=(22:ℝ)/5 ∧ mean2 (9/10) 2 10=(14:ℝ)/5 := by norm_num [mean2]

theorem zero_mean_nonnegative_two (p a b : ℝ) (hp : 0<p) (hp1 : p<1)
    (ha : 0≤a) (hb : 0≤b) (hm : mean2 p a b=0) : a=0 ∧ b=0 := by
  unfold mean2 at hm
  constructor <;> nlinarith

/-- General finite weighted Markov inequality; no independence assumption. -/
theorem finite_weighted_markov {ι : Type*} (s : Finset ι) (w x : ι→ℝ)
    (a : ℝ) (_ha : 0<a) (hw : ∀ i∈s, 0≤w i) (hx : ∀ i∈s, 0≤x i) :
    a*(∑ i∈s, if a≤x i then w i else 0)≤∑ i∈s, w i*x i := by
  classical
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : a≤x i
  · simp only [h, ite_true]
    nlinarith [hw i hi]
  · simp only [h, ite_false, mul_zero]
    exact mul_nonneg (hw i hi) (hx i hi)

theorem failure_product_bound (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    1-a-b≤(1-a)*(1-b) := by nlinarith [mul_nonneg ha hb]

theorem three_failure_budgets : (1:ℝ)-((1/100)+(1/100)+(1/100))=97/100 := by norm_num

theorem centered_discrete_moments :
    (((-1:ℝ)^2+0^2+1^2)/3=2/3) ∧
    (((-1:ℝ)*(((-1)^2)-2/3)+0*(0^2-2/3)+1*(1^2-2/3))/3=0) ∧
    (((((-1:ℝ)^2)-2/3)^2+(0^2-2/3)^2+(1^2-2/3)^2)/3=2/9) := by norm_num

theorem gaussian_precision_addition (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    1/(a*b/(a+b))=1/a+1/b := by field_simp; ring

theorem gaussian_posterior_numbers :
    (1/(1/(4:ℝ)+1)=4/5) ∧ ((4:ℝ)/5*3=12/5) ∧ ((4:ℝ)/5+1=9/5) := by norm_num

theorem bernoulli_variance_bound (p : ℝ) : p*(1-p)≤1/4 := by nlinarith [sq_nonneg (p-1/2)]

/-- One-step preservation proves preservation at every natural time. -/
theorem invariant_along_iterates {α : Type*} (F : α→α) (S : Set α)
    (preserve : ∀ x∈S, F x∈S) (x : α) (initial : x∈S) :
    ∀ n : ℕ, (F^[n]) x∈S := by
  intro n
  induction n with
  | zero => simpa using initial
  | succ n ih => simpa only [Function.iterate_succ_apply'] using preserve _ ih

theorem affine_fixed_point (a b x : ℝ) (ha : a≠1) : a*x+b=x ↔ x=b/(1-a) := by
  have h : 1-a≠0 := by intro hz; apply ha; linarith
  constructor
  · intro hx; apply (eq_div_iff h).2; nlinarith
  · intro hx; have hx' := (eq_div_iff h).1 hx; nlinarith

theorem quadratic_scalar_decrease (a p x : ℝ) :
    p*(a*x)^2-p*x^2=p*(a^2-1)*x^2 := by ring

theorem quadratic_scalar_strict_decrease (a p x : ℝ)
    (ha : a^2<1) (hp : 0<p) (hx : x≠0) : p*(a*x)^2-p*x^2<0 := by
  rw [quadratic_scalar_decrease]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp (sub_neg.mpr ha)) (sq_pos_of_ne_zero hx)

/-- General geometric bound, not finite simulation. -/
theorem geometric_upper_bound (v : ℕ→ℝ) (q : ℝ) (hq : 0≤q)
    (step : ∀ n, v (n+1)≤q*v n) : ∀ n, v n≤q^n*v 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      v (n+1)≤q*v n := step n
      _≤q*(q^n*v 0) := mul_le_mul_of_nonneg_left ih hq
      _=q^(n+1)*v 0 := by ring

theorem geometric_lower_bound (h : ℕ→ℝ) (q : ℝ) (hq : 0≤q)
    (step : ∀ n, q*h n≤h (n+1)) : ∀ n, q^n*h 0≤h n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      q^(n+1)*h 0=q*(q^n*h 0) := by ring
      _≤q*h n := mul_le_mul_of_nonneg_left ih hq
      _≤h (n+1) := step n

theorem robust_interval_half (r : ℝ) (hr : 0≤r) :
    (∀ x w : ℝ, |x|≤r → |w|≤1/10 → |x/2+w|≤r) ↔ 1/5≤r := by
  constructor
  · intro h
    have h' := h r (1/10) (by simp [abs_of_nonneg hr]) (by norm_num)
    have := (abs_le.mp h').2
    linarith
  · intro h x w hx hw
    calc
      |x/2+w|≤|x/2|+|w| := abs_add_le _ _
      _=|x|/2+|w| := by rw [abs_div]; norm_num
      _≤r/2+1/10 := by linarith
      _≤r := by linarith

theorem scalar_storage_certificate (x w : ℝ) :
    2*(x/2+w)^2-2*x^2-4*w^2+x^2=-(1/2)*(x-2*w)^2 := by ring

theorem scalar_storage_inequality (x w : ℝ) :
    2*(x/2+w)^2-2*x^2≤4*w^2-x^2 := by nlinarith [sq_nonneg (x-2*w)]

theorem storage_energy_rearrangement (v₀ vT input output gainSq : ℝ)
    (hv₀ : v₀=0) (hvT : 0≤vT) (hdiss : vT-v₀≤gainSq*input-output) :
    output≤gainSq*input := by linarith

theorem small_gain_rearrangement (e₁ e₂ r₁ r₂ g₁ g₂ : ℝ)
    (hg₂ : 0≤g₂) (hprod : g₁*g₂<1)
    (h₁ : e₁≤r₁+g₂*e₂) (h₂ : e₂≤r₂+g₁*e₁) :
    e₁≤(r₁+g₂*r₂)/(1-g₁*g₂) := by
  apply (le_div_iff₀ (by linarith : 0<1-g₁*g₂)).2
  nlinarith [mul_le_mul_of_nonneg_left h₂ hg₂]

theorem one_step_quadratic_minimizer (x u : ℝ) :
    u^2+(x+u)^2=2*(u+x/2)^2+x^2/2 := by ring

theorem one_step_quadratic_minimal (x u : ℝ) : x^2/2≤u^2+(x+u)^2 := by
  rw [one_step_quadratic_minimizer]
  nlinarith [sq_nonneg (u+x/2)]

theorem legacy_lyapunov_positive (x y : ℝ) (hxy : x≠0 ∨ y≠0) :
    0<(5/4)*x^2+(1/2)*x*y+(1/4)*y^2 := by
  have heq : (5/4)*x^2+(1/2)*x*y+(1/4)*y^2=x^2+(x+y)^2/4 := by ring
  rw [heq]
  rcases hxy with hx | hy
  · have := sq_pos_of_ne_zero hx; positivity
  · by_cases hx : x=0
    · subst x; have := sq_pos_of_ne_zero hy; norm_num at *; positivity
    · have := sq_pos_of_ne_zero hx; positivity

theorem legacy_lyapunov_derivative (x y : ℝ) :
    (2*(5/4)*x+(1/2)*y)*y+((1/2)*x+2*(1/4)*y)*(-2*x-3*y)=-(x^2+y^2) := by ring

theorem residual_error_bound (distance residual gamma : ℝ)
    (hgamma : gamma<1) (htriangle : distance≤residual+gamma*distance) :
    distance≤residual/(1-gamma) := by
  apply (le_div_iff₀ (by linarith : 0<1-gamma)).2
  nlinarith

theorem scalar_bellman_equation (r gamma v : ℝ) (hgamma : gamma≠1) :
    v=r+gamma*v ↔ v=r/(1-gamma) := by
  rw [eq_comm (a := v)]
  simpa [add_comm] using affine_fixed_point gamma r v hgamma

theorem bernoulli_baseline_unbiased (p b : ℝ) :
    p*((1-b)*(1-p))+(1-p)*((0-b)*(-p))=p*(1-p) := by ring

theorem bernoulli_optimal_baseline_equal_samples (p : ℝ) :
    (1-(1-p))*(1-p)=p*(1-p) ∧ (0-(1-p))*(-p)=p*(1-p) := by constructor <;> ring

theorem bernoulli_baseline_variance (p b : ℝ) :
    p*(((1-b)*(1-p))-p*(1-p))^2+(1-p)*(((0-b)*(-p))-p*(1-p))^2=
      p*(1-p)*(b-(1-p))^2 := by ring

theorem bernoulli_baseline_numbers :
    (4/5:ℝ)*(1-4/5)*(0-(1-4/5))^2=4/625 ∧
    (4/5:ℝ)*(1-4/5)*(4/5-(1-4/5))^2=36/625 := by norm_num

theorem running_mdp_optimal_fixed_point :
    max ((1:ℝ)+(9/10)*18) ((9/10)*20)=18 ∧
    max ((9/10:ℝ)*18) (2+(9/10)*20)=20 := by norm_num

theorem running_mdp_uniform_fixed_point :
    ((29:ℝ)/4=1/2+(9/10)*((29/4+31/4)/2)) ∧
    ((31:ℝ)/4=1+(9/10)*((29/4+31/4)/2)) := by norm_num

theorem running_mdp_occupancy :
    ((11:ℝ)/20+9/20=1) ∧ ((11:ℝ)/20=1/10+(9/10)*(11/40+9/40)) ∧
    (10*((11:ℝ)/40+2*(9/40))=29/4) ∧ (10*((9:ℝ)/40)=9/4) := by norm_num

theorem strict_penalty_comparison (p : ℝ) : (4-p/2<(2:ℝ)) ↔ 4<p := by
  constructor <;> intro h <;> linarith

theorem scalar_tube_inside_interval (z r : ℝ) (hr : 0≤r) :
    (∀ x : ℝ, z-r≤x → x≤z+r → |x|≤1) ↔ |z|+r≤1 := by
  constructor
  · intro h
    have hleft := h (z-r) (by rfl) (by linarith)
    have hright := h (z+r) (by linarith) (by rfl)
    rw [abs_le] at hleft hright
    by_cases hz : 0≤z
    · rw [abs_of_nonneg hz]; linarith
    · rw [abs_of_neg (lt_of_not_ge hz)]; linarith
  · intro h x hleft hright
    rw [abs_le]
    constructor
    · have := neg_abs_le z; linarith
    · have := le_abs_self z; linarith


open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- Actual Gaussian probability measure, not a finite numerical approximation. -/
theorem standard_gaussian_chernoff (a : ℝ) (ha : 0≤a) :
    (gaussianReal 0 1).real {z : ℝ | a≤z}≤Real.exp (-a^2/2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) a ha
    (integrable_exp_mul_gaussianReal a)
  rw [mgf_id_gaussianReal] at h
  simpa only [zero_mul, NNReal.coe_one, one_mul, zero_add, ← Real.exp_add,
    show -a*a+a^2/2=-a^2/2 by ring, id_eq] using h

/-- The completion-of-square optimizer used in Gaussian Chernoff. -/
theorem chernoff_optimizer (a t : ℝ) :
    -a^2/2≤-t*a+t^2/2 := by nlinarith [sq_nonneg (t-a)]

theorem chernoff_optimizer_attained (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ -t*a+t^2/2=-a^2/2 := by exact ⟨a,ha,by ring⟩

/-- Actual probability-space Chebyshev, with explicit square-integrability. -/
theorem chebyshev_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω→ℝ)
    (hX : MemLp X 2 μ) (a : ℝ) (ha : 0<a) :
    μ {ω | a≤|X ω-∫ w, X w ∂μ|}≤ENNReal.ofReal (variance X μ/a^2) := by
  exact meas_ge_le_variance_div_sq hX ha

/-- The actual bounded-variable variance theorem behind Bernoulli sample bounds. -/
theorem bounded_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω→ℝ) (a b : ℝ)
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, X ω∈Set.Icc a b) :
    variance X μ≤((b-a)/2)^2 := by exact variance_le_sq_of_bounded hbound hX

/-- Source's complete-domain hypothesis is explicit in Lean's typeclasses. -/
theorem contraction_unique_fixed_point {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] (F : α→α) (q : ℝ≥0) (hF : ContractingWith q F) :
    ∃! x, F x=x := by
  refine ⟨hF.fixedPoint F,hF.fixedPoint_isFixedPt,?_⟩
  intro y hy
  exact hF.fixedPoint_unique hy

theorem contraction_iterates_converge {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] (F : α→α) (q : ℝ≥0) (hF : ContractingWith q F) (x : α) :
    Tendsto (fun n : ℕ => (F^[n]) x) atTop (𝓝 (hF.fixedPoint F)) := by
  exact hF.tendsto_iterate_fixedPoint x

/-- General weighted-average sup bound used in the Bellman proof. -/
theorem weighted_average_abs_bound {ι : Type*} (s : Finset ι) (w x : ι→ℝ) (B : ℝ)
    (hw : ∀ i∈s, 0≤w i) (hwsum : ∑ i∈s, w i=1)
    (hx : ∀ i∈s, |x i|≤B) : |∑ i∈s, w i*x i|≤B := by
  calc
    |∑ i∈s, w i*x i|≤∑ i∈s, |w i*x i| := Finset.abs_sum_le_sum_abs _ _
    _=∑ i∈s, w i*|x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul,abs_of_nonneg (hw i hi)]
    _≤∑ i∈s, w i*B := Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hx i hi) (hw i hi)
    _=B := by rw [← Finset.sum_mul,hwsum,one_mul]

/-- Exact two-action max inequality; valid for all real tables. -/
theorem max_two_abs_bound (a b c d e : ℝ) (hac : |a-c|≤e) (hbd : |b-d|≤e) :
    |max a b-max c d|≤e := by
  rw [abs_le] at hac hbd ⊢
  constructor
  · have ha := le_max_left a b; have hb := le_max_right a b
    have hmax : max c d ≤ max a b+e := by apply max_le <;> linarith
    linarith
  · have hc := le_max_left c d; have hd := le_max_right c d
    apply sub_le_iff_le_add.mpr
    apply max_le <;> linarith

/-- Score invariance for a two-action action-independent baseline. -/
theorem baseline_unbiased_general_two (p r₁ r₀ b : ℝ) :
    p*(r₁-b)*(1-p)+(1-p)*(r₀-b)*(-p)=p*(1-p)*(r₁-r₀) := by ring

/-- Zero entropy-independent baseline need not be optimal, but the optimum is exact. -/
theorem baseline_minimal_variance (p b : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    0≤p*(1-p)*(b-(1-p))^2 := by positivity

/-- A strict margin and a Lipschitz difference bound preserve binary signs. -/
theorem binary_margin_positive (f₀ f₁ L r : ℝ) (_hf : 0<f₀) (hL : 0<L)
    (hdiff : |f₁-f₀|≤L*r) (hr : r<f₀/L) : 0<f₁ := by
  have he := (abs_le.mp hdiff).1
  have hb := (lt_div_iff₀ hL).mp hr
  nlinarith

theorem binary_margin_negative (f₀ f₁ L r : ℝ) (_hf : f₀<0) (hL : 0<L)
    (hdiff : |f₁-f₀|≤L*r) (hr : r<(-f₀)/L) : f₁<0 := by
  have he := (abs_le.mp hdiff).2
  have hb := (lt_div_iff₀ hL).mp hr
  nlinarith

/-- Source S21: a ReLU pair represents identity exactly. -/
theorem relu_identity (x : ℝ) : max 0 x-max 0 (-x)=x := by
  by_cases hx : 0≤x
  · rw [max_eq_right hx,max_eq_left (by linarith)]; ring
  · rw [max_eq_left (le_of_not_ge hx),max_eq_right (by linarith)]; ring

theorem sector_increment_qc (dx dy : ℝ) (_hdx : 0≤dx) (hdy : 0≤dy) (hupper : dy≤dx) :
    dy*(dx-dy)≥0 := by exact mul_nonneg hdy (sub_nonneg.mpr hupper)

/-- Exact polynomial certificates for the corrected 2×2 Lyapunov sandwich. -/
theorem legacy_lyapunov_spectral_polynomial (l : ℝ) :
    (5/4-l)*(1/4-l)-(1/4)^2=l^2-(3/2)*l+1/4 := by ring

theorem legacy_lyapunov_safe_rational_sandwich (x y : ℝ) :
    (1909/10000)*(x^2+y^2)≤(5/4)*x^2+(1/2)*x*y+(1/4)*y^2 ∧
    (5/4)*x^2+(1/2)*x*y+(1/4)*y^2≤(13091/10000)*(x^2+y^2) := by
  constructor
  · have hsq := sq_nonneg ((10591/10000)*x+y/4)
    have hid : (10591/10000)*((5/4)*x^2+(1/2)*x*y+(1/4)*y^2-
        (1909/10000)*(x^2+y^2))=((10591/10000)*x+y/4)^2+(9281/100000000)*y^2 := by ring
    have hy := sq_nonneg y
    nlinarith
  · have hsq := sq_nonneg ((591/10000)*x-y/4)
    have hid : (591/10000)*((13091/10000)*(x^2+y^2)-
        ((5/4)*x^2+(1/2)*x*y+(1/4)*y^2))=((591/10000)*x-y/4)^2+(9281/100000000)*y^2 := by ring
    have hy := sq_nonneg y
    nlinarith

/-- A finite dissipation sum gives the claimed energy budget for every horizon. -/
theorem finite_dissipation_sum (V input output : ℕ→ℝ) (g : ℝ)
    (hstep : ∀ k, V (k+1)-V k≤g*input k-output k) :
    ∀ N : ℕ, V N-V 0≤g*(∑ k∈Finset.range N,input k)-(∑ k∈Finset.range N,output k) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    have hs := hstep N
    nlinarith

/-- Source CVaR's atomic three-outcome objective is globally minimized at η=10. -/
theorem atomic_cvar_minimum (eta : ℝ) :
    (55:ℝ)≤eta+10*((4/5)*max (0-eta) 0+(3/20)*max (10-eta) 0+(1/20)*max (100-eta) 0) := by
  by_cases h₀ : eta≤0
  · rw [max_eq_left (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    linarith
  · by_cases h₁ : eta≤10
    · rw [max_eq_right (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
      linarith
    · by_cases h₂ : eta≤100
      · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_left (by linarith)]
        linarith
      · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_right (by linarith)]
        linarith

theorem atomic_cvar_attained :
    (10:ℝ)+10*((4/5)*max (0-10) 0+(3/20)*max (10-10) 0+(1/20)*max (100-10) 0)=55 := by norm_num

/-- Exact scalar MPC two-step completion of squares (S26). -/
theorem two_step_mpc_optimal (u v : ℝ) :
    (3:ℝ)≤u^2+v^2+(3+u+v)^2 := by
  have hsq : 0≤(u+1)^2+(v+1)^2+(u+v+2)^2 := by positivity
  nlinarith

theorem two_step_mpc_attained : ((-1:ℝ)^2+(-1)^2+(3-1-1)^2)=3 := by norm_num



/-! Exact source calculations below prove only the encoded subclaims.
The per-exercise ledger records omitted symbolic/statistical parts explicitly. -/

/-- Source anchor(s): pr-ready-1 pr-ready-2 pr-ready-3. -/
theorem c_ready :
    (1:ℝ)-15/100=17/20 ∧ (2+6+6+6:ℝ)/4=5 ∧ (1:ℝ)*2=2 ∧ (2:ℝ)*2=4 := by norm_num

/-- Source anchor(s): pr-extra-1. -/
theorem c_s01 :
    (1/2:ℝ)+1/4+1/4=1 ∧ (1/4:ℝ)+1/4=1/2 ∧ (1/2:ℝ)*0+(1/4)*2+(1/4)*4=3/2 := by norm_num

/-- Source anchor(s): pr-extra-2. -/
theorem c_s02 :
    (1/2:ℝ)*0^2+(1/4)*2^2+(1/4)*4^2=5 ∧ (5:ℝ)-(3/2)^2=11/4 ∧ (3:ℝ)*(3/2)+1=11/2 ∧ (9:ℝ)*(11/4)=99/4 := by norm_num

/-- Source anchor(s): pr-extra-4. -/
theorem c_s04 :
    ((2:ℝ)/6)/(3/6)=2/3 := by norm_num

/-- Source anchor(s): pr-extra-6. -/
theorem c_s06 :
    ((0:ℝ)+4)/2=2 ∧ (1:ℝ)+((0-2)^2+(4-2)^2)/2=5 := by norm_num

/-- Source anchor(s): pr-extra-7. -/
theorem c_s07 :
    (4/5:ℝ)^2+(1/5)*(3/10)=7/10 ∧ (4/5:ℝ)*(1/5)+(1/5)*(7/10)=3/10 := by norm_num

/-- Source anchor(s): pr-extra-8. -/
theorem c_s08 :
    (3/5:ℝ)*(4/5)+(2/5)*(3/10)=3/5 ∧ (3/5:ℝ)*(1/5)+(2/5)*(7/10)=2/5 := by norm_num

/-- Source anchor(s): pr-extra-9. -/
theorem c_s09 :
    (1/5:ℝ)*(4/5)/100=1/625 ∧ (1/5:ℝ)*(4/5)/50=2/625 := by norm_num

/-- Source anchor(s): pr-extra-12. -/
theorem c_s12 :
    (1:ℝ)+1/2+1/2+4=6 := by norm_num

/-- Source anchor(s): pr-extra-13. -/
theorem c_s13 :
    min (1:ℝ) (2/8)=1/4 ∧ min (1:ℝ) (2/1)=1 := by norm_num

/-- Source anchor(s): pr-extra-15. -/
theorem c_s15 :
    ((0:ℝ)+2)/2=1 ∧ ((1:ℝ)-(-1))/2=1 := by norm_num

/-- Source anchor(s): pr-extra-19. -/
theorem c_s19 :
    ((-1:ℝ)+1)/2=0 := by norm_num

/-- Source anchor(s): pr-extra-20. -/
theorem c_s20 :
    ((-2:ℝ)+2)/2=0 ∧ ((2:ℝ)^2+(-2)^2)/2=4 := by norm_num

/-- Source anchor(s): pr-extra-21. -/
theorem c_s21 :
    ((-1:ℝ)^2+1^2)/2=1 := by norm_num

/-- Source anchor(s): pr-extra-25. -/
theorem c_s25 :
    (4/5:ℝ)=80/100 ∧ (4/5:ℝ)+3/20=95/100 ∧ (4/5:ℝ)<9/10 ∧ (9/10:ℝ)≤4/5+3/20 := by norm_num

/-- Source anchor(s): pr-extra-26. -/
theorem c_s26 :
    ((1/20:ℝ)*100+(1/20)*10)/(1/10)=55 ∧ (3/20:ℝ)*10+(1/20)*100=13/2 ∧ ((13/2:ℝ)/(1/5))=65/2 := by norm_num

/-- Source anchor(s): pr-extra-28. -/
theorem c_s28 :
    (6:ℝ)*(1/10)^2*(9/10)^2=243/5000 ∧ (1:ℝ)-(9/10)^4=3439/10000 := by norm_num

/-- Source anchor(s): sys-ready-1 sys-ready-2 sys-ready-3. -/
theorem d_ready :
    (1:ℝ)/(1-1/2)=2 ∧ (3:ℝ)*(-2)=-6 ∧ (1:ℝ)^2+2*(-2)^2=9 := by norm_num

/-- Source anchor(s): sys-extra-1. -/
theorem d_s01 :
    (1/2:ℝ)*2+1=2 ∧ (1/2:ℝ)*2+0=1 ∧ (1/2:ℝ)*1-1=-1/2 := by norm_num

/-- Source anchor(s): sys-extra-2. -/
theorem d_s02 :
    (4:ℝ)*(1/4)^0=4 ∧ (4:ℝ)*(1/4)^1=1 ∧ (4:ℝ)*(1/4)^2=1/4 ∧ (4:ℝ)*(1/4)^3=1/16 := by norm_num

/-- Source anchor(s): sys-extra-3. -/
theorem d_s03 :
    (-1:ℝ)+2*0=-1 ∧ (-1:ℝ)+2*1=1 ∧ (1/10:ℝ)+(1/5)*(-1/10+(1/10)^2)=41/500 := by norm_num

/-- Source anchor(s): sys-extra-4. -/
theorem d_s04 :
    (1/2:ℝ)*2=1 ∧ (-6/5:ℝ)*1=-6/5 ∧ (1/2:ℝ)^2*2=1/2 ∧ (-6/5:ℝ)^2*1=36/25 := by norm_num

/-- Source anchor(s): sys-extra-7. -/
theorem d_s07 :
    (2:ℝ)*3*(-2*3)=-36 := by norm_num

/-- Source anchor(s): sys-extra-8. -/
theorem d_s08 :
    (2:ℝ)*(-1)=-2 ∧ (2:ℝ)*(-2)=-4 := by norm_num

/-- Source anchor(s): sys-extra-9. -/
theorem d_s09 :
    (2:ℝ)*(1/2)*(-1/2+(1/2)^3)=-3/8 := by norm_num

/-- Source anchor(s): sys-extra-12. -/
theorem d_s12 :
    min (1:ℝ) (2*(1-9/10))=1/5 := by norm_num

/-- Source anchor(s): sys-extra-13. -/
theorem d_s13 :
    (2:ℝ)-3=-1 := by norm_num

/-- Source anchor(s): sys-extra-15. -/
theorem d_s15 :
    (1/2:ℝ)*2=1 ∧ (1/3:ℝ)*3=1 := by norm_num

/-- Source anchor(s): sys-extra-16. -/
theorem d_s16 :
    (1:ℝ)/2=1/2 := by norm_num

/-- Source anchor(s): sys-extra-17. -/
theorem d_s17 :
    (2:ℝ)^2+2^2=8 ∧ (1:ℝ)/2^2=1/4 := by norm_num

/-- Source anchor(s): sys-extra-18. -/
theorem d_s18 :
    (1:ℝ)/(1-1/2)=2 ∧ (1:ℝ)/(1-1/4)=4/3 := by norm_num

/-- Source anchor(s): sys-extra-20. -/
theorem d_s20 :
    (-2:ℝ)+2*(4/5)=-2/5 := by norm_num

/-- Source anchor(s): sys-extra-21. -/
theorem d_s21 :
    (-2:ℝ)-2*0=-2 := by norm_num

/-- Source anchor(s): sys-extra-22. -/
theorem d_s22 :
    (1:ℝ)*(0*1)-(1/2)*0=0 := by norm_num

/-- Source anchor(s): sys-extra-23. -/
theorem d_s23 :
    (2:ℝ)*(1/2)^2=1/2 ∧ (2:ℝ)*(1/2)=1 := by norm_num

/-- Source anchor(s): sys-extra-24. -/
theorem d_s24 :
    (1:ℝ)/(3+1)+1/(3+2)=9/20 ∧ ((1/2:ℝ)*2)/(3+1)+1/(3+2)=9/20 := by norm_num

/-- Source anchor(s): sys-extra-25. -/
theorem d_s25 :
    (-1:ℝ)^2+(2-1)^2=2 := by norm_num

/-- Source anchor(s): sys-extra-27. -/
theorem d_s27 :
    (-1/2:ℝ)+1/2=0 ∧ (1/2:ℝ)-1/2=0 := by norm_num

/-- Source anchor(s): rle-ready-1 rle-ready-2. -/
theorem e_ready :
    (1/4:ℝ)*4+(3/4)*0=1 ∧ (2:ℝ)/(1-1/2)=4 := by norm_num

/-- Source anchor(s): rle-extra-1. -/
theorem e_s01 :
    (4/5:ℝ)-4/5+(4/5-3/5)+(4/5-3/10)+(4/5-3/5)=9/10 ∧ ((9/10:ℝ)/4)=9/40 ∧ (4/5:ℝ)-3/10=1/2 := by norm_num

/-- Source anchor(s): rle-extra-2. -/
theorem e_s02 :
    (1/2:ℝ)+1/5=7/10 ∧ (3/5:ℝ)+1/20=13/20 ∧ (3/10:ℝ)-2/5=-1/10 ∧ (1/5:ℝ)-1/10=1/10 := by norm_num

/-- Source anchor(s): rle-extra-3. -/
theorem e_s03 :
    max (1:ℝ) 1-1=0 ∧ (1:ℝ)+1-1=1 := by norm_num

/-- Source anchor(s): rle-extra-4. -/
theorem e_s04 :
    (2:ℝ)+(1/2)*4=4 ∧ (4:ℝ)+(1/2)*0=4 := by norm_num

/-- Source anchor(s): rle-extra-5. -/
theorem e_s05 :
    (1:ℝ)+(1/2)*((3/4)*4)=5/2 ∧ (3/5:ℝ)*(5/2)+(2/5)*1=19/10 := by norm_num

/-- Source anchor(s): rle-extra-6. -/
theorem e_s06 :
    (1/100:ℝ)*100=1 := by norm_num

/-- Source anchor(s): rle-extra-7. -/
theorem e_s07 :
    (2:ℝ)/(1-1/2)=4 := by norm_num

/-- Source anchor(s): rle-extra-8. -/
theorem e_s08 :
    (4/3:ℝ)=1+(1/2)*(2/3) ∧ (2/3:ℝ)=(1/2)*(4/3) ∧ (1/2:ℝ)*(4/3)-4/3=-2/3 := by norm_num

/-- Source anchor(s): rle-extra-9. -/
theorem e_s09 :
    (2:ℝ)*(2/5)/(1-4/5)=4 ∧ (2/5:ℝ)/(1-4/5)=2 := by norm_num

/-- Source anchor(s): rle-extra-10. -/
theorem e_s10 :
    (2:ℝ)+(1/2)*0=2 ∧ (2:ℝ)+(1/2)*2=3 ∧ (2:ℝ)+(1/2)*3=7/2 := by norm_num

/-- Source anchor(s): rle-extra-11. -/
theorem e_s11 :
    (3/100:ℝ)/(1-9/10)=3/10 ∧ (1/10:ℝ)*(1-9/10)=1/100 := by norm_num

/-- Source anchor(s): rle-extra-12. -/
theorem e_s12 :
    (1:ℝ)/(1-1/2)=2 := by norm_num

/-- Source anchor(s): rle-extra-13. -/
theorem e_s13 :
    (4:ℝ)*(1/4)=1 ∧ (4:ℝ)*(1/4)*(3/4)=3/4 ∧ (1/4:ℝ)*(3/4)+(3/4)*(-1/4)=0 := by norm_num

/-- Source anchor(s): rle-extra-14. -/
theorem e_s14 :
    (1/4:ℝ)*3*(3/4)+(3/4)*(-1)*(-1/4)=3/4 := by norm_num

/-- Source anchor(s): rle-extra-16. -/
theorem e_s16 :
    (1:ℝ)+(9/10)*2=14/5 ∧ (14/5:ℝ)-1/2=23/10 ∧ (1/2:ℝ)+(1/5)*(23/10)=24/25 := by norm_num

/-- Source anchor(s): rle-extra-18. -/
theorem e_s18 :
    ((0:ℝ)+2)/2=1 ∧ (1:ℝ)+((0-1)^2+(2-1)^2)/2=2 := by norm_num

/-- Source anchor(s): rle-extra-19. -/
theorem e_s19 :
    max (0:ℝ) (2*1-3+1/2)=0 ∧ max (0:ℝ) (2*2-1+1/2)=7/2 := by norm_num

/-- Source anchor(s): rle-extra-20. -/
theorem e_s20 :
    ((3:ℝ)*max 0 (2*1-1)-1)=2 ∧ ((3:ℝ)*1-1)*1=2 ∧ ((3:ℝ)*1-1)*3*1=6 ∧ ((3:ℝ)*1-1)*3*2=12 := by norm_num

/-- Source anchor(s): rle-extra-22. -/
theorem e_s22 :
    (1:ℝ)-2=-1 ∧ (2:ℝ)-3=-1 ∧ (3:ℝ)-4=-1 := by norm_num

/-- Source anchor(s): rle-extra-23. -/
theorem e_s23 :
    |(1:ℝ)+1/5|=6/5 ∧ (1:ℝ)+|1/5|=6/5 ∧ |(1:ℝ)-4/5|=1/5 ∧ (1:ℝ)+|-4/5|=9/5 := by norm_num

/-- Source anchor(s): rle-extra-24. -/
theorem e_s24 :
    (1/2:ℝ)*0+2=2 ∧ (1/2:ℝ)*2+2=3 ∧ (1/2:ℝ)*3+2=7/2 ∧ |(1/2:ℝ)*(7/2)+2-7/2|/(1-1/2)=1/2 := by norm_num

/-- Source anchor(s): rle-extra-25. -/
theorem e_s25 :
    (3:ℝ)-1-2*(2/5)=6/5 ∧ (3:ℝ)-0-2*(2/5)=11/5 := by norm_num

/-- Source anchor(s): rle-extra-26. -/
theorem e_s26 :
    |(2:ℝ)*1+1|/2=3/2 ∧ |(1:ℝ)-(-1/2)|=3/2 ∧ (2:ℝ)*(-1/2)+1=0 := by norm_num

/-- Source anchor(s): rle-extra-27. -/
theorem e_s27 :
    (50:ℝ)/100=1/2 ∧ ((80:ℝ)-10)/100=7/10 := by norm_num

/-- Source anchor(s): exercises C.3. -/
theorem legacy_c03 :
    (1:ℝ)/(1+16)=1/17 ∧ ((1:ℝ)/17)*16*(9/10)=72/85 := by norm_num

/-- Source anchor(s): exercises C.4. -/
theorem legacy_c04_chebyshev :
    (1/4:ℝ)/((1/100)*(1/20)^2)=10000 := by norm_num

/-- Source anchor(s): exercises D.2. -/
theorem legacy_d02 :
    ((0:ℝ)+1)=1 ∧ (0:ℝ)*1-(-1/2)*1=1/2 := by norm_num

/-- Source anchor(s): exercises D.8. -/
theorem legacy_d08 :
    (3/10:ℝ)/(3/2-1)=3/5 ∧ (1/5:ℝ)/(1-2/5)=1/3 ∧ (2:ℝ)-1/3=5/3 ∧ (1:ℝ)-(3/5)*(1/3)=4/5 := by norm_num

/-- Source anchor(s): exercises E.2. -/
theorem legacy_e02 :
    (11/2:ℝ)*(11/20)+(9/2)*(-9/20)=1 ∧ (11/2:ℝ)*(-9/20)+(9/2)*(11/20)=0 := by norm_num

/-- Source anchor(s): exercises E.5. -/
theorem legacy_e05 :
    (10:ℝ)*((1/10)*(-19/10)+(9/10)*(11/10))=8 := by norm_num

/-- Source anchor(s): exercises E.6. -/
theorem legacy_e06 :
    (1/25:ℝ)+(9/20)*((3/25)+(9/20)*(1/5))=269/2000 ∧ (1/25:ℝ)+(9/10)*(3/25)+(81/100)*(1/5)=31/100 := by norm_num


/-- All finite action counts, not just a two-action example. -/
theorem finite_max_abs_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f g : ι→ℝ) (B : ℝ) (hfg : ∀ i∈s, |f i-g i|≤B) :
    |s.sup' hs f-s.sup' hs g|≤B := by
  have h₁ : s.sup' hs f ≤ s.sup' hs g+B := by
    apply Finset.sup'_le
    intro i hi
    have ha := (abs_le.mp (hfg i hi)).2
    have hb := Finset.le_sup' g hi
    linarith
  have h₂ : s.sup' hs g ≤ s.sup' hs f+B := by
    apply Finset.sup'_le
    intro i hi
    have ha := (abs_le.mp (hfg i hi)).1
    have hb := Finset.le_sup' f hi
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- One Bellman row is γ-Lipschitz in the sup-bound B for arbitrary finite MDPs. -/
theorem finite_optimal_bellman_row {A S : Type*} (actions : Finset A)
    (states : Finset S) (hne : actions.Nonempty) (P : A→S→ℝ) (reward : A→ℝ)
    (V W : S→ℝ) (gamma B : ℝ) (hg : 0≤gamma)
    (hP : ∀ a∈actions, ∀ s∈states, 0≤P a s)
    (hPsum : ∀ a∈actions, ∑ s∈states,P a s=1)
    (hVW : ∀ s∈states, |V s-W s|≤B) :
    |actions.sup' hne (fun a => reward a+gamma*(∑ s∈states,P a s*V s))-
     actions.sup' hne (fun a => reward a+gamma*(∑ s∈states,P a s*W s))|≤gamma*B := by
  apply finite_max_abs_bound
  intro a ha
  have hw := weighted_average_abs_bound states (P a) (fun s => V s-W s) B
    (hP a ha) (hPsum a ha) hVW
  have heq : (∑ s∈states,P a s*V s)-(∑ s∈states,P a s*W s)=
      ∑ s∈states,P a s*(V s-W s) := by simp [mul_sub,Finset.sum_sub_distrib]
  have halgebra : reward a+gamma*(∑ s∈states,P a s*V s)-
      (reward a+gamma*(∑ s∈states,P a s*W s))=
      gamma*(∑ s∈states,P a s*(V s-W s)) := by rw [← heq]; ring
  rw [halgebra,abs_mul,abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left hw hg

/-- Exact safe direction of the rounded constants in the repaired Lyapunov example. -/
theorem legacy_lyapunov_rounding :
    (3+Real.sqrt 5)/2≤(2619/1000:ℝ) ∧ (3819/10000:ℝ)≤(3-Real.sqrt 5)/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem legacy_lyapunov_rounded_certificate (t n : ℝ) (ht : 0≤t) (hn : 0≤n) :
    ((3+Real.sqrt 5)/2)*Real.exp (-((3-Real.sqrt 5)/2)*t)*n≤
      (2619/1000)*Real.exp (-(3819/10000)*t)*n := by
  apply mul_le_mul_of_nonneg_right _ hn
  apply mul_le_mul legacy_lyapunov_rounding.1
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right legacy_lyapunov_rounding.2 ht]
  · exact le_of_lt (Real.exp_pos _)
  · norm_num

/-- The old inward-rounded lower spectral value was too large. -/
theorem legacy_lyapunov_old_lower_invalid : (3-Real.sqrt 5)/4<(191/1000:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  nlinarith

/-- Source C.S18: the failure allocation sums exactly over every finite horizon. -/
theorem telescoping_failure_budget (delta : ℝ) :
    ∀ N : ℕ, (∑ t∈Finset.range N,delta/((t+1:ℝ)*(t+2)))=delta*(1-1/(N+1:ℝ)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    have h₁ : (N:ℝ)+1≠0 := by positivity
    have h₂ : (N:ℝ)+2≠0 := by positivity
    field_simp
    ring


/-- Source C.S3: positive semidefiniteness of the displayed covariance for every v. -/
theorem c_s03_psd (u v : ℝ) : 0≤(2/3)*u^2+(2/9)*v^2 := by positivity

/-- Source C.S30: exact rank-count arithmetic, not exchangeability of random scores. -/
theorem c_s30_rank_count :
    ((Finset.univ.filter (fun i : Fin 20 => i.val<18)).card=18) ∧ ((18:ℝ)/20=9/10) := by
  constructor
  · decide
  · norm_num

/-- Source D.S3: the derivative is proved, not just substituted as a formula. -/
theorem d_s03_derivative (x : ℝ) : HasDerivAt (fun z : ℝ => -z+z^2) (-1+2*x) x := by
  convert (hasDerivAt_id x).neg.add ((hasDerivAt_id x).pow 2) using 1
  · rfl
  · simp only [id_eq, mul_one]; ring

/-- Source D.S9: universal nonlinear Lyapunov derivative and sublevel estimate. -/
theorem d_s09_lyapunov (x r : ℝ) (hx : x^2≤r^2) :
    2*x*(-x+x^3)=-2*x^2*(1-x^2) ∧
    2*x*(-x+x^3)≤-2*(1-r^2)*x^2 := by
  constructor
  · ring
  · nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]

/-- Source D.S14: exact stabilizing continuous Riccati root. -/
theorem d_s14_riccati :
    2*(1+Real.sqrt 2)-(1+Real.sqrt 2)^2+1=0 ∧
    1-(1+Real.sqrt 2)=-Real.sqrt 2 ∧ 0<1+Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor
  · nlinarith
  constructor
  · ring
  · linarith

/-- Source D.S19: saturation sector bounds for every real input. -/
theorem d_s19_saturation (v : ℝ) :
    0≤v*(max (-1) (min 1 v)) ∧ v*(max (-1) (min 1 v))≤v^2 := by
  by_cases hlo : v≤-1
  · rw [min_eq_right (by linarith),max_eq_left hlo]
    constructor <;> nlinarith
  · by_cases hhi : 1≤v
    · rw [min_eq_left hhi,max_eq_right (by norm_num)]
      constructor <;> nlinarith
    · rw [min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo)]
      constructor
      · nlinarith [sq_nonneg v]
      · nlinarith

/-- Source D.S21: a sign-preserving sector cannot worsen this derivative bound. -/
theorem d_s21_sector_decrease (x phi : ℝ) (hsector : 0≤x*phi) :
    2*x*(-x-phi)≤-2*x^2 := by nlinarith

/-- Source E.S15: universal optimum bound for the given natural-gradient subproblem. -/
theorem e_s15_natural_bound (x y : ℝ) (h : (1/2)*(4*x^2+y^2)≤1/20) :
    2*x+y≤Real.sqrt 5/5 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  nlinarith [sq_nonneg (2*x-y)]

theorem e_s15_natural_attained :
    (1/2)*(4*(Real.sqrt 5/20)^2+(Real.sqrt 5/10)^2)=(1/20:ℝ) ∧
    2*(Real.sqrt 5/20)+Real.sqrt 5/10=Real.sqrt 5/5 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  constructor
  · nlinarith
  · ring

/-- Source E.S17: exact Boltzmann arithmetic for q=(0,log3), α=1. -/
theorem e_s17_softmax_numbers :
    Real.exp 0/(Real.exp 0+Real.exp (Real.log 3))=(1/4:ℝ) ∧
    Real.exp (Real.log 3)/(Real.exp 0+Real.exp (Real.log 3))=(3/4:ℝ) ∧
    Real.log (Real.exp 0+Real.exp (Real.log 3))=Real.log 4 := by
  rw [Real.exp_zero,Real.exp_log (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Source D.6: exact nonpositive storage polynomial at P=1.8, gamma=3. -/
theorem legacy_d06_storage (x w : ℝ) :
    (9/5)*((4/5)*x+w)^2-(9/5)*x^2≤9*w^2-((3/5)*x)^2 := by
  nlinarith [sq_nonneg (x-5*w)]

/-- Source E.3: full interval equivalence for the discounted harvest cost budget. -/
theorem legacy_e03_feasible_discount (gamma : ℝ) (hg : gamma<1) :
    gamma/(1-gamma)≤9/2 ↔ gamma≤9/11 := by
  rw [div_le_iff₀ (by linarith : 0<1-gamma)]
  constructor <;> intro h <;> linarith

end SafeLearning.PrimersApplied
