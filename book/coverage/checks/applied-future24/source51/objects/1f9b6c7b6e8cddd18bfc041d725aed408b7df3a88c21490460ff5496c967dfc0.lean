import SafeLearning.CoreModules

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal NNReal
namespace SafeLearning.CoreAnalysis

theorem hoeffding_radius_above_target : (1/100 : ℝ) < Real.sqrt (Real.log 20/2000) := by
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 20 by norm_num)
  norm_num at hl
  have hnonneg : 0 ≤ Real.log 20/2000 := by positivity
  have hs := Real.sq_sqrt hnonneg
  have hr := Real.sqrt_nonneg (Real.log 20/2000)
  nlinarith

theorem validation_single_minimal (n : ℕ) :
    (99/100 : ℚ)^n ≤ 1/20 ↔ 299 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn' : n ≤ 298 := by omega
    have hm : (99/100 : ℚ)^298 ≤ (99/100 : ℚ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn'
    exact (not_lt_of_ge (hm.trans h)) CoreModules.lyapunov_p11_single.2
  · intro hn
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans
      CoreModules.lyapunov_p11_single.1

theorem validation_twenty_minimal (n : ℕ) :
    (99/100 : ℚ)^n ≤ 1/400 ↔ 597 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn' : n ≤ 596 := by omega
    have hm : (99/100 : ℚ)^596 ≤ (99/100 : ℚ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn'
    exact (not_lt_of_ge (hm.trans h)) CoreModules.lyapunov_p11_twenty.2
  · intro hn
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans
      CoreModules.lyapunov_p11_twenty.1

theorem discounted_budget_telescopes (z c : ℕ → ℝ) (γ budget : ℝ)
    (h₀ : z 0 = budget) (hstep : ∀ n, γ*z (n+1) = z n-c n) :
    ∀ n, budget-∑ t ∈ Finset.range n, γ^t*c t = γ^n*z n := by
  intro n
  induction n with
  | zero => simp [h₀]
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h := congrArg (fun w : ℝ => γ^n*w) (hstep n)
    nlinarith

-- General induction and a limit, not a finite simulation:11.P10, op-B1.
theorem geometric_bound (e : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ n, e (n+1) ≤ q*e n) (n : ℕ) : e n ≤ q^n*e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc e (n+1) ≤ q*e n := hstep n
      _ ≤ q*(q^n*e 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q^(n+1)*e 0 := by ring

theorem geometric_convergence (x : ℕ → ℝ) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hstep : ∀ n, |x (n+1)| ≤ q*|x n|) : Tendsto x atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa [Real.norm_eq_abs] using geometric_bound (fun n => |x n|) q hq₀ hstep n
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).mul_const |x 0|

theorem relative_error_convergence (x e : ℕ → ℝ)
    (hstep : ∀ n, x (n+1) = (1/2)*x n+e n)
    (he : ∀ n, |e n| ≤ (1/10)*|x n|) : Tendsto x atTop (𝓝 0) := by
  apply geometric_convergence x (3/5) (by norm_num) (by norm_num)
  intro n
  rw [hstep]
  exact CoreModules.lyapunov_p10_relative (x n) (e n) (he n)

-- The nonlinear11.P9 has no fixed geometric contraction factor on[-1,1].
-- Instead prove the explicit polynomial envelope x_n² ≤1/(n+1).
theorem nonlinear_envelope (x : ℕ → ℝ) (h₀ : (x 0)^2 ≤ 1)
    (hstep : ∀ n, x (n+1) = x n-(x n)^3) :
    ∀ n : ℕ, (x n)^2 ≤ 1/(n+1 : ℝ) := by
  intro n
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    have hn : (0 : ℝ) < n+1 := by positivity
    have hn' : (0 : ℝ) < n+1+1 := by positivity
    have hv : (0 : ℝ) ≤ (x n)^2 := sq_nonneg _
    have hb : (x n)^2 ≤ 1 := by
      have : 1/(n+1 : ℝ) ≤ 1 := by rw [div_le_iff₀ hn]; norm_num
      exact ih.trans this
    have hbudget : (n+1 : ℝ)*(x n)^2 ≤ 1 := by
      have := (le_div_iff₀ hn).mp ih
      nlinarith
    have hrec : (x (n+1))^2*(1+(x n)^2) ≤ (x n)^2 := by
      rw [hstep]
      have haux : 0 ≤ (x n)^4*(1+(x n)^2-(x n)^4) := by
        apply mul_nonneg (by positivity)
        nlinarith [mul_nonneg hv (by linarith : 0 ≤ 1-(x n)^2)]
      nlinarith
    have hnonneg := sq_nonneg (x (n+1))
    have hproduct := mul_nonneg hnonneg (by linarith : 0 ≤ 1-(n+1 : ℝ)*(x n)^2)
    have hscaled := mul_le_mul_of_nonneg_left hrec (le_of_lt hn)
    rw [Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hn').mpr
    nlinarith

theorem nonlinear_convergence (x : ℕ → ℝ) (h₀ : (x 0)^2 ≤ 1)
    (hstep : ∀ n, x (n+1) = x n-(x n)^3) : Tendsto x atTop (𝓝 0) := by
  have hv : Tendsto (fun n => (x n)^2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg (x n)) (nonlinear_envelope x h₀ hstep)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have ha : Tendsto (fun n => |x n|) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hv
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using ha)

-- Union bounds use actual measures. No independence between these events is assumed.
theorem finite_union_bound {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (bad : I → Set Ω) (δ : I → ℝ≥0∞)
    (h : ∀ i, μ (bad i) ≤ δ i) : μ (⋃ i, bad i) ≤ ∑ i, δ i := by
  exact (measure_iUnion_fintype_le μ bad).trans (Finset.sum_le_sum fun i _ => h i)

theorem compose_failure_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad E F : Set Ω) (α β : ℝ≥0∞)
    (hcover : bad ⊆ E ∪ F) (hE : μ E ≤ α) (hF : μ F ≤ β) :
    μ bad ≤ α+β := by
  exact (measure_mono hcover).trans ((measure_union_le E F).trans (add_le_add hE hF))

-- Pointwise interpolation is explicit about both its model error and geometry.
theorem sampled_lower_certificate {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (x z : X)
    (m r : ℝ) (hz : m ≤ f z) (hr : dist x z ≤ r) :
    m-L*r ≤ f x := by
  have hd := hf.dist_le_mul x z
  rw [Real.dist_eq] at hd
  have ha := (abs_le.mp hd).1
  have hb := mul_le_mul_of_nonneg_left hr L.coe_nonneg
  linarith

theorem sampled_upper_certificate {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (x z : X)
    (m r : ℝ) (hz : f z ≤ m) (hr : dist x z ≤ r) :
    f x ≤ m+L*r := by
  have hd := hf.dist_le_mul x z
  rw [Real.dist_eq] at hd
  have ha := (abs_le.mp hd).2
  have hb := mul_le_mul_of_nonneg_left hr L.coe_nonneg
  linarith

-- op-F2: exact strictly positive margin for the corrected concrete grid.
theorem strict_grid_margin : (1/10 : ℝ)-50*((1/251)/2) = 1/2510 ∧
    (1/2510 : ℝ) > 0 ∧ (251 : ℕ)^2 = 63001 := by norm_num

-- op-S3: a concrete rational witness refutes positive semidefiniteness.
theorem rounded_lmi_not_psd :
    (1 : ℚ)^2+2*(1 : ℚ)*(-1)+(1-1/1000000000 : ℚ)*(-1)^2 < 0 := by norm_num

-- op-B1: disturbance/parameter accumulation uses the whole finite geometric sum.
theorem affine_error_bound (e : ℕ → ℝ) (L a : ℝ) (hL : 0 ≤ L)
    (hzero : e 0 = 0) (hstep : ∀ n, e (n+1) ≤ L*e n+a) :
    ∀ n, e n ≤ a*∑ i ∈ Finset.range n, L^i := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hs : L*(∑ i ∈ Finset.range n, L^i)+1 = ∑ i ∈ Finset.range (n+1), L^i := by
      clear ih
      induction n with
      | zero => simp
      | succ n ih => simp only [Finset.sum_range_succ] at *; rw [pow_succ]; nlinarith
    calc e (n+1) ≤ L*e n+a := hstep n
      _ ≤ L*(a*∑ i ∈ Finset.range n, L^i)+a := by nlinarith [mul_le_mul_of_nonneg_left ih hL]
      _ = a*∑ i ∈ Finset.range (n+1), L^i := by rw [← hs]; ring

end SafeLearning.CoreAnalysis
