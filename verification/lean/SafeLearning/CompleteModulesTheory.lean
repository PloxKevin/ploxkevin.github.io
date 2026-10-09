import SafeLearning.Modules
import SafeLearning.BookApplications

/-! General supporting results. All probability conclusions use actual measures;
matrix Schur complements retain arbitrary finite dimensions. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesTheory

theorem finite_failure_union {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ι → Set Ω)
    (budget : ι → ℝ) (hbound : ∀ i, μ.real (failure i) ≤ budget i) :
    μ.real (⋃ i, failure i) ≤ ∑ i, budget i := by
  exact (measureReal_iUnion_fintype_le failure).trans
    (Finset.sum_le_sum (fun i _ => hbound i))

theorem simultaneous_success {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ι → Set Ω)
    (budget : ι → ℝ) (hmeas : ∀ i, MeasurableSet (failure i))
    (hbound : ∀ i, μ.real (failure i) ≤ budget i) :
    1-(∑ i, budget i) ≤ μ.real (⋂ i, (failure i)ᶜ) := by
  have h := finite_failure_union μ failure budget hbound
  have hm : MeasurableSet (⋃ i, failure i) := MeasurableSet.iUnion hmeas
  have hc := probReal_compl_eq_one_sub (μ := μ) hm
  rw [compl_iUnion] at hc
  linarith

theorem equal_fleet_failure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 20 → Set Ω)
    (hmeas : ∀ i, MeasurableSet (failure i))
    (hbound : ∀ i, μ.real (failure i) ≤ 1/400) :
    19/20 ≤ μ.real (⋂ i, (failure i)ᶜ) := by
  have h := simultaneous_success μ failure (fun _ => 1/400) hmeas hbound
  norm_num at h ⊢
  exact h

theorem independent_success_product {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (success : ι → Set Ω)
    (hindependent : ProbabilityTheory.iIndepSet success μ) :
    μ.real (⋂ i, success i)=∏ i, μ.real (success i) := by
  have h := hindependent.meas_biInter Finset.univ
  simp only [Finset.mem_univ,iInter_true] at h
  simp only [Measure.real,ENNReal.toReal_prod,h]

theorem independent_success_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (success : Fin N → Set Ω)
    (hindependent : ProbabilityTheory.iIndepSet success μ)
    (p : ℝ) (hp : 0 ≤ p) (hbound : ∀ i, p ≤ μ.real (success i)) :
    p^N ≤ μ.real (⋂ i, success i) := by
  rw [independent_success_product μ success hindependent]
  calc
    p^N = ∏ _i : Fin N, p := by simp
    _ ≤ ∏ i, μ.real (success i) := by
      exact Finset.prod_le_prod₀ (fun _ _ => hp) (fun i _ => hbound i)

theorem delayed_deterministic_discounted_violation (gamma : ℝ) (hg : |gamma| < 1)
    (delay : ℕ) :
    (∑' n : ℕ, gamma^(n+delay))=gamma^delay/(1-gamma) := by
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one hg]
  ring

-- A fully dimension-independent positive block Schur complement.
theorem positive_block_schur {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.PosDef) [Invertible A] :
    (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef ↔
      (D-B.conjTranspose*A⁻¹*B).PosSemidef := by
  exact Matrix.PosDef.fromBlocks₁₁ B D hA

theorem positive_block_schur_lower {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hD : D.PosDef) [Invertible D] :
    (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef ↔
      (A-B*D⁻¹*B.conjTranspose).PosSemidef := by
  exact Matrix.PosDef.fromBlocks₂₂ A B hD

-- Tanh's actual derivative and its global scalar incremental sector.
theorem tanh_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hid : Real.cosh x*Real.cosh x-Real.sinh x*Real.sinh x=1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  convert h using 1
  · ext y; exact Real.tanh_eq_sinh_div_cosh y
  · rw [hid]

theorem tanh_derivative_bounds (x : ℝ) :
    0 ≤ 1/(Real.cosh x)^2 ∧ 1/(Real.cosh x)^2 ≤ 1 := by
  have hc := Real.one_le_cosh x
  have hsq : 1 ≤ (Real.cosh x)^2 := by nlinarith
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr hsq

theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x; exact (tanh_derivative x).differentiableAt
  · intro x
    have hb := tanh_derivative_bounds x
    rw [(tanh_derivative x).deriv]
    exact_mod_cast (show ‖(1:ℝ)/(Real.cosh x)^2‖ ≤ 1 by
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]; exact hb.2)

theorem tanh_monotone : Monotone Real.tanh := by
  apply monotone_of_deriv_nonneg
  · intro x; exact (tanh_derivative x).differentiableAt
  · intro x
    rw [(tanh_derivative x).deriv]
    exact (tanh_derivative_bounds x).1

theorem tanh_incremental_sector (x y : ℝ) :
    0 ≤ (Real.tanh x-Real.tanh y)*((x-y)-(Real.tanh x-Real.tanh y)) := by
  have hl := tanh_lipschitz.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
  rcases le_total y x with hxy | hxy
  · have hm := tanh_monotone hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hm),abs_of_nonneg (sub_nonneg.mpr hxy)] at hl
    exact mul_nonneg (sub_nonneg.mpr hm) (by linarith)
  · have hm := tanh_monotone hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hm),abs_of_nonpos (sub_nonpos.mpr hxy)] at hl
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hm) (by linarith)

theorem tanh_global_sector (x : ℝ) :
    0 ≤ Real.tanh x*(x-Real.tanh x) := by
  simpa using tanh_incremental_sector x 0

theorem tanh_concave_nonnegative : ConcaveOn ℝ (Ici 0) Real.tanh := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact tanh_lipschitz.continuous.continuousOn
  · intro x _; exact (tanh_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx0 : 0 ≤ x := interior_subset hx
    have hy0 : 0 ≤ y := interior_subset hy
    have hc : Real.cosh x ≤ Real.cosh y := by
      apply Real.cosh_le_cosh.mpr
      rwa [abs_of_nonneg hx0,abs_of_nonneg hy0]
    rw [(tanh_derivative x).deriv,(tanh_derivative y).deriv]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [Real.cosh_pos x,Real.cosh_pos y]

theorem tanh_chord_lower (radius x : ℝ) (hr : 0 < radius) (hx : x ∈ Icc 0 radius) :
    (Real.tanh radius/radius)*x ≤ Real.tanh x := by
  have hb : 0 ≤ x/radius := div_nonneg hx.1 (le_of_lt hr)
  have ha : 0 ≤ 1-x/radius := by
    have h := (div_le_one hr).mpr hx.2
    linarith
  have hc := tanh_concave_nonnegative.2
    (show (0:ℝ) ∈ Ici 0 by simp) (show radius ∈ Ici 0 from le_of_lt hr)
    ha hb (show (1-x/radius)+(x/radius)=1 by ring)
  simp only [smul_eq_mul,Real.tanh_zero,mul_zero,zero_add] at hc
  rw [show x/radius*radius=x by field_simp] at hc
  convert hc using 1 <;> ring

theorem tanh_local_origin_sector (radius x : ℝ) (hr : 0 < radius)
    (hx : |x| ≤ radius) :
    0 ≤ (Real.tanh x-(Real.tanh radius/radius)*x)*(x-Real.tanh x) := by
  have hglobal := tanh_global_sector x
  by_cases hp : 0 ≤ x
  · have hlo := tanh_chord_lower radius x hr ⟨hp,(abs_le.mp hx).2⟩
    have hpos := tanh_monotone hp
    simp only [Real.tanh_zero] at hpos
    have hupper := tanh_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
      abs_of_nonneg hpos,abs_of_nonneg hp] at hupper
    exact mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hupper)
  · have hlo := tanh_chord_lower radius (-x) hr
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    rw [Real.tanh_neg] at hlo
    have hneg := tanh_monotone (le_of_not_ge hp)
    simp only [Real.tanh_zero] at hneg
    have hupper := tanh_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
      abs_of_nonpos hneg,abs_of_nonpos (le_of_not_ge hp)] at hupper
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by linarith)

def neuralThermalMap (x : ℝ) : ℝ := (9/10)*x-(3/10)*Real.tanh x

theorem neural_thermal_derivative (x : ℝ) :
    HasDerivAt neuralThermalMap ((9/10)-(3/10)/(Real.cosh x)^2) x := by
  have h := ((hasDerivAt_id x).const_mul (9/10:ℝ)).sub
    ((tanh_derivative x).const_mul (3/10:ℝ))
  convert h using 1
  · rfl
  · simp [div_eq_mul_inv]

theorem neural_thermal_lipschitz : LipschitzWith (9/10) neuralThermalMap := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x; exact (neural_thermal_derivative x).differentiableAt
  · intro x
    have hb := tanh_derivative_bounds x
    rw [(neural_thermal_derivative x).deriv]
    have hid : (3/10:ℝ)/(Real.cosh x)^2=(3/10)*(1/(Real.cosh x)^2) := by ring
    rw [hid]
    have hd : |(9/10:ℝ)-(3/10)/(Real.cosh x)^2| ≤ 9/10 := by
      rw [hid]
      rw [abs_le]
      constructor <;> nlinarith
    rw [hid] at hd
    exact_mod_cast hd

theorem neural_thermal_origin_contraction (x : ℝ) :
    |neuralThermalMap x| ≤ (9/10)*|x| := by
  have h := neural_thermal_lipschitz.dist_le_mul x 0
  simpa [Real.dist_eq,neuralThermalMap] using h

theorem neural_thermal_bias_disturbance (x bias disturbance : ℝ)
    (hb : |bias| ≤ 3/100) (hw : |disturbance| ≤ 1/50) :
    |(9/10)*x-(3/10)*Real.tanh (x+bias)+disturbance| ≤
      (9/10)*|x|+29/1000 := by
  have hb' := tanh_lipschitz.dist_le_mul (x+bias) x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_cancel_left] at hb'
  have he : |-(3/10)*(Real.tanh (x+bias)-Real.tanh x)+disturbance| ≤ 29/1000 := by
    calc
      _ ≤ |-(3/10)*(Real.tanh (x+bias)-Real.tanh x)|+|disturbance| := abs_add_le _ _
      _ = (3/10)*|Real.tanh (x+bias)-Real.tanh x|+|disturbance| := by rw [abs_mul]; norm_num
      _ ≤ 29/1000 := by linarith
  calc
    _ = |neuralThermalMap x+(-(3/10)*(Real.tanh (x+bias)-Real.tanh x)+disturbance)| := by
      congr 1; unfold neuralThermalMap; ring
    _ ≤ |neuralThermalMap x|+|-(3/10)*(Real.tanh (x+bias)-Real.tanh x)+disturbance| := abs_add_le _ _
    _ ≤ (9/10)*|x|+29/1000 := by linarith [neural_thermal_origin_contraction x]

theorem biased_actuator_within_limit (x bias : ℝ) (hx : |x| ≤ 1/2)
    (hb : |bias| ≤ 3/100) : |(-3/2)*Real.tanh (x+bias)| < 4/5 := by
  have ht := tanh_lipschitz.dist_le_mul (x+bias) 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul] at ht
  have ha := abs_add_le x bias
  rw [abs_mul]
  norm_num
  linarith

theorem tube_ultimate_bound (x : ℕ → ℝ) (q allowance epsilon : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hepsilon : 0 < epsilon)
    (hstep : ∀ n, |x (n+1)| ≤ q*|x n|+allowance) :
    ∀ᶠ n in Filter.atTop, |x n| < allowance/(1-q)+epsilon := by
  have hp : Filter.Tendsto (fun n : ℕ => q^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have he : Filter.Tendsto
      (fun n : ℕ => allowance/(1-q)+q^n*(|x 0|-allowance/(1-q)))
      Filter.atTop (nhds (allowance/(1-q))) := by
    simpa using (hp.mul_const (|x 0|-allowance/(1-q))).const_add (allowance/(1-q))
  have hev := he.eventually_lt_const (show allowance/(1-q)<allowance/(1-q)+epsilon by linarith)
  filter_upwards [hev] with n hn
  exact (SafeLearning.BookApplications.tube_error_envelope x q allowance hq hq1 hstep n).trans_lt hn

theorem biased_neural_recursive_containment (x bias disturbance : ℕ → ℝ)
    (hzero : |x 0| ≤ 1/2) (hb : ∀ n, |bias n| ≤ 3/100)
    (hw : ∀ n, |disturbance n| ≤ 1/50)
    (hstep : ∀ n, x (n+1)=(9/10)*x n-(3/10)*Real.tanh (x n+bias n)+disturbance n) :
    ∀ n, |x n| ≤ 1/2 ∧ |(-3/2)*Real.tanh (x n+bias n)| < 4/5 := by
  have hi : ∀ n, |x n| ≤ 1/2 := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      rw [hstep]
      have h := neural_thermal_bias_disturbance (x n) (bias n) (disturbance n) (hb n) (hw n)
      linarith
  exact fun n => ⟨hi n,biased_actuator_within_limit (x n) (bias n) (hi n) (hb n)⟩

theorem biased_neural_ultimate_radius (x bias disturbance : ℕ → ℝ)
    (hb : ∀ n, |bias n| ≤ 3/100) (hw : ∀ n, |disturbance n| ≤ 1/50)
    (hstep : ∀ n, x (n+1)=(9/10)*x n-(3/10)*Real.tanh (x n+bias n)+disturbance n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop, |x n| < 29/100+epsilon := by
  have hd : ∀ n, |x (n+1)| ≤ (9/10)*|x n|+29/1000 := by
    intro n
    rw [hstep]
    exact neural_thermal_bias_disturbance (x n) (bias n) (disturbance n) (hb n) (hw n)
  have h := tube_ultimate_bound x (9/10) (29/1000) epsilon
    (by norm_num) (by norm_num) hepsilon hd
  norm_num at h ⊢
  exact h

theorem confidence_recommendation {α : Type*} (f lo hi : α → ℝ)
    (recommendation : α) (epsilon : ℝ)
    (hlower : ∀ x, lo x ≤ f x) (hupper : ∀ x, f x ≤ hi x)
    (hstop : ∀ x, hi x ≤ lo recommendation+epsilon) :
    ∀ x, f x-f recommendation ≤ epsilon := by
  intro x
  linarith [hlower recommendation,hupper x,hstop x]

theorem sampling_grid_margin {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (grid : Set X) (coverRadius margin : ℝ)
    (hgrid : ∀ z ∈ grid, margin ≤ f z)
    (hcover : ∀ x, ∃ z ∈ grid, dist x z ≤ coverRadius)
    (hbudget : L*coverRadius ≤ margin) : ∀ x, 0 ≤ f x := by
  intro x
  obtain ⟨z,hz,hd⟩ := hcover x
  have hf' := hf.dist_le_mul x z
  rw [Real.dist_eq] at hf'
  have hlo := (abs_le.mp hf').1
  have hm := mul_le_mul_of_nonneg_left hd L.coe_nonneg
  linarith [hgrid z hz]

-- A new point needs one certificate per constraint; witnesses may differ.
theorem multiple_constraint_witnesses {X ι : Type*}
    (f lower : ι → X → ℝ) (distance : X → X → ℝ) (L : ι → ℝ)
    (candidate : X)
    (hconfidence : ∀ i z, lower i z ≤ f i z)
    (hlip : ∀ i z, f i z-L i*distance candidate z ≤ f i candidate)
    (hwitness : ∀ i, ∃ z, 0 ≤ lower i z-L i*distance candidate z) :
    ∀ i, 0 ≤ f i candidate := by
  intro i
  obtain ⟨z,hz⟩ := hwitness i
  linarith [hconfidence i z,hlip i z]

end SafeLearning.CompleteModulesTheory
