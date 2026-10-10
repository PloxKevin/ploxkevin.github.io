import Mathlib

set_option autoImplicit false

/-! Elementary, source-mapped components of Modules 1–7 and 12–15.
These declarations verify the stated algebraic or order-theoretic steps; they do
not formalize the external papers' analytical/probabilistic theorems. -/
namespace SafeLearning.Modules

-- Modules 1, 2: risk, weak duality, and maximizer ties.
theorem weak_duality_point {reward cost budget multiplier : ℝ}
    (hfeasible : cost ≤ budget) (hmultiplier : 0 ≤ multiplier) :
    reward ≤ reward - multiplier * (cost - budget) := by
  nlinarith [mul_nonneg hmultiplier (sub_nonneg.mpr hfeasible)]

theorem lagrangian_monotone {reward cost budget lo hi : ℝ}
    (hcost : budget ≤ cost) (h : lo ≤ hi) :
    reward - hi * (cost - budget) ≤ reward - lo * (cost - budget) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hcost)]

theorem penalty_strict_separation {safe unsafeReward risk penalty : ℝ}
    (hrisk : 0 < risk) (hpenalty : (unsafeReward - safe) / risk < penalty) :
    unsafeReward - penalty * risk < safe := by
  have h := (div_lt_iff₀ hrisk).mp hpenalty
  nlinarith

theorem penalty_threshold_tie {safe unsafeReward risk : ℝ} (hrisk : risk ≠ 0) :
    unsafeReward - ((unsafeReward - safe) / risk) * risk = safe := by
  field_simp
  <;> ring

theorem count_event_bounds {n horizon : ℕ} (hn : n ≤ horizon) :
    (if n = 0 then 0 else 1 : ℕ) ≤ n ∧
      n ≤ horizon * (if n = 0 then 0 else 1) := by
  split_ifs with h <;> simp_all <;> omega

theorem finite_weighted_event_bounds {ι : Type*} [Fintype ι]
    (weight count : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (_hcount : ∀ i, 0 ≤ count i) (horizon : ℝ)
    (hbound : ∀ i, count i ≤ horizon)
    (hpositive : ∀ i, count i ≠ 0 → 1 ≤ count i) :
    (∑ i, weight i * (if count i = 0 then 0 else 1)) ≤
        ∑ i, weight i * count i ∧
    (∑ i, weight i * count i) ≤
        horizon * ∑ i, weight i * (if count i = 0 then 0 else 1) := by
  constructor
  · apply Finset.sum_le_sum
    intro i _
    split_ifs with hz
    · simp [hz]
    · simpa using mul_le_mul_of_nonneg_left (hpositive i hz) (hweight i)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hz
    · simp [hz]
    · simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hbound i) (hweight i)

-- Modules 2, 12, 14: exact scalar Schur completion and sector QCs.
theorem scalar_schur_completion {a b c x y : ℝ} (hc : c ≠ 0) :
    a*x^2 + 2*b*x*y + c*y^2 =
      (a-b^2/c)*x^2 + c*(y+b*x/c)^2 := by
  field_simp
  <;> ring

theorem negative_quadratic_from_schur {a b c x y : ℝ}
    (hc : c < 0) (hschur : a - b^2/c ≤ 0) :
    a*x^2 + 2*b*x*y + c*y^2 ≤ 0 := by
  rw [scalar_schur_completion (ne_of_lt hc)]
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg hschur (sq_nonneg x))
    (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) (sq_nonneg _))

theorem slope_sector_qc {alpha beta slope delta : ℝ}
    (hlo : alpha ≤ slope) (hhi : slope ≤ beta) :
    -2*alpha*beta*delta^2 +
      2*(alpha+beta)*delta*(slope*delta) - 2*(slope*delta)^2 ≥ 0 := by
  have h := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith [mul_nonneg h (sq_nonneg delta)]

theorem origin_sector_qc {v w alpha beta : ℝ}
    (hsector : (w-alpha*v)*(beta*v-w) ≥ 0) :
    -2*alpha*beta*v^2 + 2*(alpha+beta)*v*w - 2*w^2 ≥ 0 := by
  nlinarith

theorem local_gain_energy {p gamma x u next output : ℝ}
    (hp : 0 ≤ p) (henergy : p*next^2 - p*x^2 + output^2 - gamma^2*u^2 ≤ 0) :
    output^2 ≤ gamma^2*u^2 + p*x^2 := by
  nlinarith [mul_nonneg hp (sq_nonneg next)]

theorem bounded_real_scalar_certificate (x u : ℝ) :
    (1 - 3*(2:ℝ)/4)*x^2 + 2*((2:ℝ)/2)*x*u + ((2:ℝ)-4)*u^2 =
      -(x-2*u)^2/2 := by ring

-- Modules 3–6: confidence intervals and deterministic safe expansion.
theorem lower_confidence_safe {f lower level : ℝ}
    (hconfidence : lower ≤ f) (hcertificate : level ≤ lower) : level ≤ f :=
  le_trans hcertificate hconfidence

theorem lower_cone_safe {fsource ftarget lower L distance level : ℝ}
    (hconfidence : lower ≤ fsource)
    (hlipschitz : fsource - L*distance ≤ ftarget)
    (hcertificate : level ≤ lower - L*distance) : level ≤ ftarget := by
  linarith

theorem bounded_noise_lower_certificate {f observation noise bound : ℝ}
    (hobs : observation = f + noise) (hnoise : noise ≤ bound) :
    observation - bound ≤ f := by linarith

theorem bounded_noise_upper_certificate {f observation noise bound : ℝ}
    (hobs : observation = f + noise) (hnoise : -bound ≤ noise) :
    f ≤ observation + bound := by linarith

theorem interval_intersection_preserves {f lo hi newlo newhi : ℝ}
    (hlo : lo ≤ f) (hhi : f ≤ hi)
    (hnewlo : newlo ≤ f) (hnewhi : f ≤ newhi) :
    max lo newlo ≤ f ∧ f ≤ min hi newhi := by
  exact ⟨max_le hlo hnewlo, le_min hhi hnewhi⟩

theorem nested_interval_width {lo hi newlo newhi : ℝ}
    (hlo : lo ≤ newlo) (hhi : newhi ≤ hi) : newhi-newlo ≤ hi-lo := by linarith

theorem cone_radius_certificate {lower level L radius distance : ℝ}
    (hL : 0 ≤ L) (hradius : lower-level = L*radius)
    (hdistance : distance ≤ radius) : level ≤ lower-L*distance := by
  nlinarith [mul_le_mul_of_nonneg_left hdistance hL]

theorem safe_expansion_preserves {α : Type*} (safe expanded truth : Set α)
    (hseed : safe ⊆ truth) (hnew : expanded ⊆ truth) :
    safe ∪ expanded ⊆ truth := by
  intro x hx
  exact hx.elim (hseed ·) (hnew ·)

theorem monotone_safety_expansion {α : Type*} (safe expanded : Set α) :
    safe ⊆ safe ∪ expanded := by exact Set.subset_union_left

theorem backup_margin_safe {value lower L distance displacement : ℝ}
    (hvalue : lower-L*(distance+displacement) ≤ value)
    (hcertificate : L*(distance+displacement) ≤ lower) : 0 ≤ value := by
  linarith

theorem robust_triangle_margin {L d e movement lower : ℝ}
    (hL : 0 ≤ L) (hd : d ≤ e + movement)
    (hmargin : L*(e+movement) ≤ lower) : L*d ≤ lower := by
  exact le_trans (mul_le_mul_of_nonneg_left hd hL) hmargin

theorem tighter_backup_union {α : Type*} (old new : Set α)
    (radiusOld radiusNew distance : α → ℝ)
    (hstores : old ⊆ new) (hradius : ∀ a ∈ old, radiusOld a ≤ radiusNew a) :
    {x | ∃ a ∈ old, distance x ≤ radiusOld a} ⊆
      {x | ∃ a ∈ new, distance x ≤ radiusNew a} := by
  rintro x ⟨a, ha, hx⟩
  exact ⟨a, hstores ha, le_trans hx (hradius a ha)⟩

-- Modules 7, 13, 14: clipping, margins, and weighted singular values.
theorem quadratic_braking_identity (position velocity acceleration : ℝ)
    (ha : acceleration ≠ 0) :
    position + velocity*(velocity/acceleration) -
      acceleration*(velocity/acceleration)^2/2 =
      position + velocity^2/(2*acceleration) := by
  field_simp
  <;> ring

theorem unsafe_peak_lower_bound {actual peak wall : ℝ}
    (hactual : peak ≤ actual) (hpeak : wall ≤ peak) : wall ≤ actual :=
  le_trans hpeak hactual

theorem sampled_barrier_factor {h rate step : ℝ}
    (hh : 0 ≤ h) (hfactor : rate*step ≤ 1) : 0 ≤ (1-rate*step)*h := by
  exact mul_nonneg (by linarith) hh

theorem sandwich_scalar_bound {a b q : ℝ} (ha : 0 < a)
    (hconstraint : b^2 ≤ a*q) : b^2/a ≤ q := by
  exact (div_le_iff₀ ha).mpr (by nlinarith)

theorem safe_output_margin {baseline displacement bound level : ℝ}
    (hbaseline : level+bound ≤ baseline)
    (hchange : -bound ≤ displacement) : level ≤ baseline+displacement := by
  linarith

theorem contraction_weight_relation {sigma a : ℝ}
    (_hsigma : 0 ≤ sigma) (ha : 0 ≤ a) (hsq : sigma^2 ≤ a^2) : sigma ≤ a := by
  nlinarith

theorem two_layer_gain {gain1 gain2 bound1 bound2 : ℝ}
    (hg1 : 0 ≤ gain1) (hg2 : 0 ≤ gain2)
    (hb1 : gain1 ≤ bound1) (hb2 : gain2 ≤ bound2) :
    gain1*gain2 ≤ bound1*bound2 := by
  exact mul_le_mul hb1 hb2 hg2 (le_trans hg1 hb1)

-- Module 15: concentration-bound arithmetic (not probability theorems).
theorem empirical_margin_transfer {observed trueValue error tolerance : ℝ}
    (herror : |observed-trueValue| ≤ error)
    (hobserved : observed+error ≤ tolerance) : trueValue ≤ tolerance := by
  have h := (abs_le.mp herror).1
  linarith

theorem mixture_failure_bound {bad goodMass badMass badRate goodRate : ℝ}
    (hbad : bad ≤ goodMass*goodRate+badMass*badRate)
    (hgood : goodRate ≤ 0) (hbadRate : badRate ≤ 1)
    (hg : 0 ≤ goodMass) (hb : 0 ≤ badMass) : bad ≤ badMass := by
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hg hgood,
    mul_le_mul_of_nonneg_left hbadRate hb]

-- Modules 3 and 5: real Hilbert-space reasoning behind RKHS certificates.
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem representer_difference (f kx ky : H) :
    inner ℝ f kx - inner ℝ f ky = inner ℝ f (kx-ky) := by
  simp only [inner_sub_right]

theorem representer_lipschitz (f kx ky : H) :
    |inner ℝ f kx - inner ℝ f ky| ≤ ‖f‖ * ‖kx-ky‖ := by
  rw [representer_difference]
  exact abs_real_inner_le_norm _ _

theorem orthogonal_residual_norm (s residual : H)
    (horthogonal : inner ℝ s residual = 0) :
    ‖s+residual‖^2 = ‖s‖^2 + ‖residual‖^2 := by
  rw [norm_add_sq_real, horthogonal]
  ring

theorem orthogonal_scalar_residual_norm (s residual : H) (c : ℝ)
    (horthogonal : inner ℝ s residual = 0) :
    ‖s+c • residual‖^2 = ‖s‖^2 + c^2*‖residual‖^2 := by
  rw [norm_add_sq_real, inner_smul_right, horthogonal, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem projection_minimum_norm (s residual : H)
    (horthogonal : inner ℝ s residual = 0) : ‖s‖ ≤ ‖s+residual‖ := by
  have h := orthogonal_residual_norm s residual horthogonal
  nlinarith [norm_nonneg s, norm_nonneg (s+residual), sq_nonneg ‖residual‖]

theorem extremal_residual_budget {B snorm sigma c : ℝ}
    (hB : 0 ≤ B) (hsnorm : 0 ≤ snorm) (hbudget : snorm ≤ B)
    (hsigma : 0 < sigma)
    (hc : c = -Real.sqrt (B^2-snorm^2)/sigma) :
    snorm^2+c^2*sigma^2 = B^2 := by
  have hnonneg : 0 ≤ B^2-snorm^2 := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  rw [hc]
  field_simp
  nlinarith
end Hilbert

-- Modules 12–14: general QC and S-procedure implications.
theorem diagonal_sector_aggregation {ι : Type*} [Fintype ι]
    (weight qc : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hqc : ∀ i, 0 ≤ qc i) : 0 ≤ ∑ i, weight i*qc i := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hweight i) (hqc i))

theorem s_procedure {α : Type*} (target constraint : α → ℝ)
    (multiplier : ℝ) (hmultiplier : 0 ≤ multiplier)
    (hglobal : ∀ x, target x + multiplier*constraint x ≤ 0) :
    ∀ x, 0 ≤ constraint x → target x ≤ 0 := by
  intro x hx
  have h := mul_nonneg hmultiplier hx
  linarith [hglobal x]

theorem s_procedure_multiple {α ι : Type*} [Fintype ι]
    (target : α → ℝ) (constraint : ι → α → ℝ) (multiplier : ι → ℝ)
    (hmultiplier : ∀ i, 0 ≤ multiplier i)
    (hglobal : ∀ x, target x + ∑ i, multiplier i*constraint i x ≤ 0) :
    ∀ x, (∀ i, 0 ≤ constraint i x) → target x ≤ 0 := by
  intro x hx
  have hnonneg : 0 ≤ ∑ i, multiplier i*constraint i x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hmultiplier i) (hx i))
  linarith [hglobal x]

theorem relu_sector (x : ℝ) : (max x 0)*(x-max x 0) = 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]; ring
  · rw [max_eq_right (le_of_not_ge hx)]; ring

theorem relu_exact_qc_counterexample :
    (2:ℝ)*1 - 1^2 ≥ 0 ∧ max (2:ℝ) 0 ≠ 1 := by norm_num

theorem positive_scalar_relu (a x : ℝ) (ha : 0 ≤ a) :
    max (a*x) 0 = a*max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (mul_nonneg ha hx)]
  · rw [max_eq_right (le_of_not_ge hx),
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hx))]
    ring

theorem scalar_sandwich_relu (a b x : ℝ) :
    2*a*max (b*x) 0 = a*(max (b*x) 0)*2 := by ring

theorem scalar_sandwich_positive_reduction (a b x : ℝ) (hb : 0 ≤ b) :
    2*a*max (b*x) 0 = 2*a*b*max x 0 := by
  rw [positive_scalar_relu b x hb]
  ring

theorem off_diagonal_qc_counterexample :
    2*((3/2:ℝ)-1)*(0-1)-2*(0-1)^2 = -3 := by norm_num

-- Exact tail calculation for Exercise 1.2, including a split probability atom.
noncomputable def excursionTailSum (nu : ℝ) : ℝ :=
    max (-3/5-nu) 0 + max (-1/2-nu) 0 + max (-2/5-nu) 0 +
    max (-3/10-nu) 0 + max (-1/5-nu) 0 + max (-1/10-nu) 0 +
    max (0-nu) 0 + max (1/5-nu) 0 + max (1/2-nu) 0 + max (3/2-nu) 0

theorem excursion_mean :
    ((-3/5:ℝ)-1/2-2/5-3/10-1/5-1/10+0+1/5+1/2+3/2)/10 = 1/100 := by
  norm_num

theorem excursion_ru_nine_tenths_lower (nu : ℝ) :
    (3/2:ℝ) ≤ nu + excursionTailSum nu := by
  unfold excursionTailSum
  linarith [le_max_right (-3/5-nu) 0, le_max_right (-1/2-nu) 0,
    le_max_right (-2/5-nu) 0, le_max_right (-3/10-nu) 0,
    le_max_right (-1/5-nu) 0, le_max_right (-1/10-nu) 0,
    le_max_right (0-nu) 0, le_max_right (1/5-nu) 0,
    le_max_right (1/2-nu) 0, le_max_left (3/2-nu) 0]

theorem excursion_ru_nine_tenths_attained :
    (1/2:ℝ) + excursionTailSum (1/2) = 3/2 := by
  norm_num [excursionTailSum]

theorem excursion_ru_three_quarters_lower (nu : ℝ) :
    (21/25:ℝ) ≤ nu + (2/5)*excursionTailSum nu := by
  unfold excursionTailSum
  linarith [le_max_right (-3/5-nu) 0, le_max_right (-1/2-nu) 0,
    le_max_right (-2/5-nu) 0, le_max_right (-3/10-nu) 0,
    le_max_right (-1/5-nu) 0, le_max_right (-1/10-nu) 0,
    le_max_right (0-nu) 0, le_max_right (1/5-nu) 0,
    le_max_left (1/5-nu) 0, le_max_left (1/2-nu) 0,
    le_max_left (3/2-nu) 0]

theorem excursion_ru_three_quarters_attained :
    (1/5:ℝ) + (2/5)*excursionTailSum (1/5) = 21/25 := by
  norm_num [excursionTailSum]

-- Actual iteration-level safe-expansion induction, not just a single implication.
theorem confidence_cone_iteration {α : Type*}
    (safe : ℕ → Set α) (f : α → ℝ) (lower : ℕ → α → ℝ)
    (distance : α → α → ℝ) (L level : ℝ)
    (hseed : ∀ x ∈ safe 0, level ≤ f x)
    (hconfidence : ∀ n x, lower n x ≤ f x)
    (hregularity : ∀ a x, f a - L*distance a x ≤ f x)
    (hupdate : ∀ n, safe (n+1) = safe n ∪
      {x | ∃ a ∈ safe n, level ≤ lower n a - L*distance a x}) :
    ∀ n x, x ∈ safe n → level ≤ f x := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro x hx
    rw [hupdate n] at hx
    rcases hx with hx | ⟨a, ha, hcone⟩
    · exact ih x hx
    · exact lower_cone_safe (hconfidence n a) (hregularity a x) hcone

theorem losbo_iteration {α : Type*}
    (safe : ℕ → Set α) (f : α → ℝ) (query : ℕ → α)
    (observation noise : ℕ → ℝ) (distance : α → α → ℝ) (E L level : ℝ)
    (hseed : ∀ x ∈ safe 0, level ≤ f x)
    (hobs : ∀ n, observation n = f (query n) + noise n)
    (hnoise : ∀ n, noise n ≤ E)
    (hregularity : ∀ a x, f a - L*distance a x ≤ f x)
    (hupdate : ∀ n, safe (n+1) = safe n ∪
      {x | level ≤ observation n-E-L*distance (query n) x}) :
    ∀ n x, x ∈ safe n → level ≤ f x := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro x hx
    rw [hupdate n] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · exact lower_cone_safe
        (bounded_noise_lower_certificate (hobs n) (hnoise n))
        (hregularity (query n) x) hx

theorem lipschitz_zero_cone {observation E level distance : ℝ} :
    (level ≤ observation-E-0*distance) ↔ level ≤ observation-E := by ring_nf

theorem invariant_closed_loop {α β : Type*} (f : α → β → α)
    (policy : α → β) (safe : Set α) (trajectory : ℕ → α)
    (hstart : trajectory 0 ∈ safe)
    (hstep : ∀ x ∈ safe, f x (policy x) ∈ safe)
    (hdynamics : ∀ n, trajectory (n+1) = f (trajectory n) (policy (trajectory n))) :
    ∀ n, trajectory n ∈ safe := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih => rw [hdynamics n]; exact hstep (trajectory n) ih

theorem local_certificate_sublevel_invariance {α : Type*}
    (f : α → α) (V : α → ℝ) (validity : Set α) (c : ℝ)
    (hcontainment : ∀ x, V x ≤ c → x ∈ validity)
    (hdecrease : ∀ x ∈ validity, V (f x) ≤ V x) :
    ∀ x, V x ≤ c → V (f x) ≤ c := by
  intro x hx
  exact le_trans (hdecrease x (hcontainment x hx)) hx

theorem viability_iteration_descending {α β : Type*}
    (f : α → β → α) (C : Set α) (kernel : ℕ → Set α)
    (hzero : kernel 0 = C)
    (hstep : ∀ n, kernel (n+1) = C ∩ {x | ∃ u, f x u ∈ kernel n}) :
    ∀ n, kernel (n+1) ⊆ kernel n := by
  intro n
  induction n with
  | zero =>
    rw [hstep 0, hzero]
    exact Set.inter_subset_left
  | succ n ih =>
    intro x hx
    rw [hstep (n+1)] at hx
    rw [hstep n]
    rcases hx with ⟨hC, u, hu⟩
    exact ⟨hC, u, ih hu⟩

theorem invariant_set_survives_viability_iteration {α β : Type*}
    (f : α → β → α) (C S : Set α) (kernel : ℕ → Set α)
    (hzero : kernel 0 = C)
    (hstep : ∀ n, kernel (n+1) = C ∩ {x | ∃ u, f x u ∈ kernel n})
    (hSC : S ⊆ C) (hinvariant : ∀ x ∈ S, ∃ u, f x u ∈ S) :
    ∀ n, S ⊆ kernel n := by
  intro n
  induction n with
  | zero => rw [hzero]; exact hSC
  | succ n ih =>
    intro x hx
    rw [hstep n]
    obtain ⟨u, hu⟩ := hinvariant x hx
    exact ⟨hSC hx, u, ih hu⟩

-- Module 15's exact d=3 scenario-tail values; no distributional premise is inferred.
set_option exponentiation.threshold 1000 in
theorem scenario_60_tail_above :
    (9/10:ℚ)^60 + 60*(1/10)*(9/10)^59 +
      1770*(1/10)^2*(9/10)^58 > 1/20 := by norm_num

set_option exponentiation.threshold 1000 in
theorem scenario_61_tail_below :
    (9/10:ℚ)^61 + 61*(1/10)*(9/10)^60 +
      1830*(1/10)^2*(9/10)^59 ≤ 1/20 := by norm_num

theorem scenario_choose_60 : Nat.choose 60 2 = 1770 := by decide
theorem scenario_choose_61 : Nat.choose 61 2 = 1830 := by decide

theorem scenario_tail_step (k : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p)^(k+3) + (k+3)*p*(1-p)^(k+2) +
      (((k:ℝ)+3)*(k+2)/2)*p^2*(1-p)^(k+1) ≤
    (1-p)^(k+2) + (k+2)*p*(1-p)^(k+1) +
      (((k:ℝ)+2)*(k+1)/2)*p^2*(1-p)^k := by
  have hpow : 0 ≤ (1-p)^k := pow_nonneg (by linarith) _
  have hp3 : 0 ≤ p^3 := pow_nonneg hp _
  have hncast : 0 ≤ ((k:ℝ)+2)*(k+1)/2 := by positivity
  have hdiff :
    ((1-p)^(k+2) + (k+2)*p*(1-p)^(k+1) +
      (((k:ℝ)+2)*(k+1)/2)*p^2*(1-p)^k) -
    ((1-p)^(k+3) + (k+3)*p*(1-p)^(k+2) +
      (((k:ℝ)+3)*(k+2)/2)*p^2*(1-p)^(k+1)) =
    (((k:ℝ)+2)*(k+1)/2)*p^3*(1-p)^k := by
    simp only [pow_add, pow_one]
    ring
  have hnonneg := mul_nonneg (mul_nonneg hncast hp3) hpow
  linarith

-- Entropy-temperature monotonicity follows from two optimality inequalities.
theorem temperature_entropy_monotone {alpha beta rewardA rewardB entropyA entropyB : ℝ}
    (htemperature : alpha < beta)
    (hoptA : rewardB+alpha*entropyB ≤ rewardA+alpha*entropyA)
    (hoptB : rewardA+beta*entropyA ≤ rewardB+beta*entropyB) :
    entropyA ≤ entropyB := by nlinarith

theorem temperature_reward_monotone {alpha beta rewardA rewardB entropyA entropyB : ℝ}
    (halpha : 0 ≤ alpha) (htemperature : alpha < beta)
    (hoptA : rewardB+alpha*entropyB ≤ rewardA+alpha*entropyA)
    (hoptB : rewardA+beta*entropyA ≤ rewardB+beta*entropyB) :
    rewardB ≤ rewardA := by
  have hentropy := temperature_entropy_monotone htemperature hoptA hoptB
  nlinarith [mul_nonneg halpha (sub_nonneg.mpr hentropy)]

theorem maximum_probability_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (probability : ι → ℝ) (peak : ℝ)
    (hmass : ∑ i, probability i = 1) (hpeak : ∀ i, probability i ≤ peak) :
    1/(Fintype.card ι : ℝ) ≤ peak := by
  have hcard : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpeak i)
  simpa [hmass, Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

theorem modal_action_safe {ι : Type*} [Fintype ι] [Nonempty ι]
    (probability : ι → ℝ) (critical : Set ι) (mode : ι) (delta : ℝ)
    (hmass : ∑ i, probability i = 1)
    (hmode : ∀ i, probability i ≤ probability mode)
    (hcritical : ∀ i ∈ critical, probability i ≤ delta)
    (hdelta : delta < 1/(Fintype.card ι : ℝ)) : mode ∉ critical := by
  intro hm
  have hpeak := maximum_probability_lower_bound probability (probability mode) hmass hmode
  linarith [hcritical mode hm]

-- Generic two-dimensional Cayley orthogonality and determinant identity.
theorem cayley_plane_unit_circle (a : ℝ) :
    ((1-a^2)/(1+a^2))^2 + ((2*a)/(1+a^2))^2 = 1 := by
  have hden : 1+a^2 ≠ 0 := by nlinarith [sq_nonneg a]
  field_simp
  <;> ring

theorem cayley_plane_orthogonal_action (a x y : ℝ) :
    (((1-a^2)/(1+a^2))*x - ((2*a)/(1+a^2))*y)^2 +
    (((2*a)/(1+a^2))*x + ((1-a^2)/(1+a^2))*y)^2 = x^2+y^2 := by
  have hcircle := cayley_plane_unit_circle a
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem cayley_plane_no_minus_one (a x y : ℝ)
    (hx : ((1-a^2)/(1+a^2))*x - ((2*a)/(1+a^2))*y = -x)
    (hy : ((2*a)/(1+a^2))*x + ((1-a^2)/(1+a^2))*y = -y) :
    x=0 ∧ y=0 := by
  have hden : 1+a^2 ≠ 0 := by nlinarith [sq_nonneg a]
  field_simp at hx hy
  have hxy : x=a*y := by nlinarith [hx]
  have hyx : y= -a*x := by nlinarith [hy]
  have hxmul : (1+a^2)*x = 0 := by
    calc
      (1+a^2)*x = x+a^2*x := by ring
      _ = a*y+a^2*x := by rw [hxy]
      _ = a*(-a*x)+a^2*x := by rw [hyx]
      _ = 0 := by ring
  have hx0 : x=0 := (mul_eq_zero.mp hxmul).resolve_left hden
  exact ⟨hx0, by simpa [hx0] using hyx⟩

theorem cayley_half_entries :
    ((1-(1/2:ℝ)^2)/(1+(1/2:ℝ)^2)=3/5) ∧
    ((2*(1/2:ℝ))/(1+(1/2:ℝ)^2)=4/5) := by norm_num

theorem two_tap_dissipation_telescoping (storage inputEnergy outputEnergy : ℕ → ℝ)
    (gainSq : ℝ) (hstep : ∀ n, storage (n+1)-storage n ≤
      gainSq*inputEnergy n-outputEnergy n) :
    ∀ n, storage n-storage 0 ≤ gainSq*(∑ k ∈ Finset.range n, inputEnergy k)-
      ∑ k ∈ Finset.range n, outputEnergy k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linarith [hstep n]

theorem finite_energy_gain (storage inputEnergy outputEnergy : ℕ → ℝ)
    (gainSq : ℝ) (hstep : ∀ n, storage (n+1)-storage n ≤
      gainSq*inputEnergy n-outputEnergy n)
    (hinitial : storage 0=0) (hnonnegative : ∀ n, 0 ≤ storage n) :
    ∀ n, (∑ k ∈ Finset.range n, outputEnergy k) ≤
      gainSq*(∑ k ∈ Finset.range n, inputEnergy k) := by
  intro n
  have h := two_tap_dissipation_telescoping storage inputEnergy outputEnergy gainSq hstep n
  rw [hinitial] at h
  linarith [hnonnegative n]

-- Finite circular aliasing refutes an unrestricted single-tap converse.
theorem circular_three_tap_orthogonal :
    let C : Matrix (Fin 3) (Fin 3) ℚ :=
      Matrix.of ![![-1/3,2/3,2/3],![2/3,-1/3,2/3],![2/3,2/3,-1/3]]
    C.transpose * C = 1 ∧ ∀ i j, C i j ≠ 0 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.one_apply, Fin.sum_univ_three]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num

end SafeLearning.Modules
