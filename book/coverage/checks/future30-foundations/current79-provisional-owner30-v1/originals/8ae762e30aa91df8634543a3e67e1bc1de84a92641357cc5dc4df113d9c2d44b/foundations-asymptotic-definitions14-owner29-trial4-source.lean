import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace SafeLearning.CompleteFoundationsAsymptoticDefinitionsWhole30

def sourceBigO (f g : ℕ→ℝ) : Prop :=
  ∃ C : ℝ,0<C ∧ ∃n₀ : ℕ,∀n≥n₀,f n≤C*g n

def sourceOmega (f g : ℕ→ℝ) : Prop :=
  ∃ c : ℝ,0<c ∧ ∃n₀ : ℕ,∀n≥n₀,c*g n≤f n

def sourceTheta (f g : ℕ→ℝ) : Prop := sourceBigO f g ∧ sourceOmega f g

def sourceLittleO (f g : ℕ→ℝ) : Prop :=
  ∀ε : ℝ,0<ε→∃n₀ : ℕ,∀n≥n₀,f n≤ε*g n

def sourceTildeO (f g : ℕ→ℝ) : Prop :=
  ∃k : ℝ,0≤k ∧ sourceBigO f (fun n=>g n*Real.rpow (Real.log n) k)

theorem actual_bigO_positive_constant_and_natural_threshold_iff
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0≤g n) :
    sourceBigO f g ↔ IsBigO atTop f g := by
  constructor
  · rintro ⟨C,hC,n₀,h⟩
    apply isBigO_iff'.mpr
    refine ⟨C,hC,?_⟩
    filter_upwards [hf,hg,eventually_ge_atTop n₀] with n hfn hgn hn
    simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using h n hn
  · intro h
    obtain ⟨C,hC,hb⟩:=isBigO_iff'.mp h
    have htail : ∀ᶠ n in atTop,f n≤C*g n := by
      filter_upwards [hf,hg,hb] with n hfn hgn hn
      simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using hn
    obtain ⟨n₀,hn₀⟩:=eventually_atTop.mp htail
    exact ⟨C,hC,n₀,hn₀⟩

theorem actual_omega_positive_constant_and_natural_threshold_iff
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0≤g n) :
    sourceOmega f g ↔ IsBigO atTop g f := by
  constructor
  · rintro ⟨c,hc,n₀,h⟩
    apply isBigO_iff''.mpr
    refine ⟨c,hc,?_⟩
    filter_upwards [hf,hg,eventually_ge_atTop n₀] with n hfn hgn hn
    simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using h n hn
  · intro h
    obtain ⟨c,hc,hb⟩:=isBigO_iff''.mp h
    have htail : ∀ᶠ n in atTop,c*g n≤f n := by
      filter_upwards [hf,hg,hb] with n hfn hgn hn
      simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using hn
    obtain ⟨n₀,hn₀⟩:=eventually_atTop.mp htail
    exact ⟨c,hc,n₀,hn₀⟩

theorem actual_theta_is_both_upper_and_lower_growth
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0≤g n) :
    sourceTheta f g ↔ IsTheta atTop f g := by
  rw [sourceTheta,actual_bigO_positive_constant_and_natural_threshold_iff f g hf hg,
    actual_omega_positive_constant_and_natural_threshold_iff f g hf hg]
  rfl

theorem actual_littleO_full_epsilon_threshold_iff
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0≤g n) :
    sourceLittleO f g ↔ IsLittleO atTop f g := by
  constructor
  · intro h
    apply isLittleO_iff.mpr
    intro ε hε
    obtain ⟨n₀,hn₀⟩:=h ε hε
    filter_upwards [hf,hg,eventually_ge_atTop n₀] with n hfn hgn hn
    simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using hn₀ n hn
  · intro h ε hε
    have htail : ∀ᶠ n in atTop,f n≤ε*g n := by
      filter_upwards [hf,hg,h.def hε] with n hfn hgn hn
      simpa [Real.norm_eq_abs,abs_of_nonneg hfn,abs_of_nonneg hgn] using hn
    exact eventually_atTop.mp htail

theorem actual_littleO_ratio_equivalence_for_eventually_positive_denominator
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0<g n) :
    sourceLittleO f g ↔ Tendsto (fun n=>f n/g n) atTop (𝓝 0) := by
  rw [actual_littleO_full_epsilon_threshold_iff f g hf (hg.mono fun _ h=>h.le)]
  exact isLittleO_iff_tendsto' (hg.mono fun _ h=>fun hz=>False.elim (h.ne' hz))

theorem actual_littleO_of_zero_denominator_requires_eventual_zero
    (f : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) :
    sourceLittleO f (fun _=>0) ↔ ∀ᶠ n in atTop,f n=0 := by
  constructor
  · intro h
    obtain ⟨n₀,hn₀⟩:=h 1 (by norm_num)
    filter_upwards [hf,eventually_ge_atTop n₀] with n hfn hn
    exact le_antisymm (by simpa using hn₀ n hn) hfn
  · intro h ε hε
    obtain ⟨n₀,hn₀⟩:=eventually_atTop.mp h
    refine ⟨n₀,?_⟩
    intro n hn
    simp [hn₀ n hn]

theorem actual_ratio_zero_alone_does_not_cover_vanishing_denominators :
    Tendsto (fun _ : ℕ=>(1 : ℝ)/0) atTop (𝓝 0) ∧
    ¬sourceLittleO (fun _ : ℕ=>(1 : ℝ)) (fun _=>0) := by
  refine ⟨by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0)),?_⟩
  intro h
  obtain ⟨n₀,hn₀⟩:=h 1 (by norm_num)
  have hb:=hn₀ n₀ le_rfl
  norm_num at hb

theorem actual_small_parameter_bigO_is_the_absolute_value_bound
    (f g : ℝ→ℝ) :
    IsBigO (𝓝 0) f g ↔ ∃ C : ℝ,0<C ∧ ∃δ : ℝ,0<δ ∧
      ∀x : ℝ,|x|<δ→|f x|≤C*|g x| := by
  rw [isBigO_iff']
  apply exists_congr
  intro C
  apply and_congr_right
  intro hC
  rw [Metric.eventually_nhds_iff]
  simp only [Real.norm_eq_abs,Real.dist_eq,sub_zero]

theorem actual_exponential_linear_remainder_bound (x : ℝ) (hx : |x|≤1) :
    |Real.exp x-1-x|≤x^2 := by
  have h:=Real.norm_exp_sub_one_sub_id_le (by simpa [Real.norm_eq_abs] using hx)
  simpa [Real.norm_eq_abs,sq_abs] using h

theorem actual_exponential_expansion_remainder_is_bigO_square :
    IsBigO (𝓝 0) (fun x : ℝ=>Real.exp x-1-x) (fun x=>x^2) := by
  apply (actual_small_parameter_bigO_is_the_absolute_value_bound _ _).mpr
  refine ⟨1,by norm_num,1,by norm_num,?_⟩
  intro x hx
  simpa [abs_of_nonneg (sq_nonneg x)] using actual_exponential_linear_remainder_bound x hx.le

theorem actual_tildeO_hides_a_specified_nonnegative_real_log_power
    (f g : ℕ→ℝ) (hf : ∀ᶠ n in atTop,0≤f n) (hg : ∀ᶠ n in atTop,0≤g n) :
    sourceTildeO f g ↔ ∃k : ℝ,0≤k ∧
      IsBigO atTop f (fun n=>g n*Real.rpow (Real.log n) k) := by
  unfold sourceTildeO
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  apply actual_bigO_positive_constant_and_natural_threshold_iff _ _ hf
  filter_upwards [hg,eventually_ge_atTop (1 : ℕ)] with n hgn hn
  exact mul_nonneg hgn (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) k)

theorem actual_log_n_is_tildeO_one :
    sourceTildeO (fun n : ℕ=>Real.log n) (fun _=>1) := by
  refine ⟨1,by norm_num,1,by norm_num,1,?_⟩
  intro n hn
  simp [Real.rpow_one]

/-- A fixed dimension contributes a legitimate constant in its own asymptotic bound. -/
theorem actual_dimension_dependent_growth_constant (D : ℝ) (hD : 0<D) :
    sourceBigO (fun n : ℕ=>D*n) (fun n=>n) := by
  exact ⟨D,hD,0,fun n _=>le_rfl⟩

/-- Individually valid dimension-dependent constants do not constitute one uniform bound. -/
theorem actual_no_one_growth_constant_is_uniform_over_all_dimensions :
    ¬∃C : ℝ,0<C ∧ ∀D : ℕ,∃n₀ : ℕ,∀n≥n₀,(D : ℝ)*n≤C*n := by
  rintro ⟨C,hC,h⟩
  obtain ⟨D,hD⟩:=exists_nat_gt C
  obtain ⟨n₀,hn₀⟩:=h D
  have hnpos : (0 : ℝ) < max n₀ 1 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right n₀ 1))
  have hb:=hn₀ (max n₀ 1) (le_max_left n₀ 1)
  have hDC : (D : ℝ)≤C := (mul_le_mul_iff_right₀ hnpos).mp (by simpa only [mul_comm] using hb)
  exact hD.not_ge hDC

end SafeLearning.CompleteFoundationsAsymptoticDefinitionsWhole30
