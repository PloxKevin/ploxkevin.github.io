import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal
namespace SafeLearning.CompleteFoundationsUniformConvergenceModels

/-- An extended nonnegative supremum also represents errors that are unbounded. -/
def actualSupError {X : Type*} (F : ℕ → X → ℝ) (f : X → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal |F n x-f x|

theorem actual_pointwise_convergence_definition {X : Type*}
    (F : ℕ → X → ℝ) (f : X → ℝ) :
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) ↔
      ∀ x, ∀ ε : ℝ, 0<ε → ∃ T : ℕ, ∀ n≥T, |F n x-f x|<ε := by
  simp only [Metric.tendsto_atTop,Real.dist_eq]

theorem actual_uniform_convergence_definition {X : Type*}
    (F : ℕ → X → ℝ) (f : X → ℝ) :
    TendstoUniformly F f atTop ↔
      ∀ ε : ℝ, 0<ε → ∃ T : ℕ, ∀ n≥T, ∀ x, |F n x-f x|<ε := by
  rw [Metric.tendstoUniformly_iff]
  simp only [Real.dist_eq,abs_sub_comm,eventually_atTop]

theorem actual_uniform_convergence_iff_the_actual_supremum_error_tends_to_zero
    {X : Type*} (F : ℕ → X → ℝ) (f : X → ℝ) :
    TendstoUniformly F f atTop ↔
      Tendsto (actualSupError F f) atTop (𝓝 0) := by
  rw [actual_uniform_convergence_definition,ENNReal.tendsto_nhds_zero]
  constructor
  · intro h ε hε
    by_cases ht : ε=∞
    · subst ε; exact Eventually.of_forall (fun _ => le_top)
    · have he : 0<ε.toReal := ENNReal.toReal_pos hε.ne' ht
      obtain ⟨T,hT⟩ := h ε.toReal he
      refine eventually_atTop.mpr ⟨T,fun n hn => ?_⟩
      apply iSup_le
      intro x
      simpa only [ENNReal.ofReal_toReal ht] using
        ENNReal.ofReal_le_ofReal (hT n hn x).le
  · intro h ε hε
    have he : 0<ENNReal.ofReal (ε/2) := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨T,hT⟩ := eventually_atTop.mp (h _ he)
    refine ⟨T,fun n hn x => ?_⟩
    have hs : ENNReal.ofReal |F n x-f x| ≤ ENNReal.ofReal (ε/2) :=
      (le_iSup (fun y => ENNReal.ofReal |F n y-f y|) x).trans (hT n hn)
    have ha := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤ε/2)).mp hs
    linarith

theorem actual_uniform_convergence_implies_pointwise_convergence {X : Type*}
    (F : ℕ → X → ℝ) (f : X → ℝ) (h : TendstoUniformly F f atTop) :
    ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  rw [actual_pointwise_convergence_definition]
  intro x ε hε
  obtain ⟨T,hT⟩ := (actual_uniform_convergence_definition F f).mp h ε hε
  exact ⟨T,fun n hn => hT n hn x⟩

theorem actual_finite_domain_pointwise_convergence_implies_uniform_convergence
    {X : Type*} [Fintype X] (F : ℕ → X → ℝ) (f : X → ℝ)
    (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop := by
  rw [actual_uniform_convergence_definition]
  intro ε hε
  have he : ∀ x, ∀ᶠ n in atTop, |F n x-f x|<ε := by
    intro x
    exact ((Metric.tendsto_nhds.mp (h x) ε hε)).mono fun n hn => by
      simpa only [Real.dist_eq] using hn
  exact eventually_atTop.mp (eventually_all.mpr he)

def sourcePowerFunctions (n : ℕ) (x : Ico (0:ℝ) 1) : ℝ := x.val^n

theorem actual_source_power_functions_converge_pointwise_to_zero :
    ∀ x : Ico (0:ℝ) 1, Tendsto (fun n => sourcePowerFunctions n x) atTop (𝓝 0) := by
  intro x
  exact tendsto_pow_atTop_nhds_zero_of_lt_one x.property.1 x.property.2

theorem actual_each_positive_index_has_a_point_with_power_three_quarters
    (n : ℕ) (hn : n≠0) :
    ∃ x : Ico (0:ℝ) 1, sourcePowerFunctions n x=3/4 := by
  have hp : 0<((n:ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  let x : Ico (0:ℝ) 1 := ⟨(3/4:ℝ)^((n:ℝ)⁻¹),
    Real.rpow_nonneg (by norm_num) _,Real.rpow_lt_one (by norm_num) (by norm_num) hp⟩
  refine ⟨x,?_⟩
  exact Real.rpow_inv_natCast_pow (by norm_num : (0:ℝ)≤3/4) hn

theorem actual_source_power_functions_do_not_converge_uniformly_to_zero :
    ¬ TendstoUniformly sourcePowerFunctions (fun _ => 0) atTop := by
  intro h
  obtain ⟨T,hT⟩ := (actual_uniform_convergence_definition _ _).mp h (1/2) (by norm_num)
  let n := max 1 T
  have hn : n≠0 := by dsimp [n];omega
  obtain ⟨x,hx⟩ := actual_each_positive_index_has_a_point_with_power_three_quarters n hn
  have he := hT n (by dsimp [n];omega) x
  rw [hx] at he
  norm_num at he

theorem actual_source_power_functions_supremum_errors_do_not_tend_to_zero :
    ¬ Tendsto (actualSupError sourcePowerFunctions (fun _ => 0)) atTop (𝓝 0) := by
  exact fun h => actual_source_power_functions_do_not_converge_uniformly_to_zero
    ((actual_uniform_convergence_iff_the_actual_supremum_error_tends_to_zero _ _).mpr h)

end SafeLearning.CompleteFoundationsUniformConvergenceModels
