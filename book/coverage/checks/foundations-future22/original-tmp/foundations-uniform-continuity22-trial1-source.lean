import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsUniformContinuity22

variable {E : Type*} [NormedAddCommGroup E]

theorem actual_uniform_continuity_is_the_literal_epsilon_delta_definition
    (function : E → ℝ) (domain : Set E) :
    UniformContinuousOn function domain ↔
      ∀ epsilon : ℝ,0<epsilon → ∃ delta : ℝ,0<delta ∧
        ∀ first ∈ domain,∀ second ∈ domain,‖first-second‖<delta →
          |function first-function second|<epsilon := by
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    (Metric.uniformContinuousOn_iff (f:=function) (s:=domain))

theorem actual_continuous_function_on_a_compact_domain_is_uniformly_continuous
    (function : E → ℝ) (domain : Set E) (hcompact : IsCompact domain)
    (hcontinuous : ContinuousOn function domain) : UniformContinuousOn function domain :=
  hcompact.uniformContinuousOn_of_continuous hcontinuous

theorem actual_positive_lipschitz_constant_gives_the_literal_epsilon_over_constant_delta
    (function : E → ℝ) (domain : Set E) (constant epsilon : ℝ)
    (hconstant : 0<constant) (hepsilon : 0<epsilon)
    (hlipschitz : ∀ first ∈ domain,∀ second ∈ domain,
      |function first-function second|≤constant*‖first-second‖) :
    0<epsilon/constant ∧ ∀ first ∈ domain,∀ second ∈ domain,
      ‖first-second‖<epsilon/constant → |function first-function second|<epsilon := by
  refine ⟨div_pos hepsilon hconstant,?_⟩
  intro first hfirst second hsecond hnear
  have hstrict := mul_lt_mul_of_pos_left hnear hconstant
  have hcancel : constant*(epsilon/constant)=epsilon := by field_simp
  rw [hcancel] at hstrict
  exact lt_of_le_of_lt (hlipschitz first hfirst second hsecond) hstrict

theorem actual_zero_lipschitz_constant_makes_the_function_constant_on_its_domain
    (function : E → ℝ) (domain : Set E)
    (hlipschitz : ∀ first ∈ domain,∀ second ∈ domain,
      |function first-function second|≤0*‖first-second‖) :
    ∀ first ∈ domain,∀ second ∈ domain,function first=function second := by
  intro first hfirst second hsecond
  have h := hlipschitz first hfirst second hsecond
  have hz : |function first-function second|=0 := by
    apply le_antisymm
    · simpa using h
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

theorem actual_zero_lipschitz_constant_allows_every_positive_delta
    (function : E → ℝ) (domain : Set E)
    (hlipschitz : ∀ first ∈ domain,∀ second ∈ domain,
      |function first-function second|≤0*‖first-second‖)
    (epsilon delta : ℝ) (hepsilon : 0<epsilon) (hdelta : 0<delta) :
    ∀ first ∈ domain,∀ second ∈ domain,‖first-second‖<delta →
      |function first-function second|<epsilon := by
  intro first hfirst second hsecond _
  rw [actual_zero_lipschitz_constant_makes_the_function_constant_on_its_domain
    function domain hlipschitz first hfirst second hsecond,sub_self,abs_zero]
  exact hepsilon

theorem actual_reciprocal_is_continuous_on_the_literal_half_open_interval :
    ContinuousOn (fun point : ℝ => 1/point) (Ioc (0:ℝ) 1) := by
  apply continuousOn_const.div continuousOn_id
  intro point hp
  exact ne_of_gt hp.1

theorem actual_reciprocal_is_not_uniformly_continuous_on_the_literal_half_open_interval :
    ¬UniformContinuousOn (fun point : ℝ => 1/point) (Ioc (0:ℝ) 1) := by
  intro huniform
  obtain ⟨delta,hdelta,hclose⟩ := (Metric.uniformContinuousOn_iff.mp huniform) 1 (by norm_num)
  let small : ℝ := min (delta/2) (1/2)
  have hsmall : 0<small := lt_min (by positivity) (by norm_num)
  have hsdelta : small≤delta/2 := min_le_left _ _
  have hshalf : small≤1/2 := min_le_right _ _
  have hfirst : small ∈ Ioc (0:ℝ) 1 := ⟨hsmall,by linarith⟩
  have hsecond : small/2 ∈ Ioc (0:ℝ) 1 := ⟨by positivity,by linarith⟩
  have hnear : dist small (small/2)<delta := by
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤small-small/2)]
    linarith
  have hgap := hclose small hfirst (small/2) hsecond hnear
  have hreciprocal : 1/small-1/(small/2)=-(1/small) := by field_simp;ring
  rw [Real.dist_eq,hreciprocal,abs_neg,abs_of_pos (by positivity : (0:ℝ)<1/small)] at hgap
  have htwice : (2:ℝ)≤1/small := (le_div_iff₀ hsmall).mpr (by linarith)
  linarith

theorem actual_square_is_continuous_on_the_entire_real_line :
    Continuous (fun point : ℝ => point^2) := continuous_id.pow 2

theorem actual_square_is_not_uniformly_continuous_on_the_entire_real_line :
    ¬UniformContinuous (fun point : ℝ => point^2) := by
  intro huniform
  obtain ⟨delta,hdelta,hclose⟩ := (Metric.uniformContinuous_iff.mp huniform) 1 (by norm_num)
  let first : ℝ := 1/delta
  let second : ℝ := first+delta/2
  have hnear : dist first second<delta := by
    rw [Real.dist_eq,abs_of_nonpos (by dsimp [second];linarith : first-second≤0)]
    dsimp [second]
    linarith
  have hgap := hclose hnear
  have hidentity : first^2-second^2=-(1+delta^2/4) := by
    dsimp [first,second]
    field_simp
    ring
  rw [Real.dist_eq,hidentity,abs_neg,abs_of_pos (by nlinarith [sq_nonneg delta] :
    (0:ℝ)<1+delta^2/4)] at hgap
  nlinarith [sq_nonneg delta]

end SafeLearning.CompleteFoundationsUniformContinuity22
