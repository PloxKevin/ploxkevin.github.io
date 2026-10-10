import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedClassKModels
open Set Filter
open scoped Topology

/-- The literal class-K definition on the source nonnegative domain. -/
def classK (function : ℝ → ℝ) : Prop :=
  ContinuousOn function (Ici 0) ∧ StrictMonoOn function (Ici 0) ∧ function 0=0

/-- The class-K-infinity growth requirement, in addition to class K. -/
def classKInfinity (function : ℝ → ℝ) : Prop :=
  classK function ∧ Tendsto function atTop atTop

def linearGain (r : ℝ) : ℝ := 2*r
def squaredGain (r : ℝ) : ℝ := r^2
def boundedGain (r : ℝ) : ℝ := r/(1+r)

theorem actual_twice_argument_is_class_k : classK linearGain := by
  refine ⟨?_,?_,?_⟩
  · unfold linearGain
    fun_prop
  · intro r hr s hs h
    unfold linearGain
    linarith
  · norm_num [linearGain]

theorem actual_square_is_class_k_even_with_zero_derivative :
    classK squaredGain ∧ HasDerivAt squaredGain 0 0 := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · unfold squaredGain
      fun_prop
    · intro r hr s hs h
      have hp : 0<(s-r)*(s+r) := mul_pos (sub_pos.mpr h) (by
        have hr0 : 0 ≤ r := hr
        linarith)
      unfold squaredGain
      nlinarith
    · norm_num [squaredGain]
  · change HasDerivAt (fun r : ℝ => r^2) 0 0
    convert (hasDerivAt_id (0:ℝ)).pow 2 using 1
    · funext r
      rfl
    · norm_num

theorem actual_bounded_fraction_is_class_k : classK boundedGain := by
  refine ⟨?_,?_,?_⟩
  · exact continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => ne_of_gt (by have hr0 : 0 ≤ r := hr;linarith))
  · intro r hr s hs h
    have hr0 : 0 ≤ r := hr
    have hs0 : 0 ≤ s := hs
    change r/(1+r)<s/(1+s)
    apply (div_lt_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  · norm_num [boundedGain]

theorem actual_linear_and_square_are_unbounded :
    Tendsto linearGain atTop atTop ∧ Tendsto squaredGain atTop atTop := by
  constructor
  · exact tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)
  · exact tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)

theorem actual_nonnegative_fraction_is_bounded_strictly_below_one
    (r : ℝ) (hr : 0 ≤ r) : 0 ≤ boundedGain r ∧ boundedGain r < 1 := by
  have hd : 0<1+r := by linarith
  exact ⟨div_nonneg hr hd.le,(div_lt_one hd).mpr (by linarith)⟩

theorem actual_bounded_fraction_approaches_one : Tendsto boundedGain atTop (𝓝 1) := by
  have hi := tendsto_mul_add_inv_atTop_nhds_zero (1:ℝ) 1 (by norm_num)
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hi
  have he : boundedGain =ᶠ[atTop] (fun r : ℝ => 1-(1*r+1)⁻¹) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    have hd : 1+r ≠ 0 := ne_of_gt (by linarith)
    unfold boundedGain
    field_simp
    ring
  simpa using hh.congr' he.symm

theorem actual_bounded_fraction_is_not_unbounded : ¬Tendsto boundedGain atTop atTop := by
  intro h
  obtain ⟨r,hr,hlarge⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (h.eventually (eventually_ge_atTop (2:ℝ)))).exists
  have hb := actual_nonnegative_fraction_is_bounded_strictly_below_one r hr
  linarith [hb.2]

theorem actual_source_three_classifications :
    classKInfinity linearGain ∧ classKInfinity squaredGain ∧
      classK boundedGain ∧ ¬classKInfinity boundedGain := by
  exact ⟨⟨actual_twice_argument_is_class_k,actual_linear_and_square_are_unbounded.1⟩,
    ⟨actual_square_is_class_k_even_with_zero_derivative.1,
      actual_linear_and_square_are_unbounded.2⟩,
    actual_bounded_fraction_is_class_k,
    fun h => actual_bounded_fraction_is_not_unbounded h.2⟩

end SafeLearning.CompleteAppliedClassKModels
