import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLoSBOExceedanceGeometry

def actualCone {X : Type*} [PseudoMetricSpace X]
    (L E threshold reading : ℝ) (anchor candidate : X) : Prop :=
  threshold ≤ reading-E-L*dist anchor candidate

theorem actual_one_sided_noise_is_exactly_the_anchor_lower_bound
    (value noise E : ℝ) : value ≥ (value+noise)-E ↔ noise ≤ E := by
  constructor <;> intro h <;> linarith

theorem actual_unsafe_certified_point_requires_the_literal_excess_shell_and_margin
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (anchor candidate : X)
    (L E threshold noise : ℝ) (hL : 0 < L)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hc : actualCone L E threshold (f anchor+noise) anchor candidate)
    (hu : f candidate < threshold) :
    E < noise ∧
      (f anchor-threshold)/L < dist anchor candidate ∧
      dist anchor candidate ≤ (f anchor-threshold)/L+(noise-E)/L ∧
      threshold-(noise-E) ≤ f candidate := by
  have hr := (abs_le.mp (hf anchor candidate)).2
  change threshold ≤ (f anchor+noise)-E-L*dist anchor candidate at hc
  have hlow : f anchor-threshold < L*dist anchor candidate := by linarith
  have hupp : L*dist anchor candidate ≤ f anchor-threshold+(noise-E) := by linarith
  refine ⟨by linarith, (div_lt_iff₀ hL).mpr (by nlinarith), ?_, by linarith⟩
  rw [←add_div]
  exact (le_div_iff₀ hL).mpr (by nlinarith)

def actualLinearMargin (x : ℝ) : ℝ := 1-x

theorem actual_source_linear_margin_is_globally_one_lipschitz :
    ∀ a x : ℝ, |actualLinearMargin a-actualLinearMargin x| ≤ dist a x := by
  intro a x
  simp only [actualLinearMargin,Real.dist_eq]
  have he : (1-a)-(1-x)=-(a-x) := by ring
  rw [he,abs_neg]

theorem actual_source_positive_noise_at_an_interior_anchor_certifies_an_unsafe_query
    (E : ℝ) :
    actualLinearMargin 0=1 ∧
      actualCone 1 E 0 (actualLinearMargin 0+(E+1/10)) 0 (21/20:ℝ) ∧
      actualLinearMargin (21/20)<0 ∧
      (1:ℝ)<dist 0 (21/20:ℝ) ∧ dist 0 (21/20:ℝ) ≤ 1+1/10 := by
  norm_num [actualLinearMargin,actualCone,Real.dist_eq] <;> linarith

theorem actual_positive_exceedance_on_a_flat_function_is_harmless
    (E : ℝ) :
    (∀ x : ℝ, (0:ℝ) ≤ (fun _ : ℝ => (1:ℝ)) x) ∧
      actualCone 1 E 0 (1+(E+1/10)) (0:ℝ) (21/20) ∧
      E < E+1/10 := by
  norm_num [actualCone,Real.dist_eq] <;> linarith

theorem actual_conservative_lipschitz_excess_shell_can_still_be_safe
    (E : ℝ) :
    (∀ a x : ℝ, |actualLinearMargin a-actualLinearMargin x| ≤ 2*dist a x) ∧
      actualCone 2 E 0 (actualLinearMargin 0+(E+1/10)) 0 (21/40:ℝ) ∧
      (1:ℝ)/2<dist 0 (21/40:ℝ) ∧ 0<actualLinearMargin (21/40) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a x
    have hb := actual_source_linear_margin_is_globally_one_lipschitz a x
    have hd := dist_nonneg (x:=a) (y:=x)
    linarith
  · norm_num [actualCone,actualLinearMargin,Real.dist_eq] <;> linarith
  · norm_num [Real.dist_eq]
  · norm_num [actualLinearMargin]

theorem actual_double_noise_allowance_gives_a_true_buffer_and_no_later_false_alarm
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (anchor candidate : X)
    (L B threshold currentNoise futureNoise : ℝ)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hn : currentNoise ≤ B) (hfuture : -B ≤ futureNoise)
    (hc : actualCone L (2*B) threshold (f anchor+currentNoise) anchor candidate) :
    threshold+B ≤ f candidate ∧ threshold ≤ f candidate+futureNoise := by
  have hr := (abs_le.mp (hf anchor candidate)).2
  change threshold ≤ (f anchor+currentNoise)-2*B-L*dist anchor candidate at hc
  constructor <;> linarith

theorem actual_buffered_seed_also_cannot_raise_a_bounded_noise_false_alarm
    (value B threshold noise : ℝ) (hseed : threshold+B ≤ value) (hn : -B ≤ noise) :
    threshold ≤ value+noise := by linarith

theorem actual_safe_unbuffered_seed_can_raise_a_false_alarm_even_with_double_cone_allowance
    (B : ℝ) (hB : 0 < B) :
    (0:ℝ) ≤ 0 ∧ |(-B:ℝ)| ≤ B ∧ (0:ℝ)+(-B)<0 ∧ (2:ℝ)*B>B := by
  refine ⟨le_rfl,?_,?_,?_⟩
  · rw [abs_neg,abs_of_pos hB]
  · linarith
  · linarith

end SafeLearning.CompleteModulesLoSBOExceedanceGeometry
