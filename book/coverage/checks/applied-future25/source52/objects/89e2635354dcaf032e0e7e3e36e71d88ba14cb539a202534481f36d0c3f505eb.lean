import SafeLearning.CompleteModulesChords
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesScalarActivation
open CompleteModulesLipSDP

def actualQuotientSlopeRestricted (activation : ℝ → ℝ) : Prop :=
  ∀ first second,first≠second →
    0≤(activation first-activation second)/(first-second) ∧
      (activation first-activation second)/(first-second)≤1

theorem actual_source_quotient_slope_iff_actual_chord (activation : ℝ → ℝ) :
    actualQuotientSlopeRestricted activation ↔ slopeRestricted activation 0 1 := by
  constructor
  · intro h first second
    by_cases he : first=second
    · subst second
      exact ⟨0,by norm_num,by norm_num,by ring⟩
    · have hb := h first second he
      exact ⟨(activation first-activation second)/(first-second),hb.1,hb.2,
        by field_simp [sub_ne_zero.mpr he]⟩
  · intro h first second he
    obtain ⟨slope,hl,hu,hs⟩ := h first second
    rw [hs,mul_div_cancel_right₀ slope (sub_ne_zero.mpr he)]
    exact ⟨hl,hu⟩

theorem actual_scalar_slope_bound_implies_absolute_increment_bound
    (activation : ℝ → ℝ) (hactivation : actualQuotientSlopeRestricted activation)
    (first second : ℝ) : |activation first-activation second|≤|first-second| := by
  obtain ⟨slope,hl,hu,hs⟩ :=
    (actual_source_quotient_slope_iff_actual_chord activation).mp hactivation first second
  rw [hs,abs_mul,abs_of_nonneg hl]
  nlinarith [abs_nonneg (first-second)]

def actualSourceScalarLayer (activation : ℝ → ℝ) (input : ℝ) : ℝ :=
  3*activation (2*input+1)-4

theorem actual_source_scalar_layer_cancels_bias (activation : ℝ → ℝ) (first second : ℝ) :
    actualSourceScalarLayer activation first-actualSourceScalarLayer activation second=
      3*(activation (2*first+1)-activation (2*second+1)) := by
  unfold actualSourceScalarLayer
  ring

theorem actual_source_scalar_layer_is_six_lipschitz
    (activation : ℝ → ℝ) (hactivation : actualQuotientSlopeRestricted activation)
    (first second : ℝ) :
    |actualSourceScalarLayer activation first-actualSourceScalarLayer activation second|≤6*|first-second| := by
  rw [actual_source_scalar_layer_cancels_bias,abs_mul]
  have hs := actual_scalar_slope_bound_implies_absolute_increment_bound activation hactivation
    (2*first+1) (2*second+1)
  have he : 2*first+1-(2*second+1)=2*(first-second) := by ring
  rw [he,abs_mul] at hs
  norm_num at hs ⊢
  linarith

theorem actual_source_scalar_layer_squared_gain_is_thirty_six
    (activation : ℝ → ℝ) (hactivation : actualQuotientSlopeRestricted activation)
    (first second : ℝ) :
    |actualSourceScalarLayer activation first-actualSourceScalarLayer activation second|^2≤36*|first-second|^2 := by
  have hs := actual_source_scalar_layer_is_six_lipschitz activation hactivation first second
  nlinarith [abs_nonneg (actualSourceScalarLayer activation first-actualSourceScalarLayer activation second),
    abs_nonneg (first-second)]

def actualReLU (input : ℝ) : ℝ := max 0 input

theorem actual_relu_has_the_source_quotient_slope_bound :
    actualQuotientSlopeRestricted actualReLU := by
  apply (actual_source_quotient_slope_iff_actual_chord actualReLU).mpr
  have he : actualReLU=(fun value : ℝ => max value 0) := by
    funext value
    exact max_comm 0 value
  rw [he]
  exact relu_slope_restricted

theorem actual_relu_source_active_pairs_attain_six
    (first second : ℝ) (hfirst : -(1/2:ℝ)<first) (hsecond : -(1/2:ℝ)<second) :
    actualSourceScalarLayer actualReLU first-actualSourceScalarLayer actualReLU second=6*(first-second) := by
  have hf : 0≤2*first+1 := by linarith
  have hs : 0≤2*second+1 := by linarith
  simp [actualSourceScalarLayer,actualReLU,max_eq_right hf,max_eq_right hs]
  ring

theorem actual_relu_source_scalar_layer_has_no_smaller_global_gain
    (gain : ℝ) (hgain : ∀ first second,
      |actualSourceScalarLayer actualReLU first-actualSourceScalarLayer actualReLU second|≤gain*|first-second|) :
    6≤gain := by
  have h := hgain 1 0
  norm_num [actualSourceScalarLayer,actualReLU] at h
  exact h

def actualSourceSectorMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0,1/2;1/2,-1]

theorem actual_source_sector_matrix_quadratic_identity (input hidden : ℝ) :
    quadratic actualSourceSectorMatrix ![input,hidden]=hidden*(input-hidden) := by
  norm_num [quadratic,actualSourceSectorMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_relu_source_sector_case_split (input : ℝ) :
    (0 ≤ input → actualReLU input=input ∧ actualReLU input*(input-actualReLU input)=0) ∧
    (input<0 → actualReLU input=0 ∧ actualReLU input*(input-actualReLU input)=0) := by
  constructor
  · intro h;simp [actualReLU,max_eq_right h]
  · intro h;simp [actualReLU,max_eq_left (le_of_lt h)]

theorem actual_relu_source_sector_quadratic_is_nonnegative (input : ℝ) :
    0 ≤ quadratic actualSourceSectorMatrix ![input,actualReLU input] := by
  rw [actual_source_sector_matrix_quadratic_identity]
  by_cases h : 0 ≤ input
  · rw [(actual_relu_source_sector_case_split input).1 h |>.2]
  · rw [(actual_relu_source_sector_case_split input).2 (lt_of_not_ge h) |>.2]

theorem actual_source_sector_admits_a_pair_outside_relu_graph :
    quadratic actualSourceSectorMatrix ![2,1]=1 ∧ actualReLU 2≠1 := by
  rw [actual_source_sector_matrix_quadratic_identity]
  norm_num [actualReLU]

end SafeLearning.CompleteModulesScalarActivation
