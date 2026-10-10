import SafeLearning.CompleteModulesDynamicLayer

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDynamicLayerSoundness
open CompleteModulesLipSDP CompleteModulesDynamicLayer
variable {S I O : Type*} [Fintype S] [Fintype I] [Fintype O] [DecidableEq O]

def actualLayerNextState (A : Matrix S S ℝ) (B : Matrix S I ℝ)
    (state : S → ℝ) (input : I → ℝ) : S → ℝ := A *ᵥ state+B *ᵥ input

def actualLayerPreactivation (C : Matrix O S ℝ) (D : Matrix O I ℝ) (bias : O → ℝ)
    (state : S → ℝ) (input : I → ℝ) : O → ℝ := C *ᵥ state+D *ᵥ input+bias

def actualLayerHidden (C : Matrix O S ℝ) (D : Matrix O I ℝ) (bias : O → ℝ)
    (activation : ℝ → ℝ) (state : S → ℝ) (input : I → ℝ) : O → ℝ :=
  fun coordinate => activation (actualLayerPreactivation C D bias state input coordinate)

theorem actual_dynamic_preactivation_difference_cancels_bias
    (C : Matrix O S ℝ) (D : Matrix O I ℝ) (bias : O → ℝ)
    (firstState secondState : S → ℝ) (firstInput secondInput : I → ℝ) :
    actualLayerPreactivation C D bias firstState firstInput-
      actualLayerPreactivation C D bias secondState secondInput=
      C *ᵥ (firstState-secondState)+D *ᵥ (firstInput-secondInput) := by
  ext coordinate
  simp only [actualLayerPreactivation,Matrix.mulVec_sub,Pi.sub_apply,Pi.add_apply]
  ring

theorem actual_dynamic_layer_activation_increment_satisfies_qc
    (C : Matrix O S ℝ) (D : Matrix O I ℝ) (bias : O → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1) (multiplier : O → ℝ)
    (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (firstState secondState : S → ℝ) (firstInput secondInput : I → ℝ) :
    0 ≤ ∑ coordinate,multiplier coordinate*
      (2*((C *ᵥ (firstState-secondState)+D *ᵥ (firstInput-secondInput)) coordinate)*
        ((actualLayerHidden C D bias activation firstState firstInput-
          actualLayerHidden C D bias activation secondState secondInput) coordinate)-
        2*((actualLayerHidden C D bias activation firstState firstInput-
          actualLayerHidden C D bias activation secondState secondInput) coordinate)^2) := by
  apply Finset.sum_nonneg
  intro coordinate hcoordinate
  have h := scalar_slope_quadratic_constraint activation 0 1 hactivation
    (actualLayerPreactivation C D bias firstState firstInput coordinate)
    (actualLayerPreactivation C D bias secondState secondInput coordinate)
  norm_num at h
  have he := congrFun (actual_dynamic_preactivation_difference_cancels_bias C D bias
    firstState secondState firstInput secondInput) coordinate
  simp only [Pi.sub_apply] at he
  rw [he] at h
  exact mul_nonneg (hweight coordinate) (by
    simp only [actualLayerHidden,Pi.sub_apply]
    linarith)

theorem actual_dynamic_layer_lmi_implies_storage_dissipation
    (A : Matrix S S ℝ) (B : Matrix S I ℝ) (C : Matrix O S ℝ) (D : Matrix O I ℝ)
    (P : Matrix S S ℝ) (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ)
    (bias : O → ℝ) (activation : ℝ → ℝ) (hactivation : slopeRestricted activation 0 1)
    (multiplier : O → ℝ) (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (actualLayerCertificate A B C D P Xin Xout multiplier).PosSemidef)
    (firstState secondState : S → ℝ) (firstInput secondInput : I → ℝ) :
    quadratic P (actualLayerNextState A B firstState firstInput-
      actualLayerNextState A B secondState secondInput)-quadratic P (firstState-secondState) ≤
      quadratic Xin (firstInput-secondInput)-quadratic Xout
        (actualLayerHidden C D bias activation firstState firstInput-
          actualLayerHidden C D bias activation secondState secondInput) := by
  have hc : 0 ≤ quadratic (actualLayerCertificate A B C D P Xin Xout multiplier)
      (Sum.elim (Sum.elim (firstState-secondState) (firstInput-secondInput))
        (actualLayerHidden C D bias activation firstState firstInput-
          actualLayerHidden C D bias activation secondState secondInput)) := by
    simpa only [quadratic,star_trivial] using hcertificate.dotProduct_mulVec_nonneg
      (Sum.elim (Sum.elim (firstState-secondState) (firstInput-secondInput))
        (actualLayerHidden C D bias activation firstState firstInput-
          actualLayerHidden C D bias activation secondState secondInput))
  rw [actual_layer_certificate_quadratic_identity] at hc
  have hqc := actual_dynamic_layer_activation_increment_satisfies_qc C D bias activation hactivation
    multiplier hweight firstState secondState firstInput secondInput
  have hnext : actualLayerNextState A B firstState firstInput-
      actualLayerNextState A B secondState secondInput=
      A *ᵥ (firstState-secondState)+B *ᵥ (firstInput-secondInput) := by
    ext coordinate
    simp only [actualLayerNextState,Matrix.mulVec_sub,Pi.sub_apply,Pi.add_apply]
    ring
  rw [hnext]
  linarith

theorem actual_weighted_storage_dissipation_telescopes
    (storage inputEnergy outputEnergy : ℕ → ℝ)
    (hdissipation : ∀ time,storage (time+1)-storage time ≤ inputEnergy time-outputEnergy time)
    (horizon : ℕ) : storage horizon+∑ time ∈ Finset.range horizon,outputEnergy time ≤
      storage 0+∑ time ∈ Finset.range horizon,inputEnergy time := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have h := hdissipation horizon
    linarith

end SafeLearning.CompleteModulesDynamicLayerSoundness
