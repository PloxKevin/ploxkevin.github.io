import SafeLearning.CompleteModulesDynamicLayerSoundness

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDynamicLayerTrajectory
open CompleteModulesLipSDP CompleteModulesDynamicLayer CompleteModulesDynamicLayerSoundness
variable {S I O : Type*} [Fintype S] [Fintype I] [Fintype O] [DecidableEq S] [DecidableEq I] [DecidableEq O]

theorem actual_layer_lmi_bounds_every_finite_trajectory_weighted_energy
    (A : Matrix S S ℝ) (B : Matrix S I ℝ) (C : Matrix O S ℝ) (D : Matrix O I ℝ)
    (P : Matrix S S ℝ) (hP : P.PosSemidef)
    (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ)
    (bias : O → ℝ) (activation : ℝ → ℝ) (hactivation : slopeRestricted activation 0 1)
    (multiplier : O → ℝ) (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (actualLayerCertificate A B C D P Xin Xout multiplier).PosSemidef)
    (firstState secondState : ℕ → S → ℝ) (firstInput secondInput : ℕ → I → ℝ)
    (hfirst : ∀ time,firstState (time+1)=actualLayerNextState A B (firstState time) (firstInput time))
    (hsecond : ∀ time,secondState (time+1)=actualLayerNextState A B (secondState time) (secondInput time))
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon,quadratic Xout
      (actualLayerHidden C D bias activation (firstState time) (firstInput time)-
        actualLayerHidden C D bias activation (secondState time) (secondInput time)) ≤
      (∑ time ∈ Finset.range horizon,quadratic Xin (firstInput time-secondInput time))+
        quadratic P (firstState 0-secondState 0) := by
  have h := actual_weighted_storage_dissipation_telescopes
    (fun time => quadratic P (firstState time-secondState time))
    (fun time => quadratic Xin (firstInput time-secondInput time))
    (fun time => quadratic Xout
      (actualLayerHidden C D bias activation (firstState time) (firstInput time)-
        actualLayerHidden C D bias activation (secondState time) (secondInput time)))
    (by
      intro time
      rw [hfirst time,hsecond time]
      exact actual_dynamic_layer_lmi_implies_storage_dissipation A B C D P Xin Xout bias activation
        hactivation multiplier hweight hcertificate (firstState time) (secondState time)
          (firstInput time) (secondInput time)) horizon
  have hp : 0 ≤ quadratic P (firstState horizon-secondState horizon) := by
    simpa only [quadratic,star_trivial] using hP.dotProduct_mulVec_nonneg
      (firstState horizon-secondState horizon)
  linarith

theorem actual_layer_lmi_bounds_zero_initial_trajectory_weighted_energy
    (A : Matrix S S ℝ) (B : Matrix S I ℝ) (C : Matrix O S ℝ) (D : Matrix O I ℝ)
    (P : Matrix S S ℝ) (hP : P.PosSemidef)
    (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ)
    (bias : O → ℝ) (activation : ℝ → ℝ) (hactivation : slopeRestricted activation 0 1)
    (multiplier : O → ℝ) (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (actualLayerCertificate A B C D P Xin Xout multiplier).PosSemidef)
    (firstState secondState : ℕ → S → ℝ) (firstInput secondInput : ℕ → I → ℝ)
    (hfirst : ∀ time,firstState (time+1)=actualLayerNextState A B (firstState time) (firstInput time))
    (hsecond : ∀ time,secondState (time+1)=actualLayerNextState A B (secondState time) (secondInput time))
    (hinitial : firstState 0=secondState 0) (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon,quadratic Xout
      (actualLayerHidden C D bias activation (firstState time) (firstInput time)-
        actualLayerHidden C D bias activation (secondState time) (secondInput time)) ≤
      ∑ time ∈ Finset.range horizon,quadratic Xin (firstInput time-secondInput time) := by
  have h := actual_layer_lmi_bounds_every_finite_trajectory_weighted_energy A B C D P hP Xin Xout
    bias activation hactivation multiplier hweight hcertificate firstState secondState firstInput secondInput
      hfirst hsecond horizon
  simpa [hinitial,quadratic] using h

theorem actual_identity_quadratic_is_coordinate_energy {J : Type*} [Fintype J] [DecidableEq J]
    (vector : J → ℝ) : quadratic (1 : Matrix J J ℝ) vector=∑ coordinate,(vector coordinate)^2 := by
  simp [quadratic,dotProduct,pow_two]

theorem actual_euclidean_layer_lmi_bounds_every_zero_initial_trajectory_energy
    (A : Matrix S S ℝ) (B : Matrix S I ℝ) (C : Matrix O S ℝ) (D : Matrix O I ℝ)
    (P : Matrix S S ℝ) (hP : P.PosSemidef) (gain : ℝ)
    (bias : O → ℝ) (activation : ℝ → ℝ) (hactivation : slopeRestricted activation 0 1)
    (multiplier : O → ℝ) (hweight : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (actualLayerCertificate A B C D P ((gain^2) • (1 : Matrix I I ℝ))
      (1 : Matrix O O ℝ) multiplier).PosSemidef)
    (firstState secondState : ℕ → S → ℝ) (firstInput secondInput : ℕ → I → ℝ)
    (hfirst : ∀ time,firstState (time+1)=actualLayerNextState A B (firstState time) (firstInput time))
    (hsecond : ∀ time,secondState (time+1)=actualLayerNextState A B (secondState time) (secondInput time))
    (hinitial : firstState 0=secondState 0) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,∑ coordinate,
      (actualLayerHidden C D bias activation (firstState time) (firstInput time) coordinate-
        actualLayerHidden C D bias activation (secondState time) (secondInput time) coordinate)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,∑ coordinate,
        (firstInput time coordinate-secondInput time coordinate)^2) := by
  have h := actual_layer_lmi_bounds_zero_initial_trajectory_weighted_energy A B C D P hP
    ((gain^2) • (1 : Matrix I I ℝ)) (1 : Matrix O O ℝ) bias activation hactivation multiplier hweight
    hcertificate firstState secondState firstInput secondInput hfirst hsecond hinitial horizon
  simpa only [quadratic_smul,actual_identity_quadratic_is_coordinate_energy,Pi.sub_apply,← Finset.mul_sum] using h

theorem actual_dynamic_layer_certificate_dimension_is_state_plus_input_plus_output :
    Fintype.card ((S ⊕ I) ⊕ O)=Fintype.card S+Fintype.card I+Fintype.card O := by
  simp only [Fintype.card_sum]

theorem actual_three_tap_dynamic_certificate_has_signal_length_independent_dimension :
    Fintype.card (((I ⊕ I) ⊕ I) ⊕ O)=3*Fintype.card I+Fintype.card O := by
  simp only [Fintype.card_sum]
  omega

end SafeLearning.CompleteModulesDynamicLayerTrajectory
