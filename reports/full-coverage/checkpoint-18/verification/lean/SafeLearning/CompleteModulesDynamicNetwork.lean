import SafeLearning.CompleteModulesDynamicCascade

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDynamicNetwork
open CompleteModulesLipSDP CompleteModulesDynamicLayer CompleteModulesDynamicLayerSoundness
  CompleteModulesDynamicLayerTrajectory CompleteModulesDynamicCascade

theorem actual_connected_dynamic_network_lmis_imply_euclidean_gain
    (channels states : ℕ → ℕ)
    (layer : ∀ stage,actualFiniteDynamicLayer (states stage) (channels stage) (channels (stage+1)))
    (weight : ∀ stage,Matrix (Fin (channels stage)) (Fin (channels stage)) ℝ)
    (hstorage : ∀ stage,(layer stage).P.PosSemidef)
    (hactivation : ∀ stage,slopeRestricted (layer stage).activation 0 1)
    (hmultiplier : ∀ stage coordinate,0 ≤ (layer stage).multiplier coordinate)
    (hcertificate : ∀ stage,(actualLayerCertificate (layer stage).A (layer stage).B
      (layer stage).C (layer stage).D (layer stage).P (weight stage) (weight (stage+1))
        (layer stage).multiplier).PosSemidef)
    (firstState secondState : ∀ stage,ℕ → Fin (states stage) → ℝ)
    (firstInput secondInput : ∀ stage,ℕ → Fin (channels stage) → ℝ)
    (hfirstState : ∀ stage time,firstState stage (time+1)=
      actualLayerNextState (layer stage).A (layer stage).B (firstState stage time) (firstInput stage time))
    (hsecondState : ∀ stage time,secondState stage (time+1)=
      actualLayerNextState (layer stage).A (layer stage).B (secondState stage time) (secondInput stage time))
    (hinitial : ∀ stage,firstState stage 0=secondState stage 0)
    (hfirstConnection : ∀ stage time,firstInput (stage+1) time=
      actualLayerHidden (layer stage).C (layer stage).D (layer stage).bias (layer stage).activation
        (firstState stage time) (firstInput stage time))
    (hsecondConnection : ∀ stage time,secondInput (stage+1) time=
      actualLayerHidden (layer stage).C (layer stage).D (layer stage).bias (layer stage).activation
        (secondState stage time) (secondInput stage time))
    (depth horizon outputDimension : ℕ)
    (W : Matrix (Fin outputDimension) (Fin (channels depth)) ℝ) (bias : Fin outputDimension → ℝ)
    (gain : ℝ) (hinputWeight : weight 0=(gain^2) • (1 : Matrix (Fin (channels 0)) (Fin (channels 0)) ℝ))
    (houtputWeight : (weight depth-Wᵀ*W).PosSemidef) :
    (∑ time ∈ Finset.range horizon,∑ coordinate,
      ((W *ᵥ firstInput depth time+bias) coordinate-(W *ᵥ secondInput depth time+bias) coordinate)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,∑ coordinate,
        (firstInput 0 time coordinate-secondInput 0 time coordinate)^2) := by
  have hc := actual_connected_dynamic_cascade_has_every_finite_weighted_energy_bound channels states
    layer weight hstorage hactivation hmultiplier hcertificate firstState secondState firstInput secondInput
    hfirstState hsecondState hinitial hfirstConnection hsecondConnection depth horizon
  rw [hinputWeight] at hc
  exact actual_dynamic_cascade_euclidean_output_bound_from_source_endpoint_weights W bias (weight depth)
    houtputWeight (firstInput depth) (secondInput depth) (firstInput 0) (secondInput 0) gain horizon hc

end SafeLearning.CompleteModulesDynamicNetwork
