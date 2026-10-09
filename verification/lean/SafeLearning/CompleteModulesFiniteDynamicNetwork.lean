import SafeLearning.CompleteModulesDynamicNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFiniteDynamicNetwork
open CompleteModulesLipSDP CompleteModulesDynamicLayer CompleteModulesDynamicLayerSoundness
  CompleteModulesDynamicLayerTrajectory CompleteModulesDynamicCascade

theorem actual_finite_dynamic_network_lmis_imply_euclidean_gain
    (depth : ℕ) (channels states : ℕ → ℕ)
    (layer : ∀ stage,actualFiniteDynamicLayer (states stage) (channels stage) (channels (stage+1)))
    (weight : ∀ stage,Matrix (Fin (channels stage)) (Fin (channels stage)) ℝ)
    (hstorage : ∀ stage,stage<depth → (layer stage).P.PosSemidef)
    (hactivation : ∀ stage,stage<depth → slopeRestricted (layer stage).activation 0 1)
    (hmultiplier : ∀ stage,stage<depth → ∀ coordinate,0 ≤ (layer stage).multiplier coordinate)
    (hcertificate : ∀ stage,stage<depth → (actualLayerCertificate (layer stage).A (layer stage).B
      (layer stage).C (layer stage).D (layer stage).P (weight stage) (weight (stage+1))
        (layer stage).multiplier).PosSemidef)
    (firstState secondState : ∀ stage,ℕ → Fin (states stage) → ℝ)
    (firstInput secondInput : ∀ stage,ℕ → Fin (channels stage) → ℝ)
    (hfirstState : ∀ stage,stage<depth → ∀ time,firstState stage (time+1)=
      actualLayerNextState (layer stage).A (layer stage).B (firstState stage time) (firstInput stage time))
    (hsecondState : ∀ stage,stage<depth → ∀ time,secondState stage (time+1)=
      actualLayerNextState (layer stage).A (layer stage).B (secondState stage time) (secondInput stage time))
    (hinitial : ∀ stage,stage<depth → firstState stage 0=secondState stage 0)
    (hfirstConnection : ∀ stage,stage<depth → ∀ time,firstInput (stage+1) time=
      actualLayerHidden (layer stage).C (layer stage).D (layer stage).bias (layer stage).activation
        (firstState stage time) (firstInput stage time))
    (hsecondConnection : ∀ stage,stage<depth → ∀ time,secondInput (stage+1) time=
      actualLayerHidden (layer stage).C (layer stage).D (layer stage).bias (layer stage).activation
        (secondState stage time) (secondInput stage time))
    (horizon outputDimension : ℕ)
    (W : Matrix (Fin outputDimension) (Fin (channels depth)) ℝ) (bias : Fin outputDimension → ℝ)
    (gain : ℝ) (hinputWeight : weight 0=(gain^2) • (1 : Matrix (Fin (channels 0)) (Fin (channels 0)) ℝ))
    (houtputWeight : (weight depth-Wᵀ*W).PosSemidef) :
    (∑ time ∈ Finset.range horizon,∑ coordinate,
      ((W *ᵥ firstInput depth time+bias) coordinate-(W *ᵥ secondInput depth time+bias) coordinate)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,∑ coordinate,
        (firstInput 0 time coordinate-secondInput 0 time coordinate)^2) := by
  have hchain : ∀ stage,stage ≤ depth →
      (∑ time ∈ Finset.range horizon,quadratic (weight stage)
        (firstInput stage time-secondInput stage time)) ≤
      ∑ time ∈ Finset.range horizon,quadratic (weight 0) (firstInput 0 time-secondInput 0 time) := by
    intro stage
    induction stage with
    | zero => intro hzero;exact le_rfl
    | succ stage ih =>
      intro hstage
      have hs : stage<depth := by omega
      have h := actual_layer_lmi_bounds_zero_initial_trajectory_weighted_energy
        (layer stage).A (layer stage).B (layer stage).C (layer stage).D (layer stage).P
        (hstorage stage hs) (weight stage) (weight (stage+1)) (layer stage).bias (layer stage).activation
        (hactivation stage hs) (layer stage).multiplier (hmultiplier stage hs) (hcertificate stage hs)
        (firstState stage) (secondState stage) (firstInput stage) (secondInput stage)
        (hfirstState stage hs) (hsecondState stage hs) (hinitial stage hs) horizon
      have he : (∑ time ∈ Finset.range horizon,
          quadratic (weight (stage+1)) (firstInput (stage+1) time-secondInput (stage+1) time)) ≤
          ∑ time ∈ Finset.range horizon,quadratic (weight stage) (firstInput stage time-secondInput stage time) := by
        simpa only [hfirstConnection stage hs,hsecondConnection stage hs] using h
      exact he.trans (ih (by omega))
  have hc := hchain depth le_rfl
  rw [hinputWeight] at hc
  exact actual_dynamic_cascade_euclidean_output_bound_from_source_endpoint_weights W bias (weight depth)
    houtputWeight (firstInput depth) (secondInput depth) (firstInput 0) (secondInput 0) gain horizon hc

end SafeLearning.CompleteModulesFiniteDynamicNetwork
