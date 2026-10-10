import SafeLearning.CompleteModulesDynamicLayerTrajectory

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDynamicCascade
open CompleteModulesLipSDP CompleteModulesDynamicLayer CompleteModulesDynamicLayerSoundness
  CompleteModulesDynamicLayerTrajectory

structure actualFiniteDynamicLayer (stateDimension inputDimension outputDimension : ℕ) where
  A : Matrix (Fin stateDimension) (Fin stateDimension) ℝ
  B : Matrix (Fin stateDimension) (Fin inputDimension) ℝ
  C : Matrix (Fin outputDimension) (Fin stateDimension) ℝ
  D : Matrix (Fin outputDimension) (Fin inputDimension) ℝ
  P : Matrix (Fin stateDimension) (Fin stateDimension) ℝ
  bias : Fin outputDimension → ℝ
  activation : ℝ → ℝ
  multiplier : Fin outputDimension → ℝ

theorem actual_connected_dynamic_cascade_has_every_finite_weighted_energy_bound
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
    (depth horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,quadratic (weight depth) (firstInput depth time-secondInput depth time)) ≤
      ∑ time ∈ Finset.range horizon,quadratic (weight 0) (firstInput 0 time-secondInput 0 time) := by
  induction depth with
  | zero => exact le_rfl
  | succ depth ih =>
    have h := actual_layer_lmi_bounds_zero_initial_trajectory_weighted_energy
      (layer depth).A (layer depth).B (layer depth).C (layer depth).D (layer depth).P
      (hstorage depth) (weight depth) (weight (depth+1)) (layer depth).bias (layer depth).activation
      (hactivation depth) (layer depth).multiplier (hmultiplier depth) (hcertificate depth)
      (firstState depth) (secondState depth) (firstInput depth) (secondInput depth)
      (hfirstState depth) (hsecondState depth) (hinitial depth) horizon
    have he : (∑ time ∈ Finset.range horizon,
        quadratic (weight (depth+1)) (firstInput (depth+1) time-secondInput (depth+1) time)) ≤
        ∑ time ∈ Finset.range horizon,quadratic (weight depth) (firstInput depth time-secondInput depth time) := by
      simpa only [hfirstConnection depth,hsecondConnection depth] using h
    exact he.trans ih

theorem actual_linear_output_gram_dominance_bounds_weighted_energy
    {I O : Type*} [Fintype I] [Fintype O]
    (W : Matrix O I ℝ) (bias : O → ℝ) (weight : Matrix I I ℝ)
    (hweight : (weight-Wᵀ*W).PosSemidef) (first second : ℕ → I → ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,∑ coordinate,
      ((W *ᵥ first time+bias) coordinate-(W *ᵥ second time+bias) coordinate)^2) ≤
      ∑ time ∈ Finset.range horizon,quadratic weight (first time-second time) := by
  apply Finset.sum_le_sum
  intro time htime
  have h : 0 ≤ quadratic (weight-Wᵀ*W) (first time-second time) := by
    simpa only [quadratic,star_trivial] using hweight.dotProduct_mulVec_nonneg (first time-second time)
  rw [quadratic_sub,quadratic_gram] at h
  have he : (fun coordinate => ((W *ᵥ first time+bias) coordinate-(W *ᵥ second time+bias) coordinate)^2)=
      fun coordinate => ((W *ᵥ (first time-second time)) coordinate)^2 := by
    ext coordinate
    simp only [Matrix.mulVec_sub,Pi.sub_apply,Pi.add_apply,add_sub_add_right_eq_sub]
  rw [he]
  linarith

theorem actual_dynamic_cascade_euclidean_output_bound_from_source_endpoint_weights
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (W : Matrix O I ℝ) (bias : O → ℝ) (weight : Matrix I I ℝ)
    (hweight : (weight-Wᵀ*W).PosSemidef) (first second : ℕ → I → ℝ)
    {J : Type*} [Fintype J] [DecidableEq J] (sourceFirst sourceSecond : ℕ → J → ℝ)
    (gain : ℝ) (horizon : ℕ)
    (hcascade : (∑ time ∈ Finset.range horizon,quadratic weight (first time-second time)) ≤
      ∑ time ∈ Finset.range horizon,quadratic ((gain^2) • (1 : Matrix J J ℝ))
        (sourceFirst time-sourceSecond time)) :
    (∑ time ∈ Finset.range horizon,∑ coordinate,
      ((W *ᵥ first time+bias) coordinate-(W *ᵥ second time+bias) coordinate)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,∑ coordinate,
        (sourceFirst time coordinate-sourceSecond time coordinate)^2) := by
  have h := (actual_linear_output_gram_dominance_bounds_weighted_energy W bias weight hweight first second horizon).trans hcascade
  simpa only [quadratic_smul,actual_identity_quadratic_is_coordinate_energy,Pi.sub_apply,← Finset.mul_sum] using h

end SafeLearning.CompleteModulesDynamicCascade
