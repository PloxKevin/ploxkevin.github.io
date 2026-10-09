import SafeLearning.CompleteModulesLipSDPNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesLipSDPConvex

open CompleteModulesLipSDP CompleteModulesLipSDPNetwork
variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K]

theorem actual_block_certificate_is_affine (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (alpha beta : ℝ)
    (first second : ℝ × (K → ℝ)) (a b : ℝ) (hab : a+b=1) :
    blockCertificate firstWeight lastWeight alpha beta (a*first.1+b*second.1)
      (a • first.2+b • second.2)=
      a • blockCertificate firstWeight lastWeight alpha beta first.1 first.2+
      b • blockCertificate firstWeight lastWeight alpha beta second.1 second.2 := by
  have hd : Matrix.diagonal (a • first.2+b • second.2)=
      a • Matrix.diagonal first.2+b • Matrix.diagonal second.2 := by
    ext i j
    simp only [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.add_apply,Pi.smul_apply,Pi.add_apply]
    split_ifs <;> ring
  unfold blockCertificate
  rw [hd]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
  ext i j
  cases i with
  | inl i =>
    cases j <;> simp [Matrix.fromBlocks,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply] <;> ring
  | inr i =>
    cases j with
    | inl j => simp [Matrix.fromBlocks,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply]; ring
    | inr j =>
      simp [Matrix.fromBlocks,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply]
      linear_combination -((lastWeightᵀ*lastWeight) i j)*hab

def feasibleNeuronParameters (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (alpha beta : ℝ) : Set (ℝ × (K → ℝ)) :=
  {parameter | 0 ≤ parameter.1 ∧ (∀ k, 0 ≤ parameter.2 k) ∧
    (-(blockCertificate firstWeight lastWeight alpha beta parameter.1 parameter.2)).PosSemidef}

theorem actual_neuron_sdp_feasible_set_is_convex (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (alpha beta : ℝ) :
    Convex ℝ (feasibleNeuronParameters firstWeight lastWeight alpha beta) := by
  intro first hf second hs a b ha hb hab
  rcases hf with ⟨hfrho,hfmult,hfm⟩
  rcases hs with ⟨hsrho,hsmult,hsm⟩
  refine ⟨?_,?_,?_⟩
  · exact add_nonneg (mul_nonneg ha hfrho) (mul_nonneg hb hsrho)
  · intro k
    exact add_nonneg (mul_nonneg ha (hfmult k)) (mul_nonneg hb (hsmult k))
  · change (-(blockCertificate firstWeight lastWeight alpha beta
      (a*first.1+b*second.1) (a • first.2+b • second.2))).PosSemidef
    rw [actual_block_certificate_is_affine _ _ _ _ _ _ _ _ hab]
    simpa only [smul_neg,neg_add] using (hfm.smul ha).add (hsm.smul hb)

theorem actual_neuron_sdp_objective_is_convex (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (alpha beta : ℝ) :
    ConvexOn ℝ (feasibleNeuronParameters firstWeight lastWeight alpha beta)
      (fun parameter => parameter.1) := by
  refine ⟨actual_neuron_sdp_feasible_set_is_convex _ _ _ _,?_⟩
  intro first hf second hs a b ha hb hab
  simp

theorem actual_neuron_sdp_has_no_nonglobal_local_minimum (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (alpha beta : ℝ) (parameter : ℝ × (K → ℝ))
    (hfeasible : parameter ∈ feasibleNeuronParameters firstWeight lastWeight alpha beta)
    (hlocal : IsLocalMinOn (fun candidate : ℝ × (K → ℝ) => candidate.1)
      (feasibleNeuronParameters firstWeight lastWeight alpha beta) parameter) :
    IsMinOn (fun candidate : ℝ × (K → ℝ) => candidate.1)
      (feasibleNeuronParameters firstWeight lastWeight alpha beta) parameter :=
  IsMinOn.of_isLocalMinOn_of_convexOn hfeasible hlocal
    (actual_neuron_sdp_objective_is_convex firstWeight lastWeight alpha beta)

theorem diagonal_multiplier_cone_is_convex :
    Convex ℝ {multiplier : K → ℝ | ∀ k, 0 ≤ multiplier k} := by
  intro first hf second hs a b ha hb hab k
  exact add_nonneg (mul_nonneg ha (hf k)) (mul_nonneg hb (hs k))

end SafeLearning.CompleteModulesLipSDPConvex
