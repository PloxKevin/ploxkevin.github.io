import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesLipSDP

/-- Every finite chord has a slope in the declared interval. -/
def slopeRestricted (activation : ℝ → ℝ) (alpha beta : ℝ) : Prop :=
  ∀ first second : ℝ, ∃ slope : ℝ, alpha ≤ slope ∧ slope ≤ beta ∧
    activation first-activation second=slope*(first-second)

theorem scalar_slope_quadratic_constraint (activation : ℝ → ℝ) (alpha beta : ℝ)
    (hactivation : slopeRestricted activation alpha beta) (first second : ℝ) :
    0 ≤  -2*alpha*beta*(first-second)^2+
      2*(alpha+beta)*(first-second)*(activation first-activation second)-
      2*(activation first-activation second)^2 := by
  obtain ⟨slope,hl,hu,he⟩ := hactivation first second
  rw [he]
  have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu))
    (sq_nonneg (first-second))
  nlinarith

theorem relu_slope_restricted : slopeRestricted (fun value : ℝ =>  max value 0) 0 1 := by
  intro first second
  by_cases he : first=second
  · subst second
    refine ⟨0,by norm_num,by norm_num,by simp⟩
  · refine ⟨(max first 0-max second 0)/(first-second),?_,?_,?_⟩
    · by_cases hs : second < first
      · apply div_nonneg _ (sub_nonneg.mpr hs.le)
        exact sub_nonneg.mpr (max_le_max hs.le le_rfl)
      · apply div_nonneg_of_nonpos
        · exact sub_nonpos.mpr (max_le_max (le_of_not_gt hs) le_rfl)
        · exact sub_nonpos.mpr (le_of_not_gt hs)
    · have hab := abs_max_sub_max_le_abs first second 0
      have hd : first-second≠0 := sub_ne_zero.mpr he
      have hnorm : |(max first 0-max second 0)/(first-second)| ≤ 1 := by
        rw [abs_div,div_le_one (abs_pos.mpr hd)]
        exact hab
      exact le_trans (le_abs_self _) hnorm
    · exact (div_mul_cancel₀ _ (sub_ne_zero.mpr he)).symm

variable {N K I O : Type*} [Fintype N] [Fintype K] [Fintype I] [Fintype O]
    [DecidableEq K]

def quadratic (matrix : Matrix N N ℝ) (vector : N → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

theorem quadratic_add (first second : Matrix N N ℝ) (vector : N → ℝ) :
    quadratic (first+second) vector=quadratic first vector+quadratic second vector := by
  simp [quadratic,Matrix.add_mulVec,dotProduct_add]

theorem quadratic_sub (first second : Matrix N N ℝ) (vector : N → ℝ) :
    quadratic (first-second) vector=quadratic first vector-quadratic second vector := by
  simp [quadratic,Matrix.sub_mulVec,dotProduct_sub]

theorem quadratic_smul (matrix : Matrix N N ℝ) (scalar : ℝ) (vector : N → ℝ) :
    quadratic (scalar • matrix) vector=scalar*quadratic matrix vector := by
  simp [quadratic,Matrix.smul_mulVec,dotProduct_smul]

theorem negative_semidefinite_quadratic (matrix : Matrix N N ℝ)
    (hnegative : (-matrix).PosSemidef) (vector : N → ℝ) : quadratic matrix vector ≤ 0 := by
  have h := hnegative.dotProduct_mulVec_nonneg vector
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at h
  exact neg_nonneg.mp h

theorem squared_norm_of_coordinates {J : Type*} [Fintype J] (vector : J → ℝ) :
    ‖WithLp.toLp 2 vector‖^2=∑ j, (vector j)^2 := by
  rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply]
  simp [RCLike.inner_apply,conj_trivial,pow_two]

omit [DecidableEq K] in
theorem quadratic_gram (matrix : Matrix K N ℝ) (vector : N → ℝ) :
    quadratic (matrixᵀ*matrix) vector=∑ k, ((matrix *ᵥ vector) k)^2 := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp [dotProduct,pow_two]

theorem quadratic_diagonal_pullback (first second : Matrix K N ℝ)
    (multiplier : K → ℝ) (vector : N → ℝ) :
    quadratic (firstᵀ*Matrix.diagonal multiplier*second) vector=
      ∑ k, multiplier k*((first *ᵥ vector) k)*((second *ᵥ vector) k) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_diagonal,dotProduct]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def certificateMatrix (preactivation hidden : Matrix K N ℝ)
    (input : Matrix I N ℝ) (output : Matrix O N ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ) : Matrix N N ℝ :=
  outputᵀ*output-rho • (inputᵀ*input)+
    (-2*alpha*beta) • (preactivationᵀ*Matrix.diagonal multiplier*preactivation)+
    (alpha+beta) • (preactivationᵀ*Matrix.diagonal multiplier*hidden+
      hiddenᵀ*Matrix.diagonal multiplier*preactivation)-
    (2:ℝ) • (hiddenᵀ*Matrix.diagonal multiplier*hidden)

theorem certificate_quadratic_identity (preactivation hidden : Matrix K N ℝ)
    (input : Matrix I N ℝ) (output : Matrix O N ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ) (vector : N → ℝ) :
    quadratic (certificateMatrix preactivation hidden input output alpha beta rho multiplier) vector=
      (∑ o, ((output *ᵥ vector) o)^2)-rho*(∑ i, ((input *ᵥ vector) i)^2)+
      ∑ k, multiplier k*(-2*alpha*beta*((preactivation *ᵥ vector) k)^2+
        2*(alpha+beta)*((preactivation *ᵥ vector) k)*((hidden *ᵥ vector) k)-
        2*((hidden *ᵥ vector) k)^2) := by
  simp only [certificateMatrix,quadratic_add,quadratic_sub,quadratic_smul,
    quadratic_gram,quadratic_diagonal_pullback]
  have hc : (∑ k, multiplier k*((hidden *ᵥ vector) k)*((preactivation *ᵥ vector) k))=
      ∑ k, multiplier k*((preactivation *ᵥ vector) k)*((hidden *ᵥ vector) k) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hc]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,pow_two]
  ring_nf
  simp only [Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  ring

/-- General finite lifted LipSDP soundness. The preactivation and hidden rows
may contain every neuron of a multi-layer network; the relation is the actual
increment of its elementwise activation, with all biases already cancelled. -/
theorem finite_lifted_lipsdp_soundness (preactivation hidden : Matrix K N ℝ)
    (input : Matrix I N ℝ) (output : Matrix O N ℝ)
    (activation : ℝ → ℝ) (alpha beta rho : ℝ) (multiplier : K → ℝ)
    (hactivation : slopeRestricted activation alpha beta)
    (hmultiplier : ∀ k, 0 ≤ multiplier k) (hrho : 0 ≤ rho)
    (hcertificate : (-(certificateMatrix preactivation hidden input output alpha beta rho multiplier)).PosSemidef)
    (first second : N → ℝ) (bias : K → ℝ)
    (hhidden : ∀ k, (hidden *ᵥ (first-second)) k=
      activation ((preactivation *ᵥ first) k+bias k)-
        activation ((preactivation *ᵥ second) k+bias k)) :
    ‖WithLp.toLp 2 (output *ᵥ (first-second))‖ ≤
      Real.sqrt rho*‖WithLp.toLp 2 (input *ᵥ (first-second))‖ := by
  have hqc : 0 ≤ ∑ k, multiplier k*(-2*alpha*beta*((preactivation *ᵥ (first-second)) k)^2+
      2*(alpha+beta)*((preactivation *ᵥ (first-second)) k)*((hidden *ᵥ (first-second)) k)-
      2*((hidden *ᵥ (first-second)) k)^2) := by
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg (hmultiplier k)
    rw [hhidden k]
    have h := scalar_slope_quadratic_constraint activation alpha beta hactivation
      ((preactivation *ᵥ first) k+bias k) ((preactivation *ᵥ second) k+bias k)
    simpa only [Matrix.mulVec_sub,Pi.sub_apply,add_sub_add_right_eq_sub] using h
  have hnegative := negative_semidefinite_quadratic _ hcertificate (first-second)
  rw [certificate_quadratic_identity] at hnegative
  have hsq : ‖WithLp.toLp 2 (output *ᵥ (first-second))‖^2 ≤
      rho*‖WithLp.toLp 2 (input *ᵥ (first-second))‖^2 := by
    rw [squared_norm_of_coordinates,squared_norm_of_coordinates]
    linarith
  have hs := Real.sq_sqrt hrho
  nlinarith [norm_nonneg (WithLp.toLp 2 (output *ᵥ (first-second))),
    norm_nonneg (WithLp.toLp 2 (input *ᵥ (first-second))),Real.sqrt_nonneg rho,
    mul_nonneg (Real.sqrt_nonneg rho) (norm_nonneg (WithLp.toLp 2 (input *ᵥ (first-second))))]

end SafeLearning.CompleteModulesLipSDP
