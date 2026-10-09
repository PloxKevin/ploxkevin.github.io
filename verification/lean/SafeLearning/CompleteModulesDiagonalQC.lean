import SafeLearning.CompleteModulesLipSDPNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDiagonalQC

open CompleteModulesLipSDP CompleteModulesLipSDPNetwork

def scalarQC (alpha beta input hidden : ℝ) : ℝ :=
  -2*alpha*beta*input^2+2*(alpha+beta)*input*hidden-2*hidden^2

theorem scalar_qc_factorization (alpha beta input hidden : ℝ) :
    scalarQC alpha beta input hidden=-2*(hidden-alpha*input)*(hidden-beta*input) := by
  unfold scalarQC
  ring

theorem scalar_qc_iff_admissible_chord (alpha beta input hidden : ℝ) (hab : alpha ≤ beta) :
    0 ≤ scalarQC alpha beta input hidden ↔
      ∃ slope : ℝ, alpha ≤ slope ∧ slope ≤ beta ∧ hidden=slope*input := by
  constructor
  · intro hqc
    by_cases hi : input=0
    · subst input
      have hh : hidden=0 := by
        unfold scalarQC at hqc
        nlinarith [sq_nonneg hidden]
      exact ⟨alpha,le_rfl,hab,by simp [hh]⟩
    · let slope : ℝ := hidden/input
      have he : hidden=slope*input := by
        exact (div_mul_cancel₀ hidden hi).symm
      have hf : scalarQC alpha beta input hidden=
          (2*input^2)*((slope-alpha)*(beta-slope)) := by
        rw [he]
        unfold scalarQC
        ring
      rw [hf] at hqc
      have hp : 0 ≤ (slope-alpha)*(beta-slope) :=
        (mul_nonneg_iff_of_pos_left (show 0 < 2*input^2 by
          exact mul_pos (by norm_num) (sq_pos_of_ne_zero hi))).mp hqc
      rcases mul_nonneg_iff.mp hp with ⟨hl,hu⟩ | ⟨hl,hu⟩
      · exact ⟨slope,by linarith,by linarith,he⟩
      · exact ⟨slope,by linarith,by linarith,he⟩
  · rintro ⟨slope,hl,hu,he⟩
    rw [he]
    unfold scalarQC
    have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu))
      (sq_nonneg input)
    nlinarith

variable {K : Type*} [Fintype K] [DecidableEq K]

def diagonalQC (alpha beta : ℝ) (multiplier input hidden : K → ℝ) : ℝ :=
  ∑ k, multiplier k*scalarQC alpha beta (input k) (hidden k)

theorem diagonal_qc_from_actual_activations (activation : K → ℝ → ℝ) (alpha beta : ℝ)
    (hactivation : ∀ k, slopeRestricted (activation k) alpha beta)
    (multiplier : K → ℝ) (hmultiplier : ∀ k, 0 ≤ multiplier k) (first second : K → ℝ) :
    0 ≤ diagonalQC alpha beta multiplier (first-second)
      (fun k => activation k (first k)-activation k (second k)) := by
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg (hmultiplier k)
  exact scalar_slope_quadratic_constraint (activation k) alpha beta (hactivation k) (first k) (second k)

theorem all_diagonal_qcs_iff_coordinate_qcs (alpha beta : ℝ) (input hidden : K → ℝ) :
    (∀ multiplier : K → ℝ, (∀ k, 0 ≤ multiplier k) →
      0 ≤ diagonalQC alpha beta multiplier input hidden) ↔
    ∀ k, 0 ≤ scalarQC alpha beta (input k) (hidden k) := by
  constructor
  · intro h k
    have hs := h (Pi.single k 1) (by intro j; simp [Pi.single_apply]; split_ifs <;> norm_num)
    simpa [diagonalQC,Pi.single_apply] using hs
  · intro h multiplier hm
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hm k) (h k))

theorem all_diagonal_qcs_iff_independent_diagonal_slopes
    (alpha beta : ℝ) (hab : alpha ≤ beta) (input hidden : K → ℝ) :
    (∀ multiplier : K → ℝ, (∀ k, 0 ≤ multiplier k) →
      0 ≤ diagonalQC alpha beta multiplier input hidden) ↔
    ∃ slope : K → ℝ, (∀ k, alpha ≤ slope k ∧ slope k ≤ beta) ∧
      hidden=Matrix.diagonal slope *ᵥ input := by
  rw [all_diagonal_qcs_iff_coordinate_qcs]
  constructor
  · intro h
    have hc : ∀ k, ∃ slope : ℝ, alpha ≤ slope ∧ slope ≤ beta ∧ hidden k=slope*input k :=
      fun k => (scalar_qc_iff_admissible_chord alpha beta (input k) (hidden k) hab).mp (h k)
    choose slope hl hu he using hc
    exact ⟨slope,fun k => ⟨hl k,hu k⟩,by ext k; simp [Matrix.mulVec_diagonal,he k]⟩
  · rintro ⟨slope,hbounds,he⟩ k
    apply (scalar_qc_iff_admissible_chord alpha beta (input k) (hidden k) hab).mpr
    refine ⟨slope k,(hbounds k).1,(hbounds k).2,?_⟩
    rw [he,Matrix.mulVec_diagonal]

def diagonalQCMatrix (alpha beta : ℝ) (multiplier : K → ℝ) : Matrix (K ⊕ K) (K ⊕ K) ℝ :=
  blockCertificate (1 : Matrix K K ℝ) (0 : Matrix K K ℝ) alpha beta 0 multiplier

theorem diagonal_qc_matrix_is_stated_block (alpha beta : ℝ) (multiplier : K → ℝ) :
    diagonalQCMatrix alpha beta multiplier=
      Matrix.fromBlocks ((-2*alpha*beta) • Matrix.diagonal multiplier)
        ((alpha+beta) • Matrix.diagonal multiplier)
        ((alpha+beta) • Matrix.diagonal multiplier)
        ((-2:ℝ) • Matrix.diagonal multiplier) := by
  simp [diagonalQCMatrix,blockCertificate]

theorem diagonal_qc_is_actual_block_quadratic (alpha beta : ℝ) (multiplier input hidden : K → ℝ) :
    quadratic (diagonalQCMatrix alpha beta multiplier) (Sum.elim input hidden)=
      diagonalQC alpha beta multiplier input hidden := by
  unfold diagonalQCMatrix
  rw [← canonical_certificate_is_stated_block_matrix]
  unfold canonicalCertificate
  rw [certificate_quadratic_identity]
  simp [diagonalQC,scalarQC,Matrix.fromCols_mulVec_sumElim]

end SafeLearning.CompleteModulesDiagonalQC
