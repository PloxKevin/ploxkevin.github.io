import SafeLearning.CompleteModulesLipSDP
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNTanhSectorClass24
open CompleteModulesLipSDP

def stackedGain {n : Type*} [DecidableEq n] (d : n→ℝ) : Matrix (n⊕n) n ℝ :=
  Matrix.fromRows 1 (Matrix.diagonal d)

theorem actual_stacked_identity_diagonal_gain_matrix_has_the_printed_action
    {n : Type*} [Fintype n] [DecidableEq n] (d v : n→ℝ) :
    (stackedGain d).mulVec v=Sum.elim v (fun i=>d i*v i) := by
  funext i
  cases i <;> simp [stackedGain,Matrix.fromRows_mulVec,Matrix.mulVec_diagonal]

theorem actual_robust_full_block_psd_condition_gives_every_pointwise_gain_box_qc
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix (n⊕n) (n⊕n) ℝ)
    (hQ : ∀ d : n→ℝ, (∀ i,0≤d i ∧ d i≤1) →
      ((stackedGain d).transpose*Q*stackedGain d).PosSemidef) :
    ∀ v d : n→ℝ, (∀ i,0≤d i ∧ d i≤1) →
      0≤quadratic Q (Sum.elim v (fun i=>d i*v i)) := by
  intro v d hd
  have h := (hQ d hd).dotProduct_mulVec_nonneg v
  rw [star_trivial,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec,dotProduct_comm] at h
  simpa only [actual_stacked_identity_diagonal_gain_matrix_has_the_printed_action,quadratic] using h

theorem actual_robust_full_block_psd_condition_applies_to_independent_scalar_sector_channels
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix (n⊕n) (n⊕n) ℝ) (f : n→ℝ→ℝ)
    (hQ : ∀ d : n→ℝ, (∀ i,0≤d i ∧ d i≤1) →
      ((stackedGain d).transpose*Q*stackedGain d).PosSemidef)
    (hf : ∀ i,slopeRestricted (f i) 0 1) (hz : ∀ i,f i 0=0) (v : n→ℝ) :
    0≤quadratic Q (Sum.elim v (fun i=>f i (v i))) := by
  have he : ∀ i,∃ d : ℝ,0≤d ∧ d≤1 ∧ f i (v i)=d*v i := by
    intro i
    obtain ⟨d,hd0,hd1,hd⟩ := hf i (v i) 0
    exact ⟨d,hd0,hd1,by simpa only [hz i,sub_zero] using hd⟩
  choose d hd0 hd1 hd using he
  simpa only [←hd] using
    actual_robust_full_block_psd_condition_gives_every_pointwise_gain_box_qc Q hQ v d
      (fun i=>⟨hd0 i,hd1 i⟩)

theorem actual_bias_free_tanh_network_at_zero_has_zero_outputs_and_preactivations_at_every_depth
    (width : ℕ→ℕ)
    (weights : (k : ℕ)→Matrix (Fin (width (k+1))) (Fin (width k)) ℝ)
    (layer : (k : ℕ)→Fin (width k)→ℝ)
    (hinitial : layer 0=0)
    (hstep : ∀ k,layer (k+1)=fun i=>Real.tanh ((weights k).mulVec (layer k) i)) :
    ∀ k,layer k=0 ∧ (weights k).mulVec (layer k)=0 := by
  have hz : ∀ k,layer k=0 := by
    intro k
    induction k with
    | zero => exact hinitial
    | succ k ih =>
      rw [hstep,ih]
      funext i
      simp
  exact fun k=>⟨hz k,by simp [hz k]⟩

end SafeLearning.CompleteModulesNNTanhSectorClass24
