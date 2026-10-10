import SafeLearning.CompleteModulesSDPCone
import SafeLearning.CompleteModulesSDPTrace

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesSDPDual
open CompleteModulesSDPCone CompleteModulesSDPTrace

variable {Index Parameter : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Parameter] [DecidableEq Parameter]

def actualSDPLagrangian (constant : Matrix Index Index ℝ)
    (coefficient : Parameter→Matrix Index Index ℝ) (cost unknown : Parameter→ℝ)
    (dual : Matrix Index Index ℝ) : ℝ :=
  cost ⬝ᵥ unknown-(dual*actualAffineMatrix constant coefficient unknown).trace

def actualSDPDualValue (constant : Matrix Index Index ℝ)
    (coefficient : Parameter→Matrix Index Index ℝ) (cost : Parameter→ℝ)
    (dual : Matrix Index Index ℝ) : EReal :=
  sInf {value | ∃ unknown : Parameter→ℝ,value=(actualSDPLagrangian constant coefficient cost unknown dual : EReal)}

omit [DecidableEq Index] [DecidableEq Parameter] in
theorem actual_sdp_lagrangian_has_the_literal_trace_coefficient_expansion
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost unknown : Parameter→ℝ) (dual : Matrix Index Index ℝ) :
    actualSDPLagrangian constant coefficient cost unknown dual=
      (fun parameter => cost parameter-(coefficient parameter*dual).trace) ⬝ᵥ unknown-
        (constant*dual).trace := by
  unfold actualSDPLagrangian
  rw [Matrix.trace_mul_comm]
  simp only [actualAffineMatrix,Matrix.add_mul,Matrix.sum_mul,Matrix.smul_mul,
    Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,
    dotProduct,Finset.sum_sub_distrib,sub_mul]
  have hs : (∑ parameter,unknown parameter*(coefficient parameter*dual).trace)=
      ∑ parameter,(coefficient parameter*dual).trace*unknown parameter := by
    apply Finset.sum_congr rfl
    intro parameter _
    ring
  rw [hs];ring

omit [DecidableEq Index] in
theorem actual_sdp_dual_is_the_true_extended_infimum_with_exact_coefficient_domain
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost : Parameter→ℝ) (dual : Matrix Index Index ℝ) :
    actualSDPDualValue constant coefficient cost dual=
      if ∀ parameter,(coefficient parameter*dual).trace=cost parameter
      then ((-(constant*dual).trace : ℝ) : EReal) else (⊥ : EReal) := by
  classical
  by_cases hcoeff : ∀ parameter,(coefficient parameter*dual).trace=cost parameter
  · rw [ite_eq_left hcoeff]
    unfold actualSDPDualValue
    have he : {value : EReal | ∃ unknown : Parameter→ℝ,
        value=(actualSDPLagrangian constant coefficient cost unknown dual : EReal)}=
        {((-(constant*dual).trace : ℝ) : EReal)} := by
      ext value
      simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff]
      constructor
      · rintro ⟨unknown,rfl⟩
        rw [actual_sdp_lagrangian_has_the_literal_trace_coefficient_expansion]
        simp [hcoeff,dotProduct]
      · intro heq
        refine ⟨0,?_⟩
        rw [actual_sdp_lagrangian_has_the_literal_trace_coefficient_expansion]
        simpa using heq
    rw [he,sInf_singleton]
  · rw [ite_eq_right hcoeff]
    push Not at hcoeff
    obtain ⟨parameter,hparameter⟩ := hcoeff
    have hn : cost parameter-(coefficient parameter*dual).trace≠0 := by
      exact sub_ne_zero.mpr (Ne.symm hparameter)
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro bound
    let unknown : Parameter→ℝ := Pi.single parameter
      ((bound+(constant*dual).trace-1)/(cost parameter-(coefficient parameter*dual).trace))
    have hl : actualSDPLagrangian constant coefficient cost unknown dual=bound-1 := by
      rw [actual_sdp_lagrangian_has_the_literal_trace_coefficient_expansion]
      unfold unknown
      rw [dotProduct_single]
      field_simp [hn]
      ring
    have hi : actualSDPDualValue constant coefficient cost dual≤
        (actualSDPLagrangian constant coefficient cost unknown dual : EReal) :=
      sInf_le ⟨unknown,rfl⟩
    rw [hl] at hi
    exact lt_of_le_of_lt hi (EReal.coe_lt_coe_iff.mpr (by linarith))

omit [DecidableEq Index] [DecidableEq Parameter] in
theorem actual_primal_dual_objective_gap_is_the_true_trace_pairing
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost unknown : Parameter→ℝ) (dual : Matrix Index Index ℝ)
    (hdual : ∀ parameter,(coefficient parameter*dual).trace=cost parameter) :
    cost ⬝ᵥ unknown+(constant*dual).trace=(actualAffineMatrix constant coefficient unknown*dual).trace := by
  simp only [actualAffineMatrix,Matrix.add_mul,Matrix.sum_mul,Matrix.smul_mul,
    Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,dotProduct]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro parameter _
  simp [hdual parameter,smul_eq_mul,mul_comm]

omit [DecidableEq Parameter] in
theorem actual_every_primal_and_dual_feasible_pair_obeys_weak_duality
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost unknown : Parameter→ℝ) (dual : Matrix Index Index ℝ)
    (hprimal : (actualAffineMatrix constant coefficient unknown).PosSemidef)
    (hdual : dual.PosSemidef) (hcoeff : ∀ parameter,(coefficient parameter*dual).trace=cost parameter) :
    -(constant*dual).trace≤cost ⬝ᵥ unknown := by
  have hgap := actual_primal_dual_objective_gap_is_the_true_trace_pairing constant coefficient cost unknown dual hcoeff
  have ht := actual_psd_matrices_have_nonnegative_trace_pairing _ _ hprimal hdual
  linarith

omit [DecidableEq Parameter] in
theorem actual_zero_primal_dual_objective_gap_iff_true_matrix_complementary_slackness
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost unknown : Parameter→ℝ) (dual : Matrix Index Index ℝ)
    (hprimal : (actualAffineMatrix constant coefficient unknown).PosSemidef)
    (hdual : dual.PosSemidef) (hcoeff : ∀ parameter,(coefficient parameter*dual).trace=cost parameter) :
    cost ⬝ᵥ unknown= -(constant*dual).trace ↔ actualAffineMatrix constant coefficient unknown*dual=0 := by
  have hg := actual_primal_dual_objective_gap_is_the_true_trace_pairing constant coefficient cost unknown dual hcoeff
  rw [←actual_trace_zero_of_two_psd_matrices_iff_actual_matrix_product_zero _ _ hprimal hdual]
  constructor <;> intro h <;> linarith

omit [Fintype Parameter] [DecidableEq Parameter] in
theorem actual_pd_and_nonzero_psd_matrices_have_strictly_positive_trace_pairing
    (first second : Matrix Index Index ℝ) (hf : first.PosDef) (hs : second.PosSemidef) (hn : second≠0) :
    0 < (first*second).trace := by
  have hnonnegative := actual_psd_matrices_have_nonnegative_trace_pairing first second hf.posSemidef hs
  apply lt_of_le_of_ne hnonnegative
  intro heq
  have hz := (actual_trace_zero_of_two_psd_matrices_iff_actual_matrix_product_zero first second hf.posSemidef hs).mp heq.symm
  have hc := congrArg (fun matrix : Matrix Index Index ℝ => first⁻¹*matrix) hz
  rw [Matrix.nonsing_inv_mul_cancel_left first second (first.isUnit_iff_isUnit_det.mp hf.isUnit),Matrix.mul_zero] at hc
  exact hn hc

omit [DecidableEq Parameter] in
theorem actual_nonzero_psd_dual_homogeneous_witness_excludes_strict_primal_feasibility
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (dual : Matrix Index Index ℝ) (hdual : dual.PosSemidef) (hnonzero : dual≠0)
    (hcoeff : ∀ parameter,(coefficient parameter*dual).trace=0)
    (hconstant : (constant*dual).trace≤0) :
    ∀ unknown : Parameter→ℝ,¬(actualAffineMatrix constant coefficient unknown).PosDef := by
  intro unknown hprimal
  have hpositive := actual_pd_and_nonzero_psd_matrices_have_strictly_positive_trace_pairing _ _ hprimal hdual hnonzero
  have htrace := actual_primal_dual_objective_gap_is_the_true_trace_pairing constant coefficient 0 unknown dual hcoeff
  simp only [zero_dotProduct,zero_add] at htrace
  linarith

end SafeLearning.CompleteModulesSDPDual
