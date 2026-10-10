import SafeLearning.CompleteModulesLipSDPNetwork
import SafeLearning.CompleteModulesDesignScalarLayers

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesDesignCertificateSet
open CompleteModulesLipSDPNetwork CompleteModulesDesignScalarLayers

def sourceFirst : Matrix (Fin 2) (Fin 1) ℝ := ![![1],![-1]]
def sourceLast : Matrix (Fin 1) (Fin 2) ℝ := ![![1,-1]]
def sourceFunction (x : ℝ) : ℝ := max x 0-max (-x) 0
def sourceCertificate (rho : ℝ) (t : Fin 2 → ℝ) :=
  blockCertificate sourceFirst sourceLast 0 1 rho t
def sourceCertifiedGains : Set ℝ := {g | 0≤g ∧ ∃ t : Fin 2 → ℝ,
  (∀ i,0≤t i) ∧ (-sourceCertificate (g^2) t).PosSemidef}

theorem actual_source_relu_cancellation_is_the_actual_weighted_network (x : ℝ) :
    sourceFunction x=x ∧
      oneHiddenNetwork sourceFirst sourceLast 0 0 (fun v=>max v 0) (fun _=>x)=
        (fun _=>sourceFunction x) := by
  constructor
  · by_cases hx : 0≤x
    · simp [sourceFunction,max_eq_left hx,max_eq_right (by linarith : -x≤0)]
    · have hl : x≤0 := le_of_not_ge hx
      simp [sourceFunction,max_eq_right hl,max_eq_left (by linarith : 0≤-x)]
  · ext i;fin_cases i
    by_cases hx : 0≤x
    · simp [oneHiddenNetwork,hiddenValues,sourceFirst,sourceLast,sourceFunction,
        Matrix.mulVec,dotProduct,Fin.sum_univ_two,max_eq_left hx,
        max_eq_right (by linarith : -x≤0)]
    · have hl : x≤0 := le_of_not_ge hx
      simp [oneHiddenNetwork,hiddenValues,sourceFirst,sourceLast,sourceFunction,
        Matrix.mulVec,dotProduct,Fin.sum_univ_two,max_eq_right hl,
        max_eq_left (by linarith : 0≤-x)]

theorem actual_source_true_gain_is_exactly_one :
    IsLeast (admissibleGains sourceFunction) 1 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro x y
    rw [(actual_source_relu_cancellation_is_the_actual_weighted_network x).1,
      (actual_source_relu_cancellation_is_the_actual_weighted_network y).1,one_mul]
  · intro L hL
    have h:=hL.2 1 0
    norm_num [(actual_source_relu_cancellation_is_the_actual_weighted_network _).1] at h
    exact h

theorem actual_source_certificate_quadratic (rho : ℝ) (t : Fin 2 → ℝ)
    (v : Fin 1 ⊕ Fin 2 → ℝ) :
    v ⬝ᵥ ((sourceCertificate rho t) *ᵥ v)=
      (v (.inr 0)-v (.inr 1))^2-rho*(v (.inl 0))^2+
      2*t 0*v (.inr 0)*(v (.inl 0)-v (.inr 0))+
      2*t 1*v (.inr 1)*(-v (.inl 0)-v (.inr 1)) := by
  simp [sourceCertificate,blockCertificate,sourceFirst,sourceLast,dotProduct,
    Matrix.mulVec,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_one,
    Fin.sum_univ_two,Matrix.fromBlocks,Matrix.diagonal_apply]
  norm_num [Matrix.transpose,Matrix.mul,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two,
    Matrix.diagonal_apply]
  ring

theorem actual_independent_all_active_pattern_forces_squared_bound_at_least_four
    (rho : ℝ) (t : Fin 2 → ℝ)
    (h : (-sourceCertificate rho t).PosSemidef) : 4≤rho := by
  let v : Fin 1 ⊕ Fin 2 → ℝ := Sum.elim (fun _=>1) ![1,-1]
  have hc:=h.dotProduct_mulVec_nonneg v
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hc
  rw [actual_source_certificate_quadratic] at hc
  norm_num [v] at hc
  linarith

theorem actual_source_squared_bound_four_has_a_genuine_diagonal_certificate :
    (-sourceCertificate 4 (fun _=>2)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    cases i with
    | inl i => cases j with
      | inl j => fin_cases i;fin_cases j;norm_num [sourceCertificate,blockCertificate,
          sourceFirst,sourceLast,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two]
        <;>norm_num [Matrix.transpose,Matrix.mul,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two,
          Matrix.diagonal_apply]
      | inr j => fin_cases i;fin_cases j <;>norm_num [sourceCertificate,blockCertificate,
          sourceFirst,sourceLast,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two]
        <;>norm_num [Matrix.transpose,Matrix.mul,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two,
          Matrix.diagonal_apply]
    | inr i => cases j with
      | inl j => fin_cases i <;>fin_cases j <;>norm_num [sourceCertificate,blockCertificate,
          sourceFirst,sourceLast,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two]
        <;>norm_num [Matrix.transpose,Matrix.mul,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two,
          Matrix.diagonal_apply]
      | inr j => fin_cases i <;>fin_cases j <;>norm_num [sourceCertificate,blockCertificate,
          sourceFirst,sourceLast,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two]
        <;>norm_num [Matrix.transpose,Matrix.mul,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two,
          Matrix.diagonal_apply]
  · intro v
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
    rw [actual_source_certificate_quadratic]
    nlinarith [sq_nonneg (2*v (.inl 0)-v (.inr 0)+v (.inr 1)),
      sq_nonneg (v (.inr 0)+v (.inr 1))]

theorem actual_minimum_diagonal_lipsdp_gain_is_two_and_unit_gain_is_excluded :
    IsLeast sourceCertifiedGains 2 ∧ 1∉sourceCertifiedGains := by
  have hl : ∀ g∈sourceCertifiedGains,2≤g := by
    intro g hg
    obtain ⟨hg, t,ht,hc⟩:=hg
    have h4:=actual_independent_all_active_pattern_forces_squared_bound_at_least_four (g^2) t hc
    nlinarith
  constructor
  · refine ⟨?_,hl⟩
    refine ⟨by norm_num,fun _=>2,by intro i;norm_num,?_⟩
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    exact actual_source_squared_bound_four_has_a_genuine_diagonal_certificate
  · intro h;have hc:=hl 1 h;norm_num at hc

theorem actual_completeness_of_a_certificate_set_does_not_require_excluded_weights
    {Parameters Weights : Type*} (parameterization : Parameters → Weights)
    (certified : Set Weights) (weight : Weights)
    (hcomplete : range parameterization=certified) (hexcluded : weight∉certified) :
    weight∉range parameterization := by rwa [hcomplete]

end SafeLearning.CompleteModulesDesignCertificateSet
