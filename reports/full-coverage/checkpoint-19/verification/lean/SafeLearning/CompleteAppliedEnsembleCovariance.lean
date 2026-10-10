import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedEnsembleCovariance

variable {E I : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

def ensembleMean (X : E → I → ℝ) : I → ℝ :=
  fun i => (Fintype.card E:ℝ)⁻¹*∑ e,X e i

def centeredColumns (X : E → I → ℝ) : Matrix I E ℝ :=
  fun i e => X e i-ensembleMean X i

def empiricalCovariance (X : E → I → ℝ) : Matrix I I ℝ :=
  (Fintype.card E:ℝ)⁻¹ • (centeredColumns X*(centeredColumns X)ᵀ)

theorem actual_empirical_covariance_is_the_literal_average_centered_outer_product
    (X : E → I → ℝ) :
    empiricalCovariance X=(Fintype.card E:ℝ)⁻¹ •
      ∑ e,vecMulVec (fun i => X e i-ensembleMean X i)
        (fun i => X e i-ensembleMean X i) := by
  ext i j
  simp [empiricalCovariance,centeredColumns,Matrix.mul_apply,vecMulVec,
    Matrix.sum_apply]

theorem actual_centered_ensemble_columns_sum_to_zero (X : E → I → ℝ) (i : I) :
    ∑ e,centeredColumns X i e=0 := by
  have hn : (Fintype.card E:ℝ)≠0 := by exact_mod_cast (Fintype.card_pos.ne' : Fintype.card E≠0)
  simp [centeredColumns,ensembleMean,Finset.sum_sub_distrib]

lemma actual_ones_column_has_rank_one :
    Matrix.rank ((fun (_ : E) (_ : Unit) => (1:ℝ)) : Matrix E Unit ℝ)=1 := by
  have hi : Function.Injective (Matrix.mulVecLin (fun (_ : E) (_ : Unit) => (1:ℝ))) := by
    intro u v huv
    funext j
    have h := congrFun huv (Classical.choice (inferInstance : Nonempty E))
    change (∑ k : Unit,1*u k)=(∑ k : Unit,1*v k) at h
    simpa using h
  change Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (fun (_ : E) (_ : Unit) => (1:ℝ))))=1
  rw [LinearMap.finrank_range_of_inj hi]
  simp

theorem actual_empirical_covariance_rank_is_at_most_member_count_minus_one
    (X : E → I → ℝ) : (empiricalCovariance X).rank≤Fintype.card E-1 := by
  let B : Matrix E Unit ℝ := fun _ _ => 1
  have hz : centeredColumns X*B=0 := by
    ext i j
    change (∑ e,centeredColumns X i e*1)=0
    simpa using actual_centered_ensemble_columns_sum_to_zero X i
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
  have hb : B.rank=1 := actual_ones_column_has_rank_one
  rw [hb] at hr
  have hf : empiricalCovariance X=centeredColumns X*((Fintype.card E:ℝ)⁻¹ • (centeredColumns X)ᵀ) := by
    rw [empiricalCovariance,Matrix.mul_smul]
  rw [hf]
  exact (Matrix.rank_mul_le_left _ _).trans (by omega)

theorem actual_empirical_covariance_is_positive_semidefinite
    (X : E → I → ℝ) : (empiricalCovariance X).PosSemidef := by
  have hh : (centeredColumns X*(centeredColumns X)ᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (centeredColumns X)
  exact hh.smul (by positivity)

theorem actual_empirical_covariance_is_singular_when_members_do_not_exceed_dimension
    (X : E → I → ℝ) (hcount : Fintype.card E≤Fintype.card I) :
    (empiricalCovariance X).det=0 ∧ ¬IsUnit (empiricalCovariance X) := by
  have hr := actual_empirical_covariance_rank_is_at_most_member_count_minus_one X
  have hn := Fintype.card_pos (α:=E)
  have hd : (empiricalCovariance X).det=0 := by
    by_contra h
    have hf := Matrix.rank_of_det_ne_zero h
    omega
  refine ⟨hd,?_⟩
  intro hu
  have hf := Matrix.rank_of_isUnit _ hu
  omega

theorem actual_two_member_spread_has_zero_mean_and_the_printed_singular_covariance :
    ensembleMean (![![1,0],![-1,0]] : Fin 2 → Fin 2 → ℝ)=![0,0] ∧
    empiricalCovariance (![![1,0],![-1,0]] : Fin 2 → Fin 2 → ℝ)=!![1,0;0,0] ∧
    (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧
    (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ).det=0 := by
  have hm : ensembleMean (![![1,0],![-1,0]] : Fin 2 → Fin 2 → ℝ)=![0,0] := by
    ext i
    fin_cases i <;> norm_num [ensembleMean,Fin.sum_univ_two]
  have hc : empiricalCovariance (![![1,0],![-1,0]] : Fin 2 → Fin 2 → ℝ)=!![1,0;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [empiricalCovariance,centeredColumns,hm,Matrix.mul_apply,Fin.sum_univ_two]
  refine ⟨hm,hc,?_,?_⟩
  · rw [←hc]
    exact actual_empirical_covariance_is_positive_semidefinite _
  · norm_num [Matrix.det_fin_two]

theorem actual_positive_semidefinite_member_is_invertible_iff_positive_definite
    (S : Matrix I I ℝ) (hS : S.PosSemidef) : IsUnit S ↔ S.PosDef := by
  constructor
  · intro hu
    exact hS.posDef_iff_det_ne_zero.mpr
      (isUnit_iff_ne_zero.mp (S.isUnit_iff_isUnit_det.mp hu))
  · exact PosDef.isUnit

theorem actual_fusion_of_positive_definite_member_covariances_is_positive_definite
    (S : E → Matrix I I ℝ) (hS : ∀ e,(S e).PosDef) :
    ((Fintype.card E:ℝ)⁻¹ • (∑ e,(S e)⁻¹))⁻¹ |>.PosDef := by
  have hs : (∑ e,(S e)⁻¹).PosDef := by
    exact Matrix.posDef_sum Finset.univ_nonempty (fun e _ => (hS e).inv)
  exact (hs.smul (by positivity)).inv

end SafeLearning.CompleteAppliedEnsembleCovariance
