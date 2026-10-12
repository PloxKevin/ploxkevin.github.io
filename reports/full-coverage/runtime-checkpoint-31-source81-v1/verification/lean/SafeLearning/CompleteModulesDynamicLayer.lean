import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDynamicLayer
open CompleteModulesLipSDP
variable {S I O J K : Type*} [Fintype S] [Fintype I] [Fintype O]
    [Fintype J] [Fintype K] [DecidableEq O]

def actualLayerCertificate (A : Matrix S S ℝ) (B : Matrix S I ℝ)
    (C : Matrix O S ℝ) (D : Matrix O I ℝ) (P : Matrix S S ℝ)
    (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ) :
    Matrix ((S ⊕ I) ⊕ O) ((S ⊕ I) ⊕ O) ℝ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (P-Aᵀ*P*A) (-Aᵀ*P*B) (-Bᵀ*P*A) (Xin-Bᵀ*P*B))
    (Matrix.fromRows (-Cᵀ*Matrix.diagonal multiplier) (-Dᵀ*Matrix.diagonal multiplier))
    (Matrix.fromCols (-Matrix.diagonal multiplier*C) (-Matrix.diagonal multiplier*D))
    ((2:ℝ) • Matrix.diagonal multiplier-Xout)

theorem actual_bilinear_matrix_pullback (M : Matrix J K ℝ) (P : Matrix J J ℝ)
    (N : Matrix J S ℝ) (first : K → ℝ) (second : S → ℝ) :
    first ⬝ᵥ ((Mᵀ*P*N) *ᵥ second) =
      (M *ᵥ first) ⬝ᵥ (P *ᵥ (N *ᵥ second)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

theorem actual_quadratic_state_increment_expansion (P : Matrix S S ℝ)
    (first second : S → ℝ) :
    quadratic P (first+second)=quadratic P first+quadratic P second+
      first ⬝ᵥ (P *ᵥ second)+second ⬝ᵥ (P *ᵥ first) := by
  simp only [quadratic,Matrix.mulVec_add,dotProduct_add,add_dotProduct]
  ring

theorem actual_layer_certificate_quadratic_identity (A : Matrix S S ℝ) (B : Matrix S I ℝ)
    (C : Matrix O S ℝ) (D : Matrix O I ℝ) (P : Matrix S S ℝ)
    (Xin : Matrix I I ℝ) (Xout : Matrix O O ℝ) (multiplier : O → ℝ)
    (state : S → ℝ) (input : I → ℝ) (hidden : O → ℝ) :
    quadratic (actualLayerCertificate A B C D P Xin Xout multiplier)
      (Sum.elim (Sum.elim state input) hidden)=
      quadratic P state-quadratic P (A *ᵥ state+B *ᵥ input)+
      quadratic Xin input-quadratic Xout hidden-
      ∑ coordinate, multiplier coordinate*
        (2*((C *ᵥ state+D *ᵥ input) coordinate)*(hidden coordinate)-2*(hidden coordinate)^2) := by
  have hqc : (∑ coordinate, multiplier coordinate*
      (2*((C *ᵥ state+D *ᵥ input) coordinate)*(hidden coordinate)-2*(hidden coordinate)^2))=
      2*(∑ coordinate,multiplier coordinate*hidden coordinate*(C *ᵥ state) coordinate)+
      2*(∑ coordinate,multiplier coordinate*hidden coordinate*(D *ᵥ input) coordinate)-
      2*(∑ coordinate,multiplier coordinate*(hidden coordinate)^2) := by
    calc
      _ = ∑ coordinate, (2*(multiplier coordinate*hidden coordinate*(C *ᵥ state) coordinate)+
        2*(multiplier coordinate*hidden coordinate*(D *ᵥ input) coordinate)-
        2*(multiplier coordinate*(hidden coordinate)^2)) := by
          apply Finset.sum_congr rfl
          intro coordinate hcoordinate
          simp only [Pi.add_apply]
          ring
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
        ← Finset.mul_sum,← Finset.mul_sum]
  rw [hqc]
  simp only [actualLayerCertificate,quadratic,Matrix.fromBlocks_mulVec,Matrix.fromRows_mulVec,
    Matrix.fromCols_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    sumElim_dotProduct_sumElim,Matrix.sub_mulVec,Matrix.neg_mulVec,Matrix.neg_mul,
    Matrix.smul_mulVec,dotProduct_add,dotProduct_sub,dotProduct_neg,add_dotProduct,dotProduct_smul]
  simp only [actual_bilinear_matrix_pullback,← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_add,add_dotProduct,dotProduct_add]
  simp only [Matrix.mulVec_diagonal,dotProduct,Pi.mul_apply,Pi.add_apply,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
  simp only [mul_comm,mul_left_comm,mul_assoc]
  ring_nf
  rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
  ring

end SafeLearning.CompleteModulesDynamicLayer
