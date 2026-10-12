import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace SafeLearning.CompleteFoundationsParsevalModels

section General
variable {M N : Type*} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
abbrev Space (M N : Type*) [Fintype M] [Fintype N] := EuclideanSpace ℝ (M×N)

def toMatrix (w : Space M N) : Matrix M N ℝ := fun i j => w (i,j)
def fromMatrix (w : Matrix M N ℝ) : Space M N := WithLp.toLp 2 (fun ij => w ij.1 ij.2)
def entry (i : M) (j : N) : Space M N →L[ℝ] ℝ := PiLp.proj 2 (fun _ : M×N => ℝ) (i,j)
def errorMatrix (w : Space M N) : Matrix M M ℝ := toMatrix w*(toMatrix w)ᵀ-1
def objective (beta : ℝ) (w : Space M N) : ℝ := beta/4*‖errorMatrix w‖^2
def errorEntry (w : Space M N) (i j : M) : ℝ :=
  (∑ k : N,w (i,k)*w (j,k))-(if i=j then 1 else 0)
def errorDerivative (w : Space M N) (i j : M) : Space M N →L[ℝ] ℝ :=
  ∑ k : N,((w (j,k)) • entry i k+(w (i,k)) • entry j k)
def sourceGradient (beta : ℝ) (w : Space M N) : Space M N :=
  fromMatrix (beta • (errorMatrix w*toMatrix w))

theorem actual_frobenius_squared (X : Matrix M N ℝ) :
    ‖X‖^2=∑ i : M,∑ j : N,(X i j)^2 := by
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt]
  · simp [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  · positivity

theorem actual_error_entries (w : Space M N) (i j : M) :
    errorMatrix w i j=errorEntry w i j := by
  simp [errorMatrix,errorEntry,toMatrix,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]

theorem actual_objective_expansion (beta : ℝ) (w : Space M N) :
    objective beta w=beta/4*(∑ i : M,∑ j : M,(errorEntry w i j)^2) := by
  rw [objective,actual_frobenius_squared]
  simp only [actual_error_entries]

theorem actual_error_is_symmetric (w : Space M N) : (errorMatrix w)ᵀ=errorMatrix w := by
  simp [errorMatrix,Matrix.transpose_mul]

theorem actual_entry_differential (w : Space M N) (i j : M) :
    HasFDerivAt (fun v : Space M N => errorEntry v i j) (errorDerivative w i j) w := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((entry i k).hasFDerivAt (x := w)).mul ((entry j k).hasFDerivAt (x := w)))
  convert h.sub_const (if i=j then 1 else 0) using 1
  · rfl
  · ext u
    simp [errorDerivative,entry,PiLp.proj,PiLp.projₗ,add_comm]

theorem actual_symmetric_trace_identity (S : Matrix M M ℝ) (hS : Sᵀ=S)
    (W H : Matrix M N ℝ) :
    (∑ i : M,∑ j : M,S i j*(∑ k : N,(W j k*H i k+W i k*H j k)))=
      2*(∑ i : M,∑ k : N,(∑ j : M,S i j*W j k)*H i k) := by
  have hs (i j : M) : S j i=S i j := congrFun (congrFun hS i) j
  have hb : (∑ i : M,∑ j : M,∑ k : N,S i j*(W i k*H j k))=
      (∑ i : M,∑ j : M,∑ k : N,S i j*(W j k*H i k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hs]
  have ha : (∑ i : M,∑ j : M,∑ k : N,S i j*(W j k*H i k))=
      (∑ i : M,∑ k : N,(∑ j : M,S i j*W j k)*H i k) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  rw [hb,ha]
  simp [two_mul,Finset.sum_add_distrib]

theorem actual_inner_coordinates (w v : Space M N) :
    inner ℝ w v=∑ i : M,∑ j : N,w (i,j)*v (i,j) := by
  simp [PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,mul_comm]

theorem actual_parseval_gradient (beta : ℝ) (w : Space M N) :
    HasGradientAt (objective beta) (sourceGradient beta w) w := by
  have hf : HasFDerivAt (objective beta)
      ((beta/2) • ∑ i : M,∑ j : M,errorEntry w i j • errorDerivative w i j) w := by
    have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (actual_entry_differential w i j).pow 2))).const_mul (beta/4)
    convert h using 1
    · exact funext (actual_objective_expansion beta)
    · ext u
      simp
      simp_rw [two_mul,add_mul,Finset.sum_add_distrib]
      ring
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext u
  rw [InnerProductSpace.toDual_apply_apply,actual_inner_coordinates]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul]
  have he (i j : M) : errorDerivative w i j u=
      ∑ k : N,(toMatrix w j k*toMatrix u i k+toMatrix w i k*toMatrix u j k) := by
    simp [errorDerivative,entry,toMatrix,PiLp.proj,PiLp.projₗ]
  simp_rw [he,← actual_error_entries]
  rw [actual_symmetric_trace_identity (errorMatrix w) (actual_error_is_symmetric w)]
  simp [sourceGradient,fromMatrix,Matrix.smul_apply,Matrix.mul_apply,toMatrix]
  have hbeta (r : ℝ) : beta/2*(2*r)=beta*r := by ring
  rw [hbeta,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_gradient_matrix (beta : ℝ) (w : Space M N) :
    toMatrix (gradient (objective beta) w)=beta • ((toMatrix w*(toMatrix w)ᵀ-1)*toMatrix w) := by
  rw [(actual_parseval_gradient beta w).gradient]
  rfl

end General

def sourceW : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,1]
def sourcePoint : Space (Fin 2) (Fin 2) := fromMatrix sourceW
def sourceStep : Space (Fin 2) (Fin 2) := sourcePoint-(1/10 : ℝ) • gradient (objective 1) sourcePoint

theorem actual_source_data :
    errorMatrix sourcePoint=!![1,1;1,0] ∧ objective 1 sourcePoint=3/4 ∧
      toMatrix (gradient (objective 1) sourcePoint)=!![1,2;1,1] := by
  have he : errorMatrix sourcePoint=!![1,1;1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [errorMatrix,sourcePoint,fromMatrix,toMatrix,sourceW,Matrix.mul_apply,
        Matrix.transpose_apply,Fin.sum_univ_two,Matrix.one_apply]
  refine ⟨he,?_,?_⟩
  · rw [objective,he,actual_frobenius_squared]
    norm_num [Fin.sum_univ_two]
  · rw [actual_gradient_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourcePoint,fromMatrix,toMatrix,sourceW,Matrix.mul_apply,Matrix.transpose_apply,
        Fin.sum_univ_two,Matrix.one_apply]

theorem actual_source_gradient_step : toMatrix sourceStep=!![(9/10 : ℝ),4/5;-1/10,9/10] := by
  rw [sourceStep]
  have he : toMatrix (sourcePoint-(1/10 : ℝ) • gradient (objective 1) sourcePoint)=
      toMatrix sourcePoint-(1/10 : ℝ) • toMatrix (gradient (objective 1) sourcePoint) := rfl
  rw [he,actual_source_data.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourcePoint,fromMatrix,toMatrix,sourceW]

theorem actual_source_step_decreases : objective 1 sourceStep=10287/40000 ∧
    objective 1 sourceStep<objective 1 sourcePoint ∧
      |objective 1 sourceStep-(257/1000 : ℝ)|<1/2000 := by
  have he : errorMatrix sourceStep=!![(9/20 : ℝ),63/100;63/100,-9/50] := by
    rw [errorMatrix,actual_source_gradient_step]
    ext i j
    simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_two]
  rw [objective,he,actual_frobenius_squared,actual_source_data.2.1]
  norm_num [Fin.sum_univ_two]

end SafeLearning.CompleteFoundationsParsevalModels
