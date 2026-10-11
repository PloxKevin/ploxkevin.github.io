import SafeLearning.CompleteFoundationsParsevalModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

namespace SafeLearning.CompleteFoundationsParsevalTrace
open CompleteFoundationsParsevalModels

variable {M N : Type*} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem actual_trace_pair_coordinates (X Y : Matrix M N ℝ) :
    (Xᵀ*Y).trace=∑ i : M,∑ j : N,X i j*Y i j := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_comm

theorem actual_trace_pair_is_hilbert_inner (X Y : Matrix M N ℝ) :
    (Xᵀ*Y).trace=inner ℝ (fromMatrix X) (fromMatrix Y) := by
  rw [actual_trace_pair_coordinates,actual_inner_coordinates]
  rfl

theorem actual_symmetric_source_trace_equalities
    (S : Matrix M M ℝ) (hS : Sᵀ=S) (W H : Matrix M N ℝ) :
    (S*(H*Wᵀ)).trace=(Wᵀ*S*H).trace ∧
      (S*(W*Hᵀ)).trace=(Wᵀ*S*H).trace := by
  constructor
  · simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle' S H Wᵀ
  · calc
      (S*(W*Hᵀ)).trace=((S*(W*Hᵀ))ᵀ).trace := (Matrix.trace_transpose _).symm
      _ = (H*(Wᵀ*S)).trace := by rw [Matrix.transpose_mul,Matrix.transpose_mul,
          Matrix.transpose_transpose,hS,Matrix.mul_assoc]
      _ = (Wᵀ*S*H).trace := Matrix.trace_mul_comm _ _

theorem actual_symmetric_trace_pair_is_inner
    (S : Matrix M M ℝ) (hS : Sᵀ=S) (W H : Matrix M N ℝ) :
    (Wᵀ*S*H).trace=inner ℝ (fromMatrix (S*W)) (fromMatrix H) := by
  rw [← actual_trace_pair_is_hilbert_inner,Matrix.transpose_mul,hS]

theorem actual_parseval_differential_is_source_inner (beta : ℝ) (w h : Space M N) :
    beta*((toMatrix w)ᵀ*errorMatrix w*toMatrix h).trace=
      inner ℝ (sourceGradient beta w) h := by
  rw [actual_symmetric_trace_pair_is_inner (errorMatrix w)
    (actual_error_is_symmetric w),actual_inner_coordinates,actual_inner_coordinates]
  simp only [sourceGradient,fromMatrix,toMatrix,Matrix.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem actual_error_along_matrix_direction (w h : Space M N) (i j : M) :
    HasDerivAt (fun t : ℝ => errorMatrix (w+t • h) i j)
      ((toMatrix h*(toMatrix w)ᵀ+toMatrix w*(toMatrix h)ᵀ) i j) 0 := by
  have hp : HasDerivAt (fun t : ℝ => w+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add w
  have he : HasFDerivAt (fun v : Space M N => errorEntry v i j)
      (errorDerivative w i j) (w+(0 : ℝ) • h) := by
    simpa using actual_entry_differential w i j
  have hd := he.comp_hasDerivAt (0 : ℝ) hp
  convert hd using 1
  · exact funext (fun t => actual_error_entries (w+t • h) i j)
  · simp [errorDerivative,entry,PiLp.proj,PiLp.projₗ,Matrix.add_apply,
      Matrix.mul_apply,Matrix.transpose_apply,toMatrix]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem actual_error_matrix_directional_differential (w h : Space M N) :
    HasDerivAt (fun t : ℝ => fromMatrix (errorMatrix (w+t • h)))
      (fromMatrix (toMatrix h*(toMatrix w)ᵀ+toMatrix w*(toMatrix h)ᵀ)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => fun ij : M×M => errorMatrix (w+t • h) ij.1 ij.2)
      (fun ij : M×M => (toMatrix h*(toMatrix w)ᵀ+toMatrix w*(toMatrix h)ᵀ) ij.1 ij.2) 0 :=
    hasDerivAt_pi.mpr (fun ij => actual_error_along_matrix_direction w h ij.1 ij.2)
  have hd := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (fun ij : M×M => errorMatrix (w+(0 : ℝ) • h) ij.1 ij.2)).comp_hasDerivAt (0 : ℝ) hc
  convert hd using 1
  · rfl
  · rfl

theorem actual_parseval_directional_trace_derivative (beta : ℝ) (w h : Space M N) :
    HasDerivAt (fun t : ℝ => objective beta (w+t • h))
      (beta*( (toMatrix w)ᵀ*errorMatrix w*toMatrix h).trace) 0 := by
  have hp : HasDerivAt (fun t : ℝ => w+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add w
  have hg : HasGradientAt (objective beta) (sourceGradient beta w) (w+(0 : ℝ) • h) := by
    simpa using actual_parseval_gradient beta w
  have hd := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp
  convert hd using 1
  · rfl
  · rw [InnerProductSpace.toDual_apply_apply]
    exact actual_parseval_differential_is_source_inner beta w h

theorem actual_squared_frobenius_directional_trace_derivative (w h : Space M N) :
    HasDerivAt (fun t : ℝ => ‖errorMatrix (w+t • h)‖^2)
      (2*(errorMatrix w*(toMatrix h*(toMatrix w)ᵀ+toMatrix w*(toMatrix h)ᵀ)).trace) 0 := by
  have hd := (actual_parseval_directional_trace_derivative 1 w h).const_mul 4
  have ht := actual_symmetric_source_trace_equalities
    (errorMatrix w) (actual_error_is_symmetric w) (toMatrix w) (toMatrix h)
  convert hd using 1
  · ext t
    simp [objective]
  · rw [Matrix.mul_add,Matrix.trace_add,ht.1,ht.2]
    ring

theorem actual_parseval_finite_differences_converge (beta : ℝ) (w h : Space M N) :
    Tendsto (fun t : ℝ => (objective beta (w+t • h)-objective beta w)/t)
      (𝓝[≠] 0) (𝓝 (beta*((toMatrix w)ᵀ*errorMatrix w*toMatrix h).trace)) := by
  simpa [div_eq_mul_inv,mul_comm] using
    (actual_parseval_directional_trace_derivative beta w h).tendsto_slope_zero

theorem actual_source_gram_matrix :
    toMatrix sourcePoint*(toMatrix sourcePoint)ᵀ=!![2,1;1,1] := by
  have he := actual_source_data.1
  change toMatrix sourcePoint*(toMatrix sourcePoint)ᵀ-1=!![1,1;1,0] at he
  have ha := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X+1) he
  simp only [sub_add_cancel] at ha
  calc
    _ = !![1,1;1,0]+1 := ha
    _ = _ := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

end SafeLearning.CompleteFoundationsParsevalTrace
