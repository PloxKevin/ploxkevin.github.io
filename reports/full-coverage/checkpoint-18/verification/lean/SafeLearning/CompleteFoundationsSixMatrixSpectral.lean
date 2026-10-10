import SafeLearning.CompleteFoundationsSixMatrixNorms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix Set
open scoped BigOperators ENNReal
namespace SafeLearning.CompleteFoundationsSixMatrixSpectral
open CompleteFoundationsSixMatrixNorms

def twoMap : E →L[ℝ] E := sourceB.toEuclideanLin.toContinuousLinearMap
def upperRoot : ℝ := 15+5*Real.sqrt 5
def lowerRoot : ℝ := 15-5*Real.sqrt 5

theorem actual_two_map_coordinates (x : E) :
    twoMap x=WithLp.toLp 2 ![x 0-2*x 1,3*x 0+4*x 1] := by
  ext i
  change (sourceB *ᵥ (x : Fin 2 → ℝ)) i=_
  rw [actual_source_matrix_action]

theorem actual_two_map_energy (x : E) :
    ‖twoMap x‖^2=10*(x 0)^2+20*x 0*x 1+20*(x 1)^2 := by
  rw [actual_two_coordinate_euclidean_norm_squared,actual_two_map_coordinates]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem actual_roots_positive_and_relations :
    0<lowerRoot ∧ lowerRoot<upperRoot ∧ upperRoot<30 ∧ upperRoot+lowerRoot=30 ∧
    upperRoot*lowerRoot=100 := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg 5
  dsimp [upperRoot,lowerRoot]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · ring
  · nlinarith

theorem actual_upper_energy_bound (x : E) : ‖twoMap x‖^2≤upperRoot*‖x‖^2 := by
  rw [actual_two_map_energy,actual_two_coordinate_euclidean_norm_squared]
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hp : 0<5*(1+Real.sqrt 5) := by positivity
  have hi : 5*(1+Real.sqrt 5)*
      (upperRoot*((x 0)^2+(x 1)^2)-(10*(x 0)^2+20*x 0*x 1+20*(x 1)^2))=
      (5*(1+Real.sqrt 5)*x 0-10*x 1)^2 := by
    dsimp [upperRoot]
    linear_combination 25*(x 1)^2*hs
  have hn := sq_nonneg (5*(1+Real.sqrt 5)*x 0-10*x 1)
  nlinarith

theorem actual_nonzero_upper_eigenvector_energy :
    let x : E := WithLp.toLp 2 ![2,1+Real.sqrt 5]
    x≠0 ∧ ‖twoMap x‖^2=upperRoot*‖x‖^2 := by
  dsimp
  constructor
  · intro h
    have hc := congrArg (fun x : E => x 0) h
    norm_num at hc
  · rw [actual_two_map_energy,actual_two_coordinate_euclidean_norm_squared]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
    dsimp [upperRoot]
    linear_combination -5*(Real.sqrt 5+1)*hs

theorem actual_euclidean_operator_norm : ‖twoMap‖=Real.sqrt upperRoot := by
  have hr := actual_roots_positive_and_relations
  have hs : (Real.sqrt upperRoot)^2=upperRoot := Real.sq_sqrt (le_of_lt (lt_trans hr.1 hr.2.1))
  apply le_antisymm
  · apply twoMap.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    apply le_of_sq_le_sq _ (by positivity)
    have he := actual_upper_energy_bound x
    nlinarith
  · let x : E := WithLp.toLp 2 ![2,1+Real.sqrt 5]
    have hx : 0<‖x‖ := norm_pos_iff.mpr actual_nonzero_upper_eigenvector_energy.1
    have he : ‖twoMap x‖^2=upperRoot*‖x‖^2 := actual_nonzero_upper_eigenvector_energy.2
    have hb := twoMap.le_opNorm x
    have hp := norm_nonneg twoMap
    have ht := norm_nonneg (twoMap x)
    by_contra h
    have hlt : ‖twoMap‖<Real.sqrt upperRoot := lt_of_not_ge h
    have hh : ‖twoMap‖*‖x‖<Real.sqrt upperRoot*‖x‖ := mul_lt_mul_of_pos_right hlt hx
    have heq : ‖twoMap x‖=Real.sqrt upperRoot*‖x‖ := by nlinarith
    linarith

theorem actual_adjoint_gram :
    twoMap.toLinearMap.adjoint ∘ₗ twoMap.toLinearMap=
      (sourceB.transpose*sourceB).toEuclideanLin := by
  change sourceB.toEuclideanLin.adjoint ∘ₗ sourceB.toEuclideanLin=_
  rw [←Matrix.toEuclideanLin_conjTranspose_eq_adjoint,←Matrix.toLpLin_mul_same]
  simp

theorem actual_singular_value_sum_squares_and_product :
    sourceB.toEuclideanLin.singularValues 0^2+sourceB.toEuclideanLin.singularValues 1^2=30 ∧
    sourceB.toEuclideanLin.singularValues 0*sourceB.toEuclideanLin.singularValues 1=10 := by
  let T := sourceB.toEuclideanLin
  have hd : Module.finrank ℝ E=2 := by simp [E]
  constructor
  · have ht := T.isSymmetric_adjoint_comp_self.trace_eq_sum_eigenvalues hd
    simp only [Fin.sum_univ_two] at ht
    change (T.adjoint ∘ₗ T).trace ℝ E=T.isSymmetric_adjoint_comp_self.eigenvalues hd 0+T.isSymmetric_adjoint_comp_self.eigenvalues hd 1 at ht
    rw [←T.sq_singularValues_fin hd (0 : Fin 2),←T.sq_singularValues_fin hd (1 : Fin 2)] at ht
    have hg : T.adjoint ∘ₗ T=(sourceB.transpose*sourceB).toEuclideanLin := actual_adjoint_gram
    have htrace : (T.adjoint ∘ₗ T).trace ℝ E=30 := by
      rw [hg]
      norm_num [Matrix.toLpLin_eq_toLin,Matrix.trace,actual_source_entry_sums_gram_and_determinant.2.2.2.2.2.1,Fin.sum_univ_two]
    rw [htrace] at ht
    simpa [T] using ht.symm
  · have hn := T.normDet_eq_prod_singularValues
    rw [T.normDet_eq_abs_det,LinearMap.det_toLpLin] at hn
    simpa [T,actual_source_entry_sums_gram_and_determinant.2.2.2.2.2.2,Finset.prod_range_succ] using hn.symm

theorem actual_first_and_second_singular_values :
    sourceB.toEuclideanLin.singularValues 0=Real.sqrt upperRoot ∧
    sourceB.toEuclideanLin.singularValues 1=Real.sqrt lowerRoot := by
  let a := sourceB.toEuclideanLin.singularValues 0
  let b := sourceB.toEuclideanLin.singularValues 1
  have he := actual_singular_value_sum_squares_and_product
  have ha : 0≤a := sourceB.toEuclideanLin.singularValues_nonneg 0
  have hb : 0≤b := sourceB.toEuclideanLin.singularValues_nonneg 1
  have hab : b≤a := sourceB.toEuclideanLin.singularValues_antitone (by omega : 0≤1)
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hd : a^2-b^2=10*Real.sqrt 5 := by
    have hq : (a^2-b^2)^2=(10*Real.sqrt 5)^2 := by
      nlinarith [sq_nonneg (a*b-10)]
    have hz : 0≤a^2-b^2 := by nlinarith
    nlinarith [Real.sqrt_nonneg 5]
  have ha2 : a^2=upperRoot := by dsimp [upperRoot];linarith
  have hb2 : b^2=lowerRoot := by dsimp [lowerRoot];linarith
  have hr := actual_roots_positive_and_relations
  constructor
  · have hr2 := Real.sq_sqrt (le_of_lt (lt_trans hr.1 hr.2.1))
    nlinarith [Real.sqrt_nonneg upperRoot]
  · have hr2 := Real.sq_sqrt (le_of_lt hr.1)
    nlinarith [Real.sqrt_nonneg lowerRoot]

theorem actual_spectral_norm_below_frobenius_and_row_column_bound :
    ‖twoMap‖≤Real.sqrt 30 ∧ ‖twoMap‖≤Real.sqrt (6*7) ∧
    Real.sqrt 10≤‖twoMap‖ := by
  rw [actual_euclidean_operator_norm]
  have hr := actual_roots_positive_and_relations
  dsimp [upperRoot] at *
  constructor
  · apply Real.sqrt_le_sqrt;linarith
  constructor
  · apply Real.sqrt_le_sqrt;linarith
  · apply Real.sqrt_le_sqrt
    nlinarith [Real.sqrt_nonneg 5]

end SafeLearning.CompleteFoundationsSixMatrixSpectral
