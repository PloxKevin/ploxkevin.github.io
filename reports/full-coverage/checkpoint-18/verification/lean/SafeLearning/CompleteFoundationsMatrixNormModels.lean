import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsMatrixNormModels

def smallMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,-2;0,3]
def l1Map (A : Matrix (Fin 2) (Fin 2) ℝ) :
    PiLp 1 (fun _ : Fin 2 => ℝ) →L[ℝ] PiLp 1 (fun _ : Fin 2 => ℝ) :=
  (Matrix.toLpLin 1 1 A).toContinuousLinearMap

theorem small_matrix_l1_apply (x : PiLp 1 (fun _ : Fin 2 => ℝ)) :
    l1Map smallMatrix x=WithLp.toLp 1 ![x 0-2*x 1,3*x 1] := by
  ext i
  change (smallMatrix *ᵥ (x : Fin 2 → ℝ)) i=(![x 0-2*x 1,3*x 1] : Fin 2 → ℝ) i
  fin_cases i <;> simp [smallMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 800000 in
theorem small_matrix_l1_norm : ‖l1Map smallMatrix‖=5 := by
  apply le_antisymm
  · apply (l1Map smallMatrix).opNorm_le_bound (by norm_num)
    intro x
    rw [small_matrix_l1_apply]
    simp only [PiLp.norm_eq_of_L1,Fin.sum_univ_two,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Real.norm_eq_abs]
    have hh : |x 0-2*x 1|≤|x 0|+2*|x 1| := by
      simpa [sub_eq_add_neg,abs_neg,abs_mul] using abs_add_le (x 0) (-(2*x 1))
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg (x 0)]
  · let x : PiLp 1 (fun _ : Fin 2 => ℝ) := WithLp.toLp 1 ![0,1]
    have hx : ‖x‖=1 := by norm_num [x,PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
    have hAx : ‖l1Map smallMatrix x‖=5 := by
      rw [small_matrix_l1_apply]
      norm_num [x,PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
    have hb := (l1Map smallMatrix).le_opNorm x
    rw [hx,hAx,mul_one] at hb
    exact hb

theorem small_matrix_l1_attainment :
    (smallMatrix *ᵥ (![0,1] : Fin 2 → ℝ))=(![-2,3] : Fin 2 → ℝ) ∧
    ‖(WithLp.toLp 1 (![0,1] : Fin 2 → ℝ) : PiLp 1 (fun _ : Fin 2 => ℝ))‖=1 ∧
    ‖l1Map smallMatrix (WithLp.toLp 1 (![0,1] : Fin 2 → ℝ))‖=5 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [smallMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  constructor
  · norm_num [PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
  · rw [small_matrix_l1_apply]
    norm_num [PiLp.norm_eq_of_L1,Fin.sum_univ_succ]

theorem two_coordinate_supnorm (a b : ℝ) : ‖(![a,b] : Fin 2 → ℝ)‖=max |a| |b| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr
    intro i
    fin_cases i
    · simpa using le_max_left |a| |b|
    · simpa using le_max_right |a| |b|
  · apply max_le
    · simpa using norm_le_pi_norm (![a,b] : Fin 2 → ℝ) (0 : Fin 2)
    · simpa using norm_le_pi_norm (![a,b] : Fin 2 → ℝ) (1 : Fin 2)

theorem diagonal_two_spectral_norm (a b : ℝ) :
    ‖(Matrix.diagonal ![a,b] : Matrix (Fin 2) (Fin 2) ℝ)‖=max |a| |b| := by
  rw [Matrix.l2_opNorm_diagonal,two_coordinate_supnorm]

def firstStretch : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![3,1/2]
def secondStretch : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1/2,3]

theorem stretch_individual_norms : ‖firstStretch‖=3 ∧ ‖secondStretch‖=3 := by
  norm_num [firstStretch,secondStretch,diagonal_two_spectral_norm,two_coordinate_supnorm]

theorem actual_stretch_product :
    firstStretch*secondStretch=(3/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstStretch,secondStretch,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem stretch_product_norm_and_bound :
    ‖firstStretch*secondStretch‖=3/2 ∧
    ‖firstStretch*secondStretch‖≤‖firstStretch‖*‖secondStretch‖ ∧
    (3/2 : ℝ)<‖firstStretch‖*‖secondStretch‖ := by
  rw [actual_stretch_product]
  simp only [norm_smul,Real.norm_eq_abs,norm_one,abs_of_pos (by norm_num : (0 : ℝ)<3/2),mul_one]
  rw [stretch_individual_norms.1,stretch_individual_norms.2]
  norm_num

theorem stretch_product_every_vector (x : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (firstStretch*secondStretch) x‖=(3/2 : ℝ)*‖x‖ := by
  rw [actual_stretch_product]
  simp [map_smul,norm_smul]

theorem individual_stretch_directions :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) firstStretch
      (WithLp.toLp 2 (![1,0] : Fin 2 → ℝ))=3 • WithLp.toLp 2 (![1,0] : Fin 2 → ℝ) ∧
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) secondStretch
      (WithLp.toLp 2 (![0,1] : Fin 2 → ℝ))=3 • WithLp.toLp 2 (![0,1] : Fin 2 → ℝ) ∧
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) firstStretch
      (WithLp.toLp 2 (![0,1] : Fin 2 → ℝ))=(1/2 : ℝ) • WithLp.toLp 2 (![0,1] : Fin 2 → ℝ) := by
  constructor
  · rw [Matrix.toEuclideanCLM_toLp]
    ext i
    fin_cases i <;> simp [firstStretch,Matrix.mulVec_diagonal]
  constructor
  · rw [Matrix.toEuclideanCLM_toLp]
    ext i
    fin_cases i <;> simp [secondStretch,Matrix.mulVec_diagonal]
  · rw [Matrix.toEuclideanCLM_toLp]
    ext i
    fin_cases i <;> simp [firstStretch,Matrix.mulVec_diagonal]

def tailMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1/2,1/4]
def partialSum (T : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ k ∈ Finset.range T,tailMatrix^k

theorem actual_tail_inverse :
    (1-tailMatrix)⁻¹=(Matrix.diagonal ![2,4/3] : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tailMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_tail_matrix (T : ℕ) :
    (1-tailMatrix)⁻¹-partialSum T=
      (Matrix.diagonal ![2*(1/2 : ℝ)^T,(4/3)*(1/4 : ℝ)^T] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h₂ : (∑ k ∈ Finset.range T,((2 : ℝ)^k)⁻¹)=((2 : ℝ)^T)⁻¹/((2 : ℝ)⁻¹-1)-1/((2 : ℝ)⁻¹-1) := by
    simpa only [inv_pow,sub_div] using geom_sum_eq (by norm_num : (2 : ℝ)⁻¹≠1) T
  have h₄ : (∑ k ∈ Finset.range T,((4 : ℝ)^k)⁻¹)=((4 : ℝ)^T)⁻¹/((4 : ℝ)⁻¹-1)-1/((4 : ℝ)⁻¹-1) := by
    simpa only [inv_pow,sub_div] using geom_sum_eq (by norm_num : (4 : ℝ)⁻¹≠1) T
  rw [actual_tail_inverse]
  ext i j
  simp only [Matrix.sub_apply,partialSum,Matrix.sum_apply,tailMatrix,Matrix.diagonal_pow,Pi.pow_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal] <;>
    first | rw [h₂] | rw [h₄]
  all_goals norm_num <;> ring

theorem first_tail_coordinate_dominates (T : ℕ) :
    (4/3 : ℝ)*(1/4 : ℝ)^T≤2*(1/2 : ℝ)^T := by
  have hp : (1/4 : ℝ)^T≤(1/2 : ℝ)^T := pow_le_pow_left₀ (by norm_num) (by norm_num) T
  have hn := pow_nonneg (by norm_num : (0 : ℝ)≤1/2) T
  nlinarith

theorem exact_spectral_tail_norm (T : ℕ) :
    ‖(1-tailMatrix)⁻¹-partialSum T‖=2*(1/2 : ℝ)^T := by
  rw [actual_tail_matrix,diagonal_two_spectral_norm,
    abs_of_nonneg (by positivity : (0 : ℝ)≤2*(1/2 : ℝ)^T),
    abs_of_nonneg (by positivity : (0 : ℝ)≤(4/3)*(1/4 : ℝ)^T),
    max_eq_left (first_tail_coordinate_dominates T)]

theorem spectral_tail_integer_power (T : ℕ) :
    ‖(1-tailMatrix)⁻¹-partialSum T‖=(2 : ℝ)^(1-(T : ℤ)) := by
  rw [exact_spectral_tail_norm,zpow_sub₀ (by norm_num),zpow_one,zpow_natCast]
  simp [one_div,inv_pow,div_eq_mul_inv]

theorem exact_tail_threshold (T : ℕ) :
    ‖(1-tailMatrix)⁻¹-partialSum T‖≤1/100 ↔ 8≤T := by
  rw [exact_spectral_tail_norm]
  have hmono : Antitone (fun n : ℕ => (1/2 : ℝ)^n) := pow_right_anti₀ (by norm_num) (by norm_num)
  constructor
  · intro h
    by_contra hnot
    have hb := hmono (show T≤7 by omega)
    norm_num at hb
    linarith
  · intro h
    have hb := hmono h
    norm_num at hb
    linarith

theorem tail_source_numbers_and_neumann_hypothesis :
    ‖tailMatrix‖=1/2 ∧ ‖tailMatrix‖<1 ∧
    ‖(1-tailMatrix)⁻¹-partialSum 7‖=15625/1000000 ∧
    ‖(1-tailMatrix)⁻¹-partialSum 8‖=78125/10000000 := by
  simp only [exact_spectral_tail_norm]
  norm_num [tailMatrix,diagonal_two_spectral_norm,two_coordinate_supnorm]

theorem small_matrix_entry_sums :
    (∑ i : Fin 2,|smallMatrix i 0|)=1 ∧ (∑ i : Fin 2,|smallMatrix i 1|)=5 ∧
    (∑ j : Fin 2,|smallMatrix 0 j|)=3 ∧ (∑ j : Fin 2,|smallMatrix 1 j|)=3 ∧
    (∑ i : Fin 2,∑ j : Fin 2,(smallMatrix i j)^2)=14 := by
  norm_num [smallMatrix,Fin.sum_univ_succ]

theorem source_tail_ratio (T : ℕ) :
    (2*(1/2 : ℝ)^T)/((4/3)*(1/4 : ℝ)^T)=(3/2 : ℝ)*2^T ∧
    1≤(3/2 : ℝ)*2^T := by
  constructor
  · rw [mul_div_mul_comm,← div_pow]
    norm_num
  · have hp : (1 : ℝ)≤2^T := one_le_pow₀ (by norm_num)
    nlinarith

theorem first_basis_attains_tail (T : ℕ) :
    ‖(WithLp.toLp 2 (![1,0] : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2))‖=1 ∧
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) ((1-tailMatrix)⁻¹-partialSum T)
      (WithLp.toLp 2 (![1,0] : Fin 2 → ℝ))‖=‖(1-tailMatrix)⁻¹-partialSum T‖ := by
  constructor
  · norm_num [EuclideanSpace.norm_eq,Fin.sum_univ_succ]
  · rw [exact_spectral_tail_norm,actual_tail_matrix,Matrix.toEuclideanCLM_toLp]
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_succ,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ)≤2*(1/2 : ℝ)^T)]

theorem eight_term_indices (k : ℕ) : k ∈ Finset.range 8 ↔ k≤7 := by
  simp only [Finset.mem_range]
  omega

section InfinityNorm
open scoped Matrix.Norms.Operator
theorem small_matrix_infinity_norm : ‖smallMatrix‖=3 := by
  norm_num [Matrix.linfty_opNorm_def,smallMatrix,Fin.sum_univ_succ,Finset.univ_fin2]
end InfinityNorm

section FrobeniusNorm
open scoped Matrix.Norms.Frobenius
theorem small_matrix_frobenius_norm : ‖smallMatrix‖=Real.sqrt 14 := by
  rw [Matrix.frobenius_norm_def]
  norm_num [smallMatrix,Fin.sum_univ_succ,Real.norm_eq_abs,Real.sqrt_eq_rpow]
end FrobeniusNorm

end SafeLearning.CompleteFoundationsMatrixNormModels
