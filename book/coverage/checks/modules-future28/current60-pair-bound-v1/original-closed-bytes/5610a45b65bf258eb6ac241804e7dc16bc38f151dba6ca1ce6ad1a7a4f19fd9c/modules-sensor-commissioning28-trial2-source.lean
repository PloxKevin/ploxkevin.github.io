import SafeLearning.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteModulesSensorCommissioning28

def normalizedCorrection (x y : ℝ) : ℝ := max (x+2*y) 0+max (x-2*y) 0
def normalizedNetwork (x y : ℝ) : ℝ := normalizedCorrection x y/2
def certificate : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-4/3,0,1/3,1/3;0,-4/3,2/3,-2/3;
      1/3,2/3,-5/12,1/4;1/3,-2/3,1/4,-5/12]
def rotation : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0;0,0,1,0;0,1/Real.sqrt 2,0,1/Real.sqrt 2;
    0,1/Real.sqrt 2,0,-1/Real.sqrt 2]
def rotatedBlocks : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-4/3,Real.sqrt 2/3,0,0;Real.sqrt 2/3,-1/6,0,0;
    0,0,-4/3,2*Real.sqrt 2/3;0,0,2*Real.sqrt 2/3,-2/3]
def eigenBasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-4,0,1,0;0,-2,0,1;1,1,2,1;1,-1,2,-1]
def inverseEigenBasis : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1/18,1/6,1/9,1/3]*eigenBasis.transpose
def commissioningBound : ℝ := 2*Real.sqrt (4/3)*(1/25)
def certifiedSlack : ℝ := 1/10-commissioningBound

private theorem relu_incremental_sector (x y : ℝ) :
    0 ≤ (max x 0-max y 0)*((x-y)-(max x 0-max y 0)) := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [max_eq_left hx,max_eq_left hy];ring_nf;exact le_rfl
  · rw [max_eq_left hx,max_eq_right (le_of_not_ge hy)];nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_left hy];nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_right (le_of_not_ge hy)];norm_num

theorem actual_certificate_quadratic_sum_of_squares (v : Fin 4 → ℝ) :
    v ⬝ᵥ (certificate *ᵥ v)=
      -(4/3)*(v 0-(v 2+v 3)/4)^2-(4/3)*(v 1-(v 2-v 3)/2)^2 := by
  simp [certificate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_sdp_certificate_is_negative_semidefinite : (-certificate).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [certificate,Matrix.conjTranspose_apply]
  · intro v
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
    rw [actual_certificate_quadratic_sum_of_squares]
    nlinarith [sq_nonneg (v 0-(v 2+v 3)/4),sq_nonneg (v 1-(v 2-v 3)/2)]

theorem actual_sdp_certificate_is_the_source_incremental_lmi (dx dy dz1 dz2 : ℝ) :
    (![dx,dy,dz1,dz2]:Fin 4 → ℝ) ⬝ᵥ
        (certificate *ᵥ (![dx,dy,dz1,dz2]:Fin 4 → ℝ))=
      ((dz1+dz2)/2)^2-(4/3)*(dx^2+dy^2)+
        (2/3)*(dz1*((dx+2*dy)-dz1)+dz2*((dx-2*dy)-dz2)) := by
  rw [actual_certificate_quadratic_sum_of_squares]
  norm_num
  ring

theorem actual_network_sdp_squared_gain (x y xb yb : ℝ) :
    (normalizedNetwork x y-normalizedNetwork xb yb)^2 ≤
      (4/3)*((x-xb)^2+(y-yb)^2) := by
  let dz1:=max (x+2*y) 0-max (xb+2*yb) 0
  let dz2:=max (x-2*y) 0-max (xb-2*yb) 0
  have h1:=relu_incremental_sector (x+2*y) (xb+2*yb)
  have h2:=relu_incremental_sector (x-2*y) (xb-2*yb)
  have hm:=actual_sdp_certificate_is_negative_semidefinite.dotProduct_mulVec_nonneg
    (![x-xb,y-yb,dz1,dz2]:Fin 4 → ℝ)
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hm
  rw [actual_sdp_certificate_is_the_source_incremental_lmi] at hm
  have he : normalizedNetwork x y-normalizedNetwork xb yb=(dz1+dz2)/2 := by
    dsimp [normalizedNetwork,normalizedCorrection,dz1,dz2]
    ring
  rw [he]
  dsimp [dz1,dz2] at hm
  nlinarith

theorem actual_physical_sdp_bound (x y xb yb r : ℝ) (hr : 0 ≤ r)
    (hinput : (x-xb)^2+(y-yb)^2 ≤ r^2) :
    |normalizedCorrection x y-normalizedCorrection xb yb| ≤ 2*Real.sqrt (4/3)*r := by
  have hg:=actual_network_sdp_squared_gain x y xb yb
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
  have he : normalizedCorrection x y-normalizedCorrection xb yb=
      2*(normalizedNetwork x y-normalizedNetwork xb yb) := by dsimp [normalizedNetwork];ring
  have hn : 0 ≤ 2*Real.sqrt (4/3)*r := by positivity
  apply abs_le_of_sq_le_sq _ hn
  rw [he]
  nlinarith

theorem actual_hidden_sum_difference_rotation_is_orthogonal :
    rotation.transpose*rotation=1 ∧ rotation*rotation.transpose=1 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hr : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] <;>
    field_simp [hr] <;> nlinarith

theorem actual_source_certificate_separates_into_the_printed_two_blocks :
    rotation.transpose*certificate*rotation=rotatedBlocks := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hr : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation,certificate,rotatedBlocks,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> field_simp [hr] <;> nlinarith

theorem actual_printed_blocks_have_zero_determinants_and_negative_traces :
    (Matrix.det (!![-4/3,Real.sqrt 2/3;Real.sqrt 2/3,-1/6]:Matrix (Fin 2) (Fin 2) ℝ)=0) ∧
    (Matrix.det (!![-4/3,2*Real.sqrt 2/3;2*Real.sqrt 2/3,-2/3]:Matrix (Fin 2) (Fin 2) ℝ)=0) ∧
    (Matrix.trace (!![-4/3,Real.sqrt 2/3;Real.sqrt 2/3,-1/6]:Matrix (Fin 2) (Fin 2) ℝ)= -3/2) ∧
    (Matrix.trace (!![-4/3,2*Real.sqrt 2/3;2*Real.sqrt 2/3,-2/3]:Matrix (Fin 2) (Fin 2) ℝ)= -2) := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  norm_num [Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_succ]
  constructor <;> nlinarith

theorem actual_eigenbasis_has_the_printed_two_sided_inverse :
    eigenBasis*inverseEigenBasis=1 ∧ inverseEigenBasis*eigenBasis=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [eigenBasis,inverseEigenBasis,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal,Fin.sum_univ_succ]

theorem actual_source_certificate_diagonalizes_with_the_printed_eigenvalues :
    inverseEigenBasis*certificate*eigenBasis=Matrix.diagonal ![-3/2,-2,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [eigenBasis,inverseEigenBasis,certificate,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal,Fin.sum_univ_succ]

theorem actual_source_certificate_characteristic_polynomial :
    certificate.charpoly=Polynomial.X^2*(Polynomial.X+Polynomial.C (3/2))*(Polynomial.X+2) := by
  have h : (inverseEigenBasis*certificate*eigenBasis).charpoly=certificate.charpoly := by
    rw [Matrix.charpoly_mul_comm,←Matrix.mul_assoc,
      actual_eigenbasis_has_the_printed_two_sided_inverse.1,Matrix.one_mul]
  rw [actual_source_certificate_diagonalizes_with_the_printed_eigenvalues,
    Matrix.charpoly_diagonal] at h
  rw [←h]
  simp [Fin.prod_univ_succ]
  ring

theorem actual_source_certificate_has_exactly_the_printed_characteristic_roots (lambda : ℝ) :
    certificate.charpoly.IsRoot lambda ↔ lambda= -3/2 ∨ lambda= -2 ∨ lambda=0 := by
  rw [Polynomial.IsRoot,actual_source_certificate_characteristic_polynomial]
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_ofNat]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h|h
    · rcases mul_eq_zero.mp h with h|h
      · right;right;exact pow_eq_zero h
      · left;linarith
    · right;left;linarith
  · rintro (rfl|rfl|rfl) <;> norm_num

theorem actual_commissioning_bound_square_positive_and_approval :
    commissioningBound^2=16/1875 ∧ 0<commissioningBound ∧ commissioningBound<1/10 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
  have he : commissioningBound^2=16/1875 := by
    dsimp [commissioningBound];rw [mul_pow,mul_pow,hs];norm_num
  refine ⟨he,?_,?_⟩
  · dsimp [commissioningBound];positivity
  · nlinarith [sq_nonneg (commissioningBound+1/10)]

theorem actual_commissioning_network_change_is_certified (x y xb yb : ℝ)
    (hinput : (x-xb)^2+(y-yb)^2 ≤ (1/25)^2) :
    |normalizedCorrection x y-normalizedCorrection xb yb| ≤ commissioningBound ∧
    |normalizedCorrection x y-normalizedCorrection xb yb| < 1/10 := by
  have hb:=actual_physical_sdp_bound x y xb yb (1/25) (by norm_num) hinput
  exact ⟨hb,hb.trans_lt actual_commissioning_bound_square_positive_and_approval.2.2⟩

theorem actual_commissioning_bound_and_slack_round_to_the_printed_decimals :
    |commissioningBound-92376/10^6|<1/(2*10^6) ∧
    |certifiedSlack-7624/10^6|<1/(2*10^6) ∧ 0<certifiedSlack := by
  have hs:=actual_commissioning_bound_square_positive_and_approval
  have hb : |commissioningBound-92376/10^6|<1/(2*10^6) := by
    rw [abs_lt];constructor <;> nlinarith [sq_nonneg (commissioningBound-92376/10^6)]
  refine ⟨hb,?_,?_⟩
  · dsimp [certifiedSlack]
    convert hb using 1
    rw [show (1/10:ℝ)-commissioningBound-7624/10^6= -(commissioningBound-92376/10^6) by ring,abs_neg]
  · dsimp [certifiedSlack];linarith [hs.2.2]

end SafeLearning.CompleteModulesSensorCommissioning28
