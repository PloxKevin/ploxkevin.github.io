import SafeLearning.CompleteFoundationsQuadraticForms
import SafeLearning.CompleteFoundationsRayleighQuotientWhole30
import SafeLearning.CompleteFoundationsSymmetricHermitianSpectral30

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsPlanarQuadraticLevelSets32
open CompleteFoundationsQuadraticForms
open CompleteFoundationsRayleighQuotientWhole30
open CompleteFoundationsSymmetricHermitianSpectral30

def positiveEntryExample : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,1]
def singularPSDExample : Matrix (Fin 2) (Fin 2) ℝ := !![1,-1;-1,1]
def oneLevel (P : Matrix (Fin 2) (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  {x | realQuadratic P x=1}

private theorem positive_weight_scaled_square (r t : ℝ) (hr : 0<r) :
    r*t^2=(t/(1/Real.sqrt r))^2 := by
  simp only [div_div_eq_mul_div,div_one,mul_pow,Real.sq_sqrt hr.le]
  ring

private theorem positive_weight_one_level (r t : ℝ) (hr : 0<r) :
    r*t^2=1 ↔ t=1/Real.sqrt r ∨ t= -(1/Real.sqrt r) := by
  have hs : (1/Real.sqrt r : ℝ)^2=1/r := by
    rw [div_pow,one_pow,Real.sq_sqrt hr.le]
  have he : r*(1/Real.sqrt r)^2=1 := by
    rw [hs];field_simp
  constructor
  · intro h
    apply eq_or_eq_neg_of_sq_eq_sq
    exact mul_left_cancel₀ hr.ne' (h.trans he.symm)
  · rintro (rfl|rfl)
    · exact he
    · simpa only [neg_sq] using he

private theorem plane_energy_normal_form (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : P.IsHermitian) (x : Fin 2 → ℝ) :
    realQuadratic P x=hP.eigenvalues 0*(actualCoordinates P hP x 0)^2+
      hP.eigenvalues 1*(actualCoordinates P hP x 1)^2 := by
  simpa only [realQuadratic,Fin.sum_univ_two] using
    actual_quadratic_form_is_eigenvalue_weighted_coordinate_energy P hP x

theorem actual_positive_entry_example_is_indefinite :
    realQuadratic positiveEntryExample (![1,-1] : Fin 2 → ℝ)= -2 ∧
    realQuadratic positiveEntryExample (![1,1] : Fin 2 → ℝ)=6 ∧
    (∀ i j : Fin 2, 0<positiveEntryExample i j) ∧
    (¬positiveEntryExample.PosSemidef ∧ ¬(-positiveEntryExample).PosSemidef) := by
  have h1 : realQuadratic positiveEntryExample (![1,-1] : Fin 2 → ℝ)= -2 := by
    norm_num [realQuadratic,positiveEntryExample,mulVec,dotProduct,Fin.sum_univ_two]
  have h2 : realQuadratic positiveEntryExample (![1,1] : Fin 2 → ℝ)=6 := by
    norm_num [realQuadratic,positiveEntryExample,mulVec,dotProduct,Fin.sum_univ_two]
  refine ⟨h1,h2,?_,?_⟩
  · intro i j;fin_cases i <;> fin_cases j <;> norm_num [positiveEntryExample]
  apply (real_indefinite_iff_both_signs positiveEntryExample (by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [positiveEntryExample])).mpr
  exact ⟨⟨![1,-1],by rw [h1];norm_num⟩,⟨![1,1],by rw [h2];norm_num⟩⟩

theorem actual_singular_PSD_example_has_the_printed_form_and_two_parallel_lines :
    singularPSDExample.PosSemidef ∧ singularPSDExample.det=0 ∧ singularPSDExample≠0 ∧
    ∀ x : Fin 2 → ℝ, realQuadratic singularPSDExample x=(x 0-x 1)^2 ∧
      (x∈oneLevel singularPSDExample ↔ x 0-x 1=1 ∨ x 0-x 1= -1) := by
  have hf (x : Fin 2 → ℝ) : realQuadratic singularPSDExample x=(x 0-x 1)^2 := by
    simp [realQuadratic,singularPSDExample,mulVec,dotProduct,Fin.sum_univ_two];ring
  refine ⟨?_,by norm_num [singularPSDExample,Matrix.det_fin_two],?_,?_⟩
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j;fin_cases i <;> fin_cases j <;> simp [singularPSDExample,Matrix.conjTranspose_apply]
    · intro x
      change 0≤realQuadratic singularPSDExample x
      rw [hf];exact sq_nonneg _
  · intro h
    have he:=congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [singularPSDExample] at he
  · intro x
    refine ⟨hf x,?_⟩
    change realQuadratic singularPSDExample x=1 ↔ _
    rw [hf]
    constructor
    · intro h
      have hz : (x 0-x 1-1)*(x 0-x 1+1)=0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz|hz
      · left;linarith
      · right;linarith
    · rintro (h|h) <;> rw [h] <;> norm_num

theorem actual_spectral_coordinate_change_is_orthogonal_invertible_and_norm_preserving
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.IsHermitian) :
    let Q:=actualEigenvectorMatrix P hP
    Q.transpose*Q=1 ∧ Q*Q.transpose=1 ∧
      ∀ x : Fin 2 → ℝ, actualCoordinates P hP x=Q.transpose *ᵥ x ∧
      Q *ᵥ actualCoordinates P hP x=x ∧
      ‖WithLp.toLp 2 (actualCoordinates P hP x)‖=‖WithLp.toLp 2 x‖ := by
  dsimp
  have hl:= (actual_Hermitian_eigenvector_matrix_is_unitary P hP).1
  have hr:= (actual_Hermitian_eigenvector_matrix_is_unitary P hP).2
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hl hr
  refine ⟨hl,hr,?_⟩
  intro x
  have hc : actualCoordinates P hP x=(actualEigenvectorMatrix P hP).transpose *ᵥ x :=
    actual_spectral_coordinates_are_transpose_times_vector P hP x
  refine ⟨hc,?_,actual_spectral_coordinates_preserve_the_Euclidean_norm P hP x⟩
  rw [hc,Matrix.mulVec_mulVec,hr]
  simp

theorem actual_every_planar_PD_one_level_is_an_ellipse_in_orthogonal_coordinates
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosDef) :
    ∃ a b : ℝ, 0<a ∧ 0<b ∧ ∀ x : Fin 2 → ℝ,
      x∈oneLevel P ↔ (actualCoordinates P hP.1 x 0/a)^2+
        (actualCoordinates P hP.1 x 1/b)^2=1 := by
  have ha:=hP.eigenvalues_pos (0 : Fin 2)
  have hb:=hP.eigenvalues_pos (1 : Fin 2)
  refine ⟨1/Real.sqrt (hP.1.eigenvalues 0),1/Real.sqrt (hP.1.eigenvalues 1),by positivity,by positivity,?_⟩
  intro x
  change realQuadratic P x=1 ↔ _
  rw [plane_energy_normal_form P hP.1 x,
    ←positive_weight_scaled_square _ _ ha,←positive_weight_scaled_square _ _ hb]

theorem actual_nonzero_singular_planar_PSD_one_level_is_two_parallel_lines
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef) (hn : P≠0) (hd : P.det=0) :
    ∃ i : Fin 2, ∃ a : ℝ, 0<a ∧ ∀ x : Fin 2 → ℝ,
      x∈oneLevel P ↔ actualCoordinates P hP.1 x i=a ∨ actualCoordinates P hP.1 x i= -a := by
  have h0:=hP.eigenvalues_nonneg (0 : Fin 2)
  have h1:=hP.eigenvalues_nonneg (1 : Fin 2)
  have hprod : hP.1.eigenvalues 0*hP.1.eigenvalues 1=0 := by
    have h:=hP.1.det_eq_prod_eigenvalues
    simpa only [hd,Fin.prod_univ_two,RCLike.ofReal_real_eq_id,id_eq] using h.symm
  have hnotboth : hP.1.eigenvalues 0≠0 ∨ hP.1.eigenvalues 1≠0 := by
    by_contra h
    push Not at h
    apply hn
    apply hP.1.eigenvalues_eq_zero_iff.mp
    ext i;fin_cases i <;> simp [h.1,h.2]
  rcases mul_eq_zero.mp hprod with hz|hz
  · have hp : 0<hP.1.eigenvalues 1 := by rcases hnotboth with h|h <;> simp_all;positivity
    refine ⟨1,1/Real.sqrt (hP.1.eigenvalues 1),by positivity,?_⟩
    intro x
    change realQuadratic P x=1 ↔ _
    rw [plane_energy_normal_form P hP.1 x,hz,zero_mul,zero_add]
    exact positive_weight_one_level _ _ hp
  · have hp : 0<hP.1.eigenvalues 0 := by rcases hnotboth with h|h <;> simp_all;positivity
    refine ⟨0,1/Real.sqrt (hP.1.eigenvalues 0),by positivity,?_⟩
    intro x
    change realQuadratic P x=1 ↔ _
    rw [plane_energy_normal_form P hP.1 x,hz,zero_mul,add_zero]
    exact positive_weight_one_level _ _ hp

theorem actual_every_planar_indefinite_one_level_is_a_hyperbola_in_orthogonal_coordinates
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.IsHermitian)
    (hind : (¬P.PosSemidef ∧ ¬(-P).PosSemidef)) :
    ∃ i j : Fin 2, ∃ a b : ℝ, i≠j ∧ 0<a ∧ 0<b ∧
      ∀ x : Fin 2 → ℝ, x∈oneLevel P ↔
        (actualCoordinates P hP x i/a)^2-(actualCoordinates P hP x j/b)^2=1 := by
  have hsym : P.transpose=P := by simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hP
  rcases (real_indefinite_iff_both_signs P hsym).mp hind with ⟨⟨xn,hn⟩,⟨xp,hp⟩⟩
  have he (x : Fin 2 → ℝ) : realQuadratic P x=∑ i,hP.eigenvalues i*(actualCoordinates P hP x i)^2 :=
    actual_quadratic_form_is_eigenvalue_weighted_coordinate_energy P hP x
  have hpos : ∃ i : Fin 2,0<hP.eigenvalues i := by
    by_contra h
    push Not at h
    have hb : realQuadratic P xp≤0 := by rw [he];exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg (h i) (sq_nonneg _))
    linarith
  have hneg : ∃ j : Fin 2,hP.eigenvalues j<0 := by
    by_contra h
    push Not at h
    have hb : 0≤realQuadratic P xn := by rw [he];exact Finset.sum_nonneg (fun i _ => mul_nonneg (h i) (sq_nonneg _))
    linarith
  obtain ⟨i,hi⟩:=hpos
  obtain ⟨j,hj⟩:=hneg
  have hij : i≠j := by intro h;subst j;linarith
  have hidx : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by fin_cases i <;> fin_cases j <;> simp_all
  have hnormal (x : Fin 2 → ℝ) : realQuadratic P x=
      hP.eigenvalues i*(actualCoordinates P hP x i)^2+hP.eigenvalues j*(actualCoordinates P hP x j)^2 := by
    rcases hidx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact plane_energy_normal_form P hP x
    · simpa only [add_comm] using plane_energy_normal_form P hP x
  have hjp : 0< -hP.eigenvalues j := neg_pos.mpr hj
  refine ⟨i,j,1/Real.sqrt (hP.eigenvalues i),1/Real.sqrt (-hP.eigenvalues j),hij,
    div_pos zero_lt_one (Real.sqrt_pos.mpr hi),div_pos zero_lt_one (Real.sqrt_pos.mpr hjp),?_⟩
  intro x
  change realQuadratic P x=1 ↔ _
  rw [hnormal,←positive_weight_scaled_square _ _ hi,
    ←positive_weight_scaled_square _ _ (neg_pos.mpr hj)]
  congr 1
  ring

theorem actual_zero_PSD_matrix_has_empty_one_level :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧ oneLevel 0=∅ := by
  constructor
  · exact Matrix.PosSemidef.zero
  · ext x;simp [oneLevel,realQuadratic]

end SafeLearning.CompleteFoundationsPlanarQuadraticLevelSets32
