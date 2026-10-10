import SafeLearning.CompleteModulesGPLinearInformationBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationDesigns
open CompleteModulesGPLinearInformationBounds
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

def cycleDesign (m : ℕ) : Matrix (Fin m × D) D ℝ :=
  Matrix.of (fun p i => if p.2=i then 1 else 0)
def orthonormalDesign (e : T ↪ D) : Matrix T D ℝ :=
  Matrix.of (fun t i => if e t=i then 1 else 0)

theorem actual_scalar_identity_information_is_the_source_closed_form
    (a lambda : ℝ) (hlambda : 0 < lambda) (ha : 0 ≤ a) :
    information (a • (1 : Matrix D D ℝ)) lambda=
      (Fintype.card D:ℝ)/2*Real.log (1+a/lambda) := by
  have hd : 1+lambda⁻¹ • (a • (1 : Matrix D D ℝ))=
      diagonal (fun _ : D => 1+a/lambda) := by
    ext i j
    by_cases hij : i=j
    · subst j;simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
    · simp [hij]
  unfold information
  rw [hd,det_diagonal,Real.log_prod (fun _ _ =>
    (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg ha hlambda.le)).ne')]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem actual_cycling_inputs_have_unit_euclidean_norm (m : ℕ) (p : Fin m × D) :
    ‖(WithLp.toLp 2 (fun i => cycleDesign m p i) : EuclideanSpace ℝ D)‖=1 := by
  have hs : ‖(WithLp.toLp 2 (fun i => cycleDesign m p i) : EuclideanSpace ℝ D)‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [cycleDesign]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => cycleDesign m p i) : EuclideanSpace ℝ D)]

theorem actual_cycle_design_gram_is_the_sample_per_dimension_times_identity (m : ℕ) :
    (cycleDesign (D:=D) m)ᵀ*cycleDesign m=(m:ℝ) • (1 : Matrix D D ℝ) := by
  ext i j
  change (∑ p : Fin m × D,cycleDesign m p i*cycleDesign m p j)=
    ((m:ℝ) • (1 : Matrix D D ℝ)) i j
  simp only [Matrix.smul_apply,Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    simp [cycleDesign,Fintype.sum_prod_type]
  · simp [cycleDesign,Fintype.sum_prod_type,hij,Ne.symm hij]

theorem actual_cycling_design_attains_the_dimension_bound_when_dimension_divides_sample_count
    [Nonempty D] (m : ℕ) (lambda : ℝ) (hlambda : 0 < lambda) :
    information ((cycleDesign (D:=D) m)ᵀ*cycleDesign m) lambda=
      (Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card (Fin m × D):ℝ)/(lambda*(Fintype.card D:ℝ))) := by
  rw [actual_cycle_design_gram_is_the_sample_per_dimension_times_identity,
    actual_scalar_identity_information_is_the_source_closed_form (m:ℝ) lambda hlambda (by positivity)]
  congr 3
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  have hn : (Fintype.card D:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem actual_embedded_orthonormal_inputs_have_unit_euclidean_norm (e : T ↪ D) (t : T) :
    ‖(WithLp.toLp 2 (fun i => orthonormalDesign e t i) : EuclideanSpace ℝ D)‖=1 := by
  have hs : ‖(WithLp.toLp 2 (fun i => orthonormalDesign e t i) : EuclideanSpace ℝ D)‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [orthonormalDesign]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => orthonormalDesign e t i) : EuclideanSpace ℝ D)]

theorem actual_embedded_orthonormal_design_has_identity_observation_gram (e : T ↪ D) :
    orthonormalDesign e*(orthonormalDesign e)ᵀ=(1 : Matrix T T ℝ) := by
  ext t s
  by_cases hts : t=s
  · subst s;simp [orthonormalDesign,Matrix.mul_apply]
  · have hn : e t≠e s := e.injective.ne hts
    simp [orthonormalDesign,Matrix.mul_apply,hts,hn]

theorem actual_orthonormal_design_information_is_the_source_small_sample_maximum (e : T ↪ D)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    information ((orthonormalDesign e)ᵀ*orthonormalDesign e) lambda=
      (Fintype.card T:ℝ)/2*Real.log (1+1/lambda) := by
  unfold information
  rw [←actual_weinstein_aronszajn_identity_for_the_linear_design,
    actual_embedded_orthonormal_design_has_identity_observation_gram]
  change information (1 : Matrix T T ℝ) lambda=_
  simpa using actual_scalar_identity_information_is_the_source_closed_form (D:=T) 1 lambda hlambda (by norm_num)

def threePlaneDesign : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1,0;-(1/2),Real.sqrt 3/2;-(1/2),-(Real.sqrt 3/2)]

theorem actual_three_plane_unit_vectors_are_a_true_tight_frame :
    (∀ t,‖(WithLp.toLp 2 (fun i => threePlaneDesign t i) : EuclideanSpace ℝ (Fin 2))‖=1) ∧
      threePlaneDesignᵀ*threePlaneDesign=(3/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  constructor
  · intro t
    have he : ‖(WithLp.toLp 2 (fun i => threePlaneDesign t i) : EuclideanSpace ℝ (Fin 2))‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      fin_cases t <;> norm_num [threePlaneDesign,Fin.sum_univ_two] <;> nlinarith
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => threePlaneDesign t i) : EuclideanSpace ℝ (Fin 2))]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [threePlaneDesign,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith

theorem actual_three_plane_angles_are_the_printed_zero_two_thirds_and_four_thirds_pi :
    threePlaneDesign 0=![Real.cos 0,Real.sin 0] ∧
      threePlaneDesign 1=![Real.cos (2*Real.pi/3),Real.sin (2*Real.pi/3)] ∧
      threePlaneDesign 2=![Real.cos (4*Real.pi/3),Real.sin (4*Real.pi/3)] := by
  have hc : Real.cos (2*Real.pi/3)=-(1/2:ℝ) := by
    rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
  have hs : Real.sin (2*Real.pi/3)=Real.sqrt 3/2 := by
    rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.sin_pi_sub,Real.sin_pi_div_three]
  have hc4 : Real.cos (4*Real.pi/3)=-(1/2:ℝ) := by
    rw [show 4*Real.pi/3=Real.pi/3+Real.pi by ring,Real.cos_add_pi,Real.cos_pi_div_three]
  have hs4 : Real.sin (4*Real.pi/3)=-(Real.sqrt 3/2) := by
    rw [show 4*Real.pi/3=Real.pi/3+Real.pi by ring,Real.sin_add_pi,Real.sin_pi_div_three]
  refine ⟨?_,?_,?_⟩
  all_goals ext i;fin_cases i <;> norm_num [threePlaneDesign,hc,hs,hc4,hs4]

theorem actual_three_plane_tight_frame_information_attains_the_source_bound
    (lambda : ℝ) (hlambda : 0 < lambda) :
    information (threePlaneDesignᵀ*threePlaneDesign) lambda=
      Real.log (1+3/(2*lambda)) := by
  rw [actual_three_plane_unit_vectors_are_a_true_tight_frame.2,
    actual_scalar_identity_information_is_the_source_closed_form (3/2:ℝ) lambda hlambda (by norm_num)]
  norm_num
  congr 1
  field_simp

end SafeLearning.CompleteModulesGPLinearInformationDesigns
