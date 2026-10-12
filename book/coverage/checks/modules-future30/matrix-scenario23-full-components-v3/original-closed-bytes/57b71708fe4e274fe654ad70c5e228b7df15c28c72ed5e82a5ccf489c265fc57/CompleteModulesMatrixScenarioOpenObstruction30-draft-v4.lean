import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators

namespace SafeLearning.CompleteModulesMatrixScenarioOpenObstruction30

abbrev State := Fin 4
abbrev Plant := Matrix State State ℝ × (State → ℝ)

def closedLoop (m : Plant) (K : State → ℝ) : Matrix State State ℝ :=
  m.1 + Matrix.vecMulVec m.2 K

def actualSchurStable (C : Matrix State State ℝ) : Prop :=
  ∀ z ∈ (C.map Complex.ofReal).charpoly.roots, ‖z‖ < 1

def gainL1 (K : State → ℝ) : ℝ := ∑ j, |K j|
def unitInput (i : State) (j : State) : ℝ := if j=i then 1 else 0
def inputClose (m : Plant) (i : State) : Prop :=
  ∀ j, |m.2 j-unitInput i j| < 1/64
def smallTracePlantNeighborhood (i : State) : Set Plant :=
  {m | |m.1.trace| < 1 ∧ inputClose m i}
def largeTracePlantNeighborhood : Set Plant :=
  {m | 11 < m.1.trace ∧ inputClose m 3}

def incompatibleFivePlantNeighborhood : Set (Fin 5 → Plant) :=
  {s | (∀ i : State, s i.castSucc ∈ smallTracePlantNeighborhood i) ∧
    s (Fin.last 4) ∈ largeTracePlantNeighborhood}

theorem actual_complex_root_sum_norm_is_bounded_by_multiplicity_card
    (roots : Multiset ℂ) (h : ∀ z ∈ roots, ‖z‖ ≤ 1) :
    ‖roots.sum‖ ≤ (roots.card:ℝ) := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons a roots ih =>
    have ha := h a (by simp)
    have hs := ih (fun z hz => h z (by simp [hz]))
    have hadd := norm_add_le a roots.sum
    simpa only [Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
      using (show ‖a+roots.sum‖ ≤ (roots.card:ℝ)+1 by linarith)

theorem actual_stable_four_state_matrix_has_trace_absolute_value_at_most_four
    (C : Matrix State State ℝ) (hC : actualSchurStable C) : |C.trace| ≤ 4 := by
  have hsum := actual_complex_root_sum_norm_is_bounded_by_multiplicity_card
    (C.map Complex.ofReal).charpoly.roots (fun z hz => (hC z hz).le)
  have hcard : ((C.map Complex.ofReal).charpoly.roots.card:ℝ) ≤ 4 := by
    have h := Polynomial.card_roots' (C.map Complex.ofReal).charpoly
    simp only [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin] at h
    exact_mod_cast h
  rw [←Matrix.trace_eq_sum_roots_charpoly] at hsum
  have he : (C.map Complex.ofReal).trace=(C.trace:ℂ) := by
    simp [Matrix.trace,Matrix.diag,Matrix.map_apply]
  rw [he,Complex.norm_real,Real.norm_eq_abs] at hsum
  exact hsum.trans hcard

theorem actual_rank_one_state_feedback_trace_is_the_input_gain_pairing
    (m : Plant) (K : State → ℝ) :
    (closedLoop m K).trace=m.1.trace+∑ j,m.2 j*K j := by
  simp [closedLoop,Matrix.trace_add,Matrix.trace_vecMulVec,dotProduct]

theorem actual_input_perturbation_pairing_error_is_uniform_in_the_gain
    (m : Plant) (i : State) (hm : inputClose m i) (K : State → ℝ) :
    |(∑ j,m.2 j*K j)-K i| ≤ (1/64)*gainL1 K := by
  have he : (∑ j,m.2 j*K j)-K i=∑ j,(m.2 j-unitInput i j)*K j := by
    simp [Finset.sum_sub_distrib,sub_mul,unitInput]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb : ∑ j, |(m.2 j-unitInput i j)*K j| ≤ ∑ j,(1/64:ℝ)*|K j| := by
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hm j).le (abs_nonneg _)
  simpa [gainL1,Finset.mul_sum] using hb

theorem actual_small_trace_plant_stability_bounds_the_corresponding_gain_coordinate
    (m : Plant) (i : State) (hm : m ∈ smallTracePlantNeighborhood i)
    (K : State → ℝ) (hs : actualSchurStable (closedLoop m K)) :
    |K i| ≤ 5+(1/64)*gainL1 K := by
  have hc := actual_stable_four_state_matrix_has_trace_absolute_value_at_most_four _ hs
  rw [actual_rank_one_state_feedback_trace_is_the_input_gain_pairing] at hc
  have he := actual_input_perturbation_pairing_error_is_uniform_in_the_gain m i hm.2 K
  have htri := abs_add_le (m.1.trace+∑ j,m.2 j*K j)
    (-m.1.trace-((∑ j,m.2 j*K j)-K i))
  have htri' := abs_add_le (-m.1.trace) (-((∑ j,m.2 j*K j)-K i))
  have hident : m.1.trace+(∑ j,m.2 j*K j)+
      (-m.1.trace-((∑ j,m.2 j*K j)-K i))=K i := by ring
  rw [hident] at htri
  simp only [abs_neg] at htri'
  change |m.1.trace| < 1 ∧ inputClose m i at hm
  simp only [sub_eq_add_neg] at htri htri' he
  linarith [hm.1]

theorem actual_four_small_trace_models_bound_the_entire_common_gain
    (s : State → Plant) (hs : ∀ i,s i ∈ smallTracePlantNeighborhood i)
    (K : State → ℝ) (hstable : ∀ i,actualSchurStable (closedLoop (s i) K)) :
    gainL1 K ≤ 64/3 := by
  have hb := Finset.sum_le_sum (fun (i : State) (_ : i ∈ Finset.univ) =>
    actual_small_trace_plant_stability_bounds_the_corresponding_gain_coordinate
      (s i) i (hs i) K (hstable i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  change gainL1 K ≤ 4*(5+(1/64)*gainL1 K) at hb
  linarith

theorem actual_open_five_model_neighborhood_has_no_common_stabilizing_gain
    (s : Fin 5 → Plant) (hs : s ∈ incompatibleFivePlantNeighborhood) :
    ¬ ∃ K : State → ℝ, ∀ i,actualSchurStable (closedLoop (s i) K) := by
  rintro ⟨K,hK⟩
  have hL := actual_four_small_trace_models_bound_the_entire_common_gain
    (fun i => s i.castSucc) hs.1 K (fun i => hK i.castSucc)
  have hcoordinate := actual_small_trace_plant_stability_bounds_the_corresponding_gain_coordinate
    (s (3:State).castSucc) 3 (hs.1 3) K (hK (3:State).castSucc)
  have he := actual_input_perturbation_pairing_error_is_uniform_in_the_gain
    (s (Fin.last 4)) 3 hs.2.2 K
  have hc := actual_stable_four_state_matrix_has_trace_absolute_value_at_most_four _
    (hK (Fin.last 4))
  rw [actual_rank_one_state_feedback_trace_is_the_input_gain_pairing] at hc
  have hlow : -(5+(2/64)*gainL1 K) ≤ ∑ j,(s (Fin.last 4)).2 j*K j := by
    have hcoord := (abs_le.mp hcoordinate).1
    have herr := (abs_le.mp he).1
    linarith
  have hupper := (abs_le.mp hc).2
  have hlast : 11 < (s (Fin.last 4)).1.trace ∧ inputClose (s (Fin.last 4)) 3 := hs.2
  linarith [hlast.1]

theorem actual_plant_trace_is_continuous : Continuous (fun m : Plant => m.1.trace) := by
  unfold Matrix.trace Matrix.diag
  fun_prop

theorem actual_input_coordinate_neighborhood_is_open (i : State) :
    IsOpen {m : Plant | inputClose m i} := by
  have he : {m : Plant | inputClose m i}=
      ⋂ j : State,{m : Plant | |m.2 j-unitInput i j| < 1/64} := by ext m;simp [inputClose]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (by fun_prop) continuous_const

theorem actual_five_model_obstruction_is_a_nonempty_open_set :
    IsOpen incompatibleFivePlantNeighborhood ∧ incompatibleFivePlantNeighborhood.Nonempty := by
  have hsmall (i : State) : IsOpen (smallTracePlantNeighborhood i) :=
    (isOpen_lt actual_plant_trace_is_continuous.abs continuous_const).inter
      (actual_input_coordinate_neighborhood_is_open i)
  have hlarge : IsOpen largeTracePlantNeighborhood :=
    (isOpen_lt continuous_const actual_plant_trace_is_continuous).inter
      (actual_input_coordinate_neighborhood_is_open 3)
  have he : incompatibleFivePlantNeighborhood=
      (⋂ i : State, (fun s : Fin 5 → Plant => s i.castSucc) ⁻¹' smallTracePlantNeighborhood i) ∩
        (fun s : Fin 5 → Plant => s (Fin.last 4)) ⁻¹' largeTracePlantNeighborhood := by
    ext s;simp [incompatibleFivePlantNeighborhood]
  constructor
  · rw [he]
    exact (isOpen_iInter_of_finite (fun i => (hsmall i).preimage (continuous_apply _))).inter
      (hlarge.preimage (continuous_apply _))
  · let small : State → Plant := fun i => (0,unitInput i)
    let large : Plant := ((3:ℝ) • (1:Matrix State State ℝ),unitInput 3)
    refine ⟨Fin.snoc small large,?_,?_⟩
    · intro i
      simp [smallTracePlantNeighborhood,small,inputClose,Fin.snoc]
    · norm_num [largeTracePlantNeighborhood,large,inputClose,Matrix.trace_smul,
        Matrix.trace_one,Fin.snoc]

theorem actual_independent_full_support_matrix_samples_have_positive_common_gain_failure_probability
    (P : Measure Plant) [IsProbabilityMeasure P] [P.IsOpenPosMeasure] :
    0 < (Measure.pi (fun _ : Fin 5 => P))
      {s | ¬ ∃ K : State → ℝ, ∀ i,actualSchurStable (closedLoop (s i) K)} := by
  obtain ⟨hopen,hne⟩ := actual_five_model_obstruction_is_a_nonempty_open_set
  apply (hopen.measure_pos (Measure.pi (fun _ : Fin 5 => P)) hne).trans_le
  apply measure_mono
  intro s hs
  exact actual_open_five_model_neighborhood_has_no_common_stabilizing_gain s hs

end SafeLearning.CompleteModulesMatrixScenarioOpenObstruction30

namespace SafeLearning.CompleteModulesMatrixScenarioOpenObstruction30
open scoped ComplexOrder
section Lyapunov
variable {n : Type*} [Fintype n] [DecidableEq n]

def complexRealEnergy (P : Matrix n n ℝ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (P.map Complex.ofReal *ᵥ v)).re

theorem actual_complex_energy_is_the_sum_of_real_and_imaginary_energies
    (P : Matrix n n ℝ) (v : n → ℂ) :
    complexRealEnergy P v =
      (fun i => (v i).re) ⬝ᵥ (P *ᵥ (fun i => (v i).re))+
      (fun i => (v i).im) ⬝ᵥ (P *ᵥ (fun i => (v i).im)) := by
  simp [complexRealEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum,Complex.mul_re,
    Finset.sum_add_distrib,mul_add,mul_assoc]

theorem actual_real_positive_definiteness_is_positive_on_every_nonzero_complex_vector
    (P : Matrix n n ℝ) (hP : P.PosDef) (v : n → ℂ) (hv : v ≠ 0) :
    0 < complexRealEnergy P v := by
  rw [actual_complex_energy_is_the_sum_of_real_and_imaginary_energies]
  have hr := hP.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have hi := hP.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
  simp only [star_trivial] at hr hi
  by_cases h0 : (fun i => (v i).re)=0
  · have h1 : (fun i => (v i).im) ≠ 0 := by
      intro hz;apply hv;ext i;apply Complex.ext
      · simpa using congrFun h0 i
      · simpa using congrFun hz i
    have hp := hP.dotProduct_mulVec_pos h1
    simpa only [star_trivial] using add_pos_of_nonneg_of_pos hr hp
  · have hp := hP.dotProduct_mulVec_pos h0
    simpa only [star_trivial] using add_pos_of_pos_of_nonneg hp hi

theorem actual_complex_energy_scales_by_squared_eigenvalue_norm
    (P : Matrix n n ℝ) (v : n → ℂ) (z : ℂ) :
    complexRealEnergy P (z • v) = ‖z‖^2*complexRealEnergy P v := by
  simp only [complexRealEnergy,Matrix.mulVec_smul,star_smul,smul_dotProduct,
    dotProduct_smul,smul_eq_mul,←mul_assoc,Complex.star_def,Complex.conj_mul']
  simp

theorem actual_discrete_Lyapunov_difference_is_the_complex_energy_drop
    (P C : Matrix n n ℝ) (v : n → ℂ) :
    complexRealEnergy (P-C.transpose*P*C) v =
      complexRealEnergy P v-complexRealEnergy P (C.map Complex.ofReal *ᵥ v) := by
  have hc : (C.transpose.map Complex.ofReal)=(C.map Complex.ofReal).conjTranspose := by
    ext i j;simp [Matrix.conjTranspose_apply]
  have he : star v ⬝ᵥ (((C.map Complex.ofReal).conjTranspose *
      P.map Complex.ofReal * C.map Complex.ofReal) *ᵥ v)=
      star (C.map Complex.ofReal *ᵥ v) ⬝ᵥ
        (P.map Complex.ofReal *ᵥ (C.map Complex.ofReal *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.star_mulVec]
  simp only [complexRealEnergy,Matrix.map_sub,Matrix.map_mul,hc,
    Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re]
  rw [he]

theorem actual_positive_discrete_Lyapunov_certificate_bounds_every_complex_eigenvalue
    (P C : Matrix n n ℝ) (hP : P.PosDef) (hdrop : (P-C.transpose*P*C).PosDef)
    (v : n → ℂ) (hv : v ≠ 0) (z : ℂ)
    (heigen : C.map Complex.ofReal *ᵥ v=z • v) : ‖z‖ < 1 := by
  have hp := actual_real_positive_definiteness_is_positive_on_every_nonzero_complex_vector P hP v hv
  have hd := actual_real_positive_definiteness_is_positive_on_every_nonzero_complex_vector _ hdrop v hv
  rw [actual_discrete_Lyapunov_difference_is_the_complex_energy_drop,heigen,
    actual_complex_energy_scales_by_squared_eigenvalue_norm] at hd
  nlinarith [norm_nonneg z]

theorem actual_positive_discrete_Lyapunov_certificate_implies_actual_Schur_stability
    (P C : Matrix State State ℝ) (hP : P.PosDef) (hdrop : (P-C.transpose*P*C).PosDef) :
    actualSchurStable C := by
  intro z hz
  have hs : z ∈ spectrum ℂ (C.map Complex.ofReal) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hz)
  have he : Module.End.HasEigenvalue (C.map Complex.ofReal).toLin' z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by simpa using hs)
  obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  have hv' : C.map Complex.ofReal *ᵥ v=z • v := by
    simpa using hv.apply_eq_smul
  exact actual_positive_discrete_Lyapunov_certificate_bounds_every_complex_eigenvalue
    P C hP hdrop v hv.2 z hv'

theorem actual_open_five_model_event_has_no_common_positive_Lyapunov_certificate
    (s : Fin 5 → Plant) (hs : s ∈ incompatibleFivePlantNeighborhood) :
    ¬ ∃ (K : State → ℝ) (P : Matrix State State ℝ),
      P.PosDef ∧ ∀ i,(P-(closedLoop (s i) K).transpose*P*closedLoop (s i) K).PosDef := by
  rintro ⟨K,P,hP,hdrop⟩
  apply actual_open_five_model_neighborhood_has_no_common_stabilizing_gain s hs
  exact ⟨K,fun i => actual_positive_discrete_Lyapunov_certificate_implies_actual_Schur_stability
    P _ hP (hdrop i)⟩
end Lyapunov

open ProbabilityTheory
abbrev Coordinates := State → Fin 5 → ℝ

def coordinatesToPlant (x : Coordinates) : Plant :=
  (fun i j => x i j.castSucc,fun i => x i (Fin.last 4))

def nondegenerateAffineGaussianPlantLaw (center : Coordinates)
    (factor : Coordinates ≃L[ℝ] Coordinates) : Measure Plant :=
  (Measure.pi (fun _ : State => Measure.pi (fun _ : Fin 5 => gaussianReal 0 1))).map
    (fun x => coordinatesToPlant (center+factor x))

theorem actual_unit_variance_real_Gaussian_has_full_support :
    (gaussianReal 0 1).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0) ≠ 0)).isOpenPosMeasure

theorem actual_coordinates_to_plant_map_is_continuous_and_surjective :
    Continuous coordinatesToPlant ∧ Function.Surjective coordinatesToPlant := by
  constructor
  · unfold coordinatesToPlant;fun_prop
  · rintro ⟨A,B⟩
    refine ⟨fun i => Fin.snoc (A i) (B i),?_⟩
    ext i j <;> simp [coordinatesToPlant]

theorem actual_nondegenerate_affine_Gaussian_plant_law_has_full_support
    (center : Coordinates) (factor : Coordinates ≃L[ℝ] Coordinates) :
    (nondegenerateAffineGaussianPlantLaw center factor).IsOpenPosMeasure := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure := actual_unit_variance_real_Gaussian_has_full_support
  have hc : Continuous (fun x : Coordinates => coordinatesToPlant (center+factor x)) :=
    actual_coordinates_to_plant_map_is_continuous_and_surjective.1.comp
      (continuous_const.add factor.continuous)
  have hs : Function.Surjective (fun x : Coordinates => coordinatesToPlant (center+factor x)) := by
    intro m
    obtain ⟨x,hx⟩ := actual_coordinates_to_plant_map_is_continuous_and_surjective.2 m
    refine ⟨factor.symm (x-center),?_⟩
    simpa using hx
  exact hc.isOpenPosMeasure_map hs

theorem actual_nondegenerate_affine_Gaussian_plant_law_is_a_probability
    (center : Coordinates) (factor : Coordinates ≃L[ℝ] Coordinates) :
    IsProbabilityMeasure (nondegenerateAffineGaussianPlantLaw center factor) := by
  unfold nondegenerateAffineGaussianPlantLaw
  apply Measure.isProbabilityMeasure_map
  exact (actual_coordinates_to_plant_map_is_continuous_and_surjective.1.comp
    (continuous_const.add factor.continuous)).aemeasurable

theorem actual_nondegenerate_affine_Gaussian_sample_has_positive_common_Lyapunov_failure_probability
    (center : Coordinates) (factor : Coordinates ≃L[ℝ] Coordinates) :
    0 < (Measure.pi (fun _ : Fin 5 => nondegenerateAffineGaussianPlantLaw center factor))
      {s | ¬ ∃ (K : State → ℝ) (P : Matrix State State ℝ),
        P.PosDef ∧ ∀ i,(P-(closedLoop (s i) K).transpose*P*closedLoop (s i) K).PosDef} := by
  letI := actual_nondegenerate_affine_Gaussian_plant_law_has_full_support center factor
  letI := actual_nondegenerate_affine_Gaussian_plant_law_is_a_probability center factor
  obtain ⟨ho,hn⟩ := actual_five_model_obstruction_is_a_nonempty_open_set
  apply (ho.measure_pos (Measure.pi (fun _ : Fin 5 => nondegenerateAffineGaussianPlantLaw center factor)) hn).trans_le
  exact measure_mono (fun s hs => actual_open_five_model_event_has_no_common_positive_Lyapunov_certificate s hs)

end SafeLearning.CompleteModulesMatrixScenarioOpenObstruction30
