import SafeLearning.CompleteModulesLipSDPWalkthrough
import SafeLearning.CompleteModulesDesignCertificateSet

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator Topology NNReal
namespace SafeLearning.CompleteModulesLipSDPPracticeCancellation21
open CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesLipSDPProduct
open CompleteModulesLipSDPWalkthrough CompleteModulesDesignScalarLayers

abbrev firstWeight := CompleteModulesDesignCertificateSet.sourceFirst
def absoluteLast : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1,1]
def absoluteNetwork (x : ℝ) : ℝ :=
  oneHiddenNetwork firstWeight absoluteLast 0 0 (fun t : ℝ => max t 0) (fun _=>x) 0

theorem actual_absolute_network_formula (x : ℝ) : absoluteNetwork x=|x| := by
  simp [absoluteNetwork,oneHiddenNetwork,hiddenValues,firstWeight,
    CompleteModulesDesignCertificateSet.sourceFirst,absoluteLast,Matrix.mulVec,
    dotProduct,Fin.sum_univ_one,Fin.sum_univ_two]

theorem actual_absolute_network_gain_is_one : IsLeast (admissibleGains absoluteNetwork) 1 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro x y
    rw [actual_absolute_network_formula,actual_absolute_network_formula,one_mul]
    exact abs_abs_sub_abs_le_abs_sub x y
  · intro L hL
    have h:=hL.2 1 0
    rw [actual_absolute_network_formula,actual_absolute_network_formula] at h
    norm_num at h
    exact h

theorem actual_first_coordinate_energy (x : Fin 1 → ℝ) :
    (∑ i : Fin 2, (firstWeight *ᵥ x) i ^2)=2*(x 0)^2 := by
  simp [firstWeight,CompleteModulesDesignCertificateSet.sourceFirst,Matrix.mulVec,
    dotProduct,Fin.sum_univ_one,Fin.sum_univ_two]
  ring

theorem actual_cancellation_matrix_and_loop_bound :
    absoluteLast * firstWeight=0 ∧ ‖firstWeight‖^2=2 ∧ ‖absoluteLast‖^2=2 ∧
      ‖absoluteLast‖*‖firstWeight‖=2 ∧
      ‖absoluteLast * firstWeight‖+(1/2:ℝ)*‖absoluteLast‖*‖firstWeight‖=1 := by
  have hz : absoluteLast * firstWeight=0 := by
    ext i j; fin_cases i; fin_cases j
    norm_num [absoluteLast,firstWeight,CompleteModulesDesignCertificateSet.sourceFirst,
      Matrix.mul_apply,Fin.sum_univ_two]
  have hf : ‖firstWeight‖^2=2 := by
    have hu : ‖firstWeight‖≤Real.sqrt 2 := by
      apply actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
      intro x
      rw [actual_first_coordinate_energy]
      simp [Fin.sum_univ_one]
    have hl:=actual_spectral_matrix_gain firstWeight (![1] : Fin 1→ℝ)
    have hi : ‖WithLp.toLp 2 (![1] : Fin 1→ℝ)‖^2=1 := by
      rw [squared_norm_of_coordinates];norm_num [Fin.sum_univ_one]
    have ho : ‖WithLp.toLp 2 (firstWeight *ᵥ (![1] : Fin 1→ℝ))‖^2=2 := by
      rw [squared_norm_of_coordinates,actual_first_coordinate_energy];norm_num
    nlinarith [norm_nonneg firstWeight,Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),
      Real.sqrt_nonneg 2,norm_nonneg (WithLp.toLp 2 (![1] : Fin 1→ℝ)),
      norm_nonneg (WithLp.toLp 2 (firstWeight *ᵥ (![1] : Fin 1→ℝ)))]
  have hl : ‖absoluteLast‖^2=2 := by
    exact walkthrough_last_actual_spectral_norm_squared
  have he : ‖absoluteLast‖=‖firstWeight‖ := by
    nlinarith [norm_nonneg absoluteLast,norm_nonneg firstWeight]
  have hp : ‖absoluteLast‖*‖firstWeight‖=2 := by rw [he];nlinarith
  refine ⟨hz,hf,hl,hp,?_⟩
  rw [hz,norm_zero]
  nlinarith

def centredRelu (t : ℝ) : ℝ := max t 0-t/2

theorem actual_centred_relu_formula_and_cancellation (t : ℝ) :
    centredRelu t=|t|/2 ∧ max t 0=t/2+centredRelu t ∧
      absoluteNetwork t=t/2+(-t)/2+centredRelu t+centredRelu (-t) := by
  have hr : centredRelu t=|t|/2 := by
    by_cases ht : 0≤t
    · simp only [centredRelu,max_eq_left ht,abs_of_nonneg ht];ring
    · have hn:=le_of_not_ge ht
      simp only [centredRelu,max_eq_right hn,abs_of_nonpos hn];ring
  refine ⟨hr,by unfold centredRelu;ring,?_⟩
  rw [actual_absolute_network_formula,hr]
  have hm : centredRelu (-t)=|t|/2 := by
    by_cases ht : 0≤t
    · simp only [centredRelu,max_eq_right (by linarith : -t≤0),abs_of_nonneg ht];ring
    · have hn:=le_of_not_ge ht
      simp only [centredRelu,max_eq_left (by linarith : 0≤-t),abs_of_nonpos hn];ring
  rw [hm];ring

theorem actual_centred_relu_half_lipschitz : LipschitzWith (1/2:ℝ≥0) centredRelu := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,(actual_centred_relu_formula_and_cancellation x).1,
    (actual_centred_relu_formula_and_cancellation y).1]
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  have h:=abs_abs_sub_abs_le_abs_sub x y
  rw [←sub_div,abs_div]
  norm_num
  linarith

theorem actual_centred_relu_open_branch_derivatives (t : ℝ) :
    (t<0 → HasDerivAt centredRelu (-1/2) t) ∧
      (0<t → HasDerivAt centredRelu (1/2) t) := by
  constructor
  · intro ht
    have he : centredRelu =ᶠ[𝓝 t] (fun s : ℝ => (-1/2)*s) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      simp only [centredRelu,max_eq_right hs.le];ring
    simpa using ((hasDerivAt_id t).const_mul (-1/2:ℝ)).congr_of_eventuallyEq he
  · intro ht
    have he : centredRelu =ᶠ[𝓝 t] (fun s : ℝ => (1/2)*s) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      simp only [centredRelu,max_eq_left hs.le];ring
    simpa using ((hasDerivAt_id t).const_mul (1/2:ℝ)).congr_of_eventuallyEq he

def biasedNetwork (b : Fin 2→ℝ) (x : ℝ) : ℝ :=
  oneHiddenNetwork firstWeight CompleteModulesDesignCertificateSet.sourceLast b 0
    (fun t : ℝ => max t 0) (fun _=>x) 0
def shifted (x : ℝ) : ℝ := max (x+1) 0-max (-x+1) 0

theorem actual_identical_weights_zero_and_unit_bias_networks (x : ℝ) :
    biasedNetwork 0 x=x ∧ biasedNetwork (fun _=>1) x=shifted x := by
  constructor
  · exact congrFun (CompleteModulesDesignCertificateSet.actual_source_relu_cancellation_is_the_actual_weighted_network x).2 0 |>.trans
      (congrArg (fun f : ℝ→ℝ => f x) (show CompleteModulesDesignCertificateSet.sourceFunction=(fun x=>x) from funext fun x=>(CompleteModulesDesignCertificateSet.actual_source_relu_cancellation_is_the_actual_weighted_network x).1))
  · simp [biasedNetwork,oneHiddenNetwork,hiddenValues,firstWeight,
      CompleteModulesDesignCertificateSet.sourceFirst,CompleteModulesDesignCertificateSet.sourceLast,
      shifted,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Fin.sum_univ_two,sub_eq_add_neg]

theorem actual_shifted_piecewise_formula (x : ℝ) :
    (x≤-1 → shifted x=x-1) ∧
      (-1≤x → x≤1 → shifted x=2*x) ∧
      (1≤x → shifted x=x+1) := by
  constructor
  · intro hx
    simp only [shifted,max_eq_right (by linarith : x+1≤0),
      max_eq_left (by linarith : 0≤-x+1)]
    ring
  constructor
  · intro hlo hhi
    simp only [shifted,max_eq_left (by linarith : 0≤x+1),
      max_eq_left (by linarith : 0≤-x+1)]
    ring
  · intro hx
    simp only [shifted,max_eq_left (by linarith : 0≤x+1),
      max_eq_right (by linarith : -x+1≤0)]
    ring

theorem actual_shifted_least_gain_is_two : IsLeast (admissibleGains shifted) 2 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro x y
    have ha:=abs_max_sub_max_le_abs (x+1) (y+1) (0:ℝ)
    have hb:=abs_max_sub_max_le_abs (-x+1) (-y+1) (0:ℝ)
    have htri:=abs_add_le (max (x+1) 0-max (y+1) 0)
      (-(max (-x+1) 0-max (-y+1) 0))
    have hxe : (x+1)-(y+1)=x-y := by ring
    have hne : (-x+1)-(-y+1)=-(x-y) := by ring
    have hfe : shifted x-shifted y=
      (max (x+1) 0-max (y+1) 0)+(-(max (-x+1) 0-max (-y+1) 0)) := by unfold shifted;ring
    rw [hxe] at ha
    rw [hne,abs_neg] at hb
    rw [←hfe,abs_neg] at htri
    linarith
  · intro L hL
    have h:=hL.2 (1/2) 0
    norm_num [shifted] at h
    linarith

theorem actual_shifted_open_branch_derivatives (t : ℝ) :
    (t< -1 → HasDerivAt shifted 1 t) ∧
      (-1<t → t<1 → HasDerivAt shifted 2 t) ∧
      (1<t → HasDerivAt shifted 1 t) := by
  constructor
  · intro ht
    have he : shifted =ᶠ[𝓝 t] (fun s : ℝ => s-1) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact (actual_shifted_piecewise_formula s).1 hs.le
    exact ((hasDerivAt_id t).sub_const 1).congr_of_eventuallyEq he
  constructor
  · intro hlo hhi
    have he : shifted =ᶠ[𝓝 t] (fun s : ℝ => 2*s) := by
      filter_upwards [eventually_gt_nhds hlo,eventually_lt_nhds hhi] with s hslo hshi
      exact (actual_shifted_piecewise_formula s).2.1 hslo.le hshi.le
    simpa using ((hasDerivAt_id t).const_mul (2:ℝ)).congr_of_eventuallyEq he
  · intro ht
    have he : shifted =ᶠ[𝓝 t] (fun s : ℝ => s+1) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact (actual_shifted_piecewise_formula s).2.2 hs.le
    exact ((hasDerivAt_id t).add_const 1).congr_of_eventuallyEq he

theorem actual_every_weight_only_gain_valid_for_all_biases_is_at_least_two
    (L : ℝ) (h : ∀b : Fin 2→ℝ,∀x y : ℝ,
      |biasedNetwork b x-biasedNetwork b y|≤L*|x-y|) : 2≤L := by
  have hp:=h (fun _=>1) (1/2) 0
  rw [(actual_identical_weights_zero_and_unit_bias_networks _).2,
    (actual_identical_weights_zero_and_unit_bias_networks _).2] at hp
  norm_num [shifted] at hp
  linarith

end SafeLearning.CompleteModulesLipSDPPracticeCancellation21
