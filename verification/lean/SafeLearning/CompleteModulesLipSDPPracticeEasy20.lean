import SafeLearning.CompleteModulesLipSDPWalkthrough
import SafeLearning.CompleteModulesDesignEasyMatrices

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator Topology NNReal
namespace SafeLearning.CompleteModulesLipSDPPracticeEasy20
open CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesLipSDPProduct
open CompleteModulesLipSDPWalkthrough

abbrev Input := EuclideanSpace ℝ (Fin 2)
def firstWeight : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![3,1]
def lastWeight : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![0,2]
def network (x : Input) : ℝ :=
  oneHiddenNetwork firstWeight lastWeight 0 0 (fun t : ℝ => max t 0) (WithLp.ofLp x) 0

theorem actual_source_network_formula (x : Input) : network x=2*max (x 1) 0 := by
  simp [network,oneHiddenNetwork,hiddenValues,firstWeight,lastWeight,Matrix.mulVec,
    dotProduct,Fin.sum_univ_two,diagonal_apply]

theorem actual_source_last_coordinate_energy (x : Fin 2 → ℝ) :
    ∑ i : Fin 1,(lastWeight *ᵥ x) i ^2=4*(x 1)^2 := by
  simp [lastWeight,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Fin.sum_univ_two]
  ring

theorem actual_source_weight_norms_and_product :
    ‖firstWeight‖=3 ∧ ‖lastWeight‖=2 ∧ ‖lastWeight‖*‖firstWeight‖=6 := by
  have hfirst : ‖firstWeight‖=3 := by
    exact CompleteModulesDesignEasyMatrices.actual_source_spectral_and_frobenius_norms.1
  have hu : ‖lastWeight‖≤2 := by
    have h : Real.sqrt (4:ℝ)=2 := by norm_num
    rw [←h]
    apply actual_spectral_norm_le_of_quadratic_bound _ 4 (by norm_num)
    intro x
    rw [actual_source_last_coordinate_energy]
    simp only [Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0)]
  have hi : ‖WithLp.toLp 2 (![0,1] : Fin 2 → ℝ)‖=1 := by
    have hs:=squared_norm_of_coordinates (![0,1] : Fin 2 → ℝ)
    have hs' : ‖WithLp.toLp 2 (![0,1] : Fin 2 → ℝ)‖^2=1 := by simpa [Fin.sum_univ_two] using hs
    nlinarith [norm_nonneg (WithLp.toLp 2 (![0,1] : Fin 2 → ℝ))]
  have ho : ‖WithLp.toLp 2 (lastWeight *ᵥ (![0,1] : Fin 2 → ℝ))‖=2 := by
    have hs:=squared_norm_of_coordinates (lastWeight *ᵥ (![0,1] : Fin 2 → ℝ))
    rw [actual_source_last_coordinate_energy] at hs
    norm_num at hs
    nlinarith [norm_nonneg (WithLp.toLp 2 (lastWeight *ᵥ (![0,1] : Fin 2 → ℝ)))]
  have hl:=actual_spectral_matrix_gain lastWeight (![0,1] : Fin 2 → ℝ)
  rw [hi,ho,mul_one] at hl
  have he:=le_antisymm hu hl
  exact ⟨hfirst,he,by rw [hfirst,he];norm_num⟩

theorem actual_source_network_is_two_lipschitz : LipschitzWith 2 network := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,dist_eq_norm,actual_source_network_formula,actual_source_network_formula,
    ←mul_sub,abs_mul]
  rw [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  norm_num only [NNReal.coe_ofNat]
  have hcoord : |x 1-y 1|≤‖x-y‖ := by
    simpa only [Real.norm_eq_abs,PiLp.sub_apply] using PiLp.norm_apply_le (x-y) 1
  have hrelu:=abs_max_sub_max_le_abs (x 1) (y 1) (0:ℝ)
  linarith

theorem actual_source_active_pair_attains_two :
    |network (WithLp.toLp 2 ![0,2])-network (WithLp.toLp 2 ![0,1])|=2 ∧
      ‖(WithLp.toLp 2 (![0,2] : Fin 2 → ℝ))-(WithLp.toLp 2 ![0,1])‖=1 := by
  constructor
  · rw [actual_source_network_formula,actual_source_network_formula]
    norm_num
  · have hs:=EuclideanSpace.real_norm_sq_eq
      ((WithLp.toLp 2 (![0,2] : Fin 2 → ℝ))-(WithLp.toLp 2 ![0,1]))
    norm_num [Fin.sum_univ_two] at hs
    rcases hs with hs | hs
    · exact hs
    · have hn:=norm_nonneg ((WithLp.toLp 2 (![0,2] : Fin 2 → ℝ))-(WithLp.toLp 2 ![0,1]))
      rw [hs] at hn
      norm_num at hn

theorem actual_source_least_global_network_gain :
    IsLeast {L : ℝ | 0≤L ∧ ∀ x y : Input,|network x-network y|≤L*‖x-y‖} 2 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro x y
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_ofNat] using
      actual_source_network_is_two_lipschitz.dist_le_mul x y
  · intro L hL
    have h:=hL.2 (WithLp.toLp 2 ![0,2]) (WithLp.toLp 2 ![0,1])
    rw [actual_source_active_pair_attains_two.1,actual_source_active_pair_attains_two.2,mul_one] at h
    exact h

theorem actual_source_second_coordinate_open_branch_derivatives (a t : ℝ) :
    (t<0 → HasDerivAt (fun s : ℝ => network (WithLp.toLp 2 ![a,s])) 0 t) ∧
      (0<t → HasDerivAt (fun s : ℝ => network (WithLp.toLp 2 ![a,s])) 2 t) := by
  constructor
  · intro ht
    have he : (fun s : ℝ => network (WithLp.toLp 2 ![a,s])) =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      rw [actual_source_network_formula]
      simp [max_eq_right hs.le]
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he
  · intro ht
    have he : (fun s : ℝ => network (WithLp.toLp 2 ![a,s])) =ᶠ[𝓝 t] (fun s => 2*s) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      rw [actual_source_network_formula]
      simp [max_eq_left hs.le]
    simpa using ((hasDerivAt_id t).const_mul (2:ℝ)).congr_of_eventuallyEq he

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_squared_certificate_implies_three_halves_gain (f : E → F)
    (hcertificate : ∀ x y,‖f x-f y‖^2≤(9/4:ℝ)*‖x-y‖^2) :
    LipschitzWith (3/2:ℝ≥0) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have h:=hcertificate x y
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  nlinarith [norm_nonneg (f x-f y),norm_nonneg (x-y)]

theorem actual_derivative_refutes_the_source_squared_certificate
    (f : E → F) (x : E) (D : E →L[ℝ] F) (hD : HasFDerivAt f D x)
    (hnorm : ‖D‖=(8/5:ℝ)) :
    ¬ (∀ a b,‖f a-f b‖^2≤(9/4:ℝ)*‖a-b‖^2) := by
  intro hc
  have hb:=norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (actual_squared_certificate_implies_three_halves_gain f hc)
  rw [hD.fderiv,hnorm] at hb
  norm_num at hb

theorem actual_gradient_refutes_the_source_squared_certificate
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (f : G → ℝ) (x gradient : G)
    (hD : HasFDerivAt f (innerSL ℝ gradient) x) (hnorm : ‖gradient‖=(8/5:ℝ)) :
    ¬ (∀ a b,|f a-f b|^2≤(9/4:ℝ)*‖a-b‖^2) := by
  intro hc
  have hnormD : ‖innerSL ℝ gradient‖=(8/5:ℝ) := by simpa only [innerSL_apply_norm] using hnorm
  apply actual_derivative_refutes_the_source_squared_certificate f x (innerSL ℝ gradient) hD hnormD
  simpa only [Real.norm_eq_abs] using hc

def firstLayer (x : ℝ) : ℝ := (3/2)*x
def secondLayer (z : ℝ) : ℝ := 2*z
def composite (x : ℝ) : ℝ := secondLayer (firstLayer x)

theorem actual_source_weighted_layer_equalities (x y z w : ℝ) :
    4*(firstLayer x-firstLayer y)^2=9*(x-y)^2 ∧
      (secondLayer z-secondLayer w)^2=4*(z-w)^2 ∧
      composite x=3*x ∧ (composite x-composite y)^2=9*(x-y)^2 := by
  dsimp only [composite,firstLayer,secondLayer]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem actual_source_composite_least_gain :
    IsLeast {L : ℝ | 0≤L ∧ ∀ x y,|composite x-composite y|≤L*|x-y|} 3 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro x y
    rw [(actual_source_weighted_layer_equalities x y 0 0).2.2.1,
      (actual_source_weighted_layer_equalities y x 0 0).2.2.1,←mul_sub,abs_mul]
    norm_num
  · intro L hL
    have h:=hL.2 1 0
    norm_num [composite,firstLayer,secondLayer] at h
    exact h

end SafeLearning.CompleteModulesLipSDPPracticeEasy20
