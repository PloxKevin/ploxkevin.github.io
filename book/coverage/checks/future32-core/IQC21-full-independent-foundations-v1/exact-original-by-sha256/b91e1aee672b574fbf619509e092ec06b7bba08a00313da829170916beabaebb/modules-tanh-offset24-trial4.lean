import SafeLearning.CompleteModulesTanhNumerics
import SafeLearning.CompleteModulesNNTwoLayerLFT23
import SafeLearning.CompleteModulesDiagonalQC
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNTanhOffset24
open CompleteModulesTanhNumerics CompleteModulesTanhChords CompleteModulesTheory
open CompleteModulesLipSDP

def shifted (center s : ℝ) : ℝ := Real.tanh (s+center)-Real.tanh center
def sourceBase : Fin 2 → ℝ := ![0,2]
def sourceChannel (i : Fin 2) (s : ℝ) : ℝ := shifted (sourceBase i) s
def sourceM : Matrix (Fin 2) (Fin 2) ℝ := !![1,-1;-1,1]

theorem actual_tanh_has_the_true_zero_one_chord_slopes :
    slopeRestricted Real.tanh 0 1 := by
  intro x y
  by_cases h : x=y
  · subst y
    exact ⟨0,by norm_num,by norm_num,by simp⟩
  · have hb := actual_tanh_chord_quotient_is_positive_and_at_most_one x y h
    exact ⟨(Real.tanh x-Real.tanh y)/(x-y),hb.1.le,hb.2,
      (div_mul_cancel₀ _ (sub_ne_zero.mpr h)).symm⟩

theorem actual_every_shifted_channel_vanishes_and_has_own_valid_sector (center : ℝ) :
    shifted center 0=0 ∧ slopeRestricted (shifted center) 0 1 ∧
      ∀ s,0≤2*shifted center s*(s-shifted center s) := by
  have h:=CompleteModulesNNTwoLayerLFT23.actual_shifted_neuron_equation_and_inherited_common_slopes
    Real.tanh center 0 1 actual_tanh_has_the_true_zero_one_chord_slopes
  exact ⟨h.1,h.2.1,by simpa only [zero_mul,sub_zero,one_mul,shifted,CompleteModulesNNTwoLayerLFT23.shifted] using h.2.2.2⟩

theorem actual_both_literal_shifted_functions :
    (∀ s,sourceChannel 0 s=Real.tanh s) ∧
      (∀ s,sourceChannel 1 s=Real.tanh (s+2)-Real.tanh 2) := by
  constructor <;> intro s <;> simp [sourceChannel,sourceBase,shifted]

theorem actual_source_matrix_qc_is_the_difference_product (v w : Fin 2 → ℝ) :
    v ⬝ᵥ (sourceM*ᵥ w)=(v 0-v 1)*(w 0-w 1) := by
  simp [sourceM,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_half_and_two_tanh_have_rigorous_rational_enclosures :
    (0.4621171571:ℝ)<Real.tanh (1/2) ∧ Real.tanh (1/2)<0.4621171574 ∧
      (0.9640275799:ℝ)<Real.tanh 2 ∧ Real.tanh 2<0.9640275802 := by
  have hlo:=Real.exp_one_gt_d9
  have hhi:=Real.exp_one_lt_d9
  have he:=Real.exp_pos 1
  have hhalf : (Real.exp (1/2:ℝ))^2=Real.exp 1 := by
    rw [pow_two,←Real.exp_add]
    norm_num
  have htwo : Real.exp 2=(Real.exp 1)^2 := by
    rw [pow_two,←Real.exp_add]
    norm_num
  have hsqL : (7.389056097:ℝ)<(Real.exp 1)^2 := by nlinarith
  have hsqU : (Real.exp 1)^2<(7.389056100:ℝ) := by nlinarith
  have hquarticL : (54.59815002:ℝ)<((Real.exp 1)^2)^2 := by nlinarith
  have hquarticU : ((Real.exp 1)^2)^2<(54.59815006:ℝ) := by nlinarith
  rw [actual_tanh_is_the_exponential_square_ratio,actual_tanh_is_the_exponential_square_ratio,
    hhalf,htwo]
  refine ⟨?_,?_,?_,?_⟩
  · apply (lt_div_iff₀ (by positivity : 0<Real.exp 1+1)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity : 0<Real.exp 1+1)).mpr
    linarith
  · apply (lt_div_iff₀ (by positivity : 0<((Real.exp 1)^2)^2+1)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity : 0<((Real.exp 1)^2)^2+1)).mpr
    linarith

theorem actual_literal_unequal_tanh_offsets_violate_the_printed_coupled_qc :
    (![(-1:ℝ),-1.5] : Fin 2→ℝ) ⬝ᵥ
      (sourceM*ᵥ(fun i=>sourceChannel i (![(-1:ℝ),-1.5] i)))<0 := by
  rw [actual_source_matrix_qc_is_the_difference_product]
  norm_num [sourceChannel,sourceBase,shifted,Real.tanh_neg]
  have h:=actual_tanh_one_rigorous_rational_enclosure
  have hh:=actual_half_and_two_tanh_have_rigorous_rational_enclosures
  nlinarith

theorem actual_literal_numbers_are_rounded_with_strict_non_equalities :
    |Real.tanh (-1)-(-0.7616)|<0.00005 ∧ Real.tanh (-1)≠ -0.7616 ∧
      |(Real.tanh (1/2)-Real.tanh 2)-(-0.5019)|<0.00005 ∧
      Real.tanh (1/2)-Real.tanh 2≠ -0.5019 ∧
      |(Real.tanh (-1)-(Real.tanh (1/2)-Real.tanh 2))-(-0.2597)|<0.00005 ∧
      Real.tanh (-1)-(Real.tanh (1/2)-Real.tanh 2)≠ -0.2597 ∧
      |(1/2)*(Real.tanh (-1)-(Real.tanh (1/2)-Real.tanh 2))-(-0.130)|<0.0005 ∧
      (1/2)*(Real.tanh (-1)-(Real.tanh (1/2)-Real.tanh 2))≠ -0.130 := by
  have h:=actual_tanh_one_rigorous_rational_enclosure
  have hh:=actual_half_and_two_tanh_have_rigorous_rational_enclosures
  rw [Real.tanh_neg]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (apply abs_lt.mpr; constructor <;> linarith) | (intro he; linarith)

theorem actual_equal_offset_group_has_the_true_monotonicity_qc (center x y : ℝ) :
    0≤(x-y)*(shifted center x-shifted center y) := by
  have h : Monotone (shifted center) := fun x y hxy=>sub_le_sub_right
    (tanh_monotone (by linarith : x+center≤y+center)) _
  rcases le_total y x with hyx|hxy
  · exact mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr (h hyx))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy) (sub_nonpos.mpr (h hxy))

theorem actual_every_shifted_channel_has_valid_nonnegative_diagonal_sector_weights
    {n : Type*} [Fintype n] (centers weights v : n→ℝ) (hw : ∀ i,0≤weights i) :
    0≤∑ i,weights i*(2*shifted (centers i) (v i)*(v i-shifted (centers i) (v i))) := by
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (hw i)
    ((actual_every_shifted_channel_vanishes_and_has_own_valid_sector (centers i)).2.2 (v i)))



theorem actual_literal_diagonal_products_are_nonnegative_rounded_and_not_equal :
    0 ≤ (-1:ℝ) * sourceChannel 0 (-1) ∧
    0 ≤ (-1.5:ℝ) * sourceChannel 1 (-1.5) ∧
    |(-1:ℝ)*sourceChannel 0 (-1)-0.762|<0.0005 ∧
    (-1:ℝ)*sourceChannel 0 (-1)≠0.762 ∧
    |(-1.5:ℝ)*sourceChannel 1 (-1.5)-0.753|<0.0005 ∧
    (-1.5:ℝ)*sourceChannel 1 (-1.5)≠0.753 := by
  have h:=actual_tanh_one_rigorous_rational_enclosure
  have hh:=actual_half_and_two_tanh_have_rigorous_rational_enclosures
  norm_num [sourceChannel,sourceBase,shifted,Real.tanh_neg]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first | (apply abs_lt.mpr; constructor <;> linarith) | (intro he; linarith) | linarith

theorem actual_full_block_sector_box_certificate_applies_to_all_offset_channels
    {n : Type*} [Fintype n] (centers v : n→ℝ)
    (Q : Matrix (n⊕n) (n⊕n) ℝ)
    (hQ : ∀ d : n→ℝ, (∀ i, 0≤d i ∧ d i≤1) →
      0≤ quadratic Q (Sum.elim v (fun i=>d i*v i))) :
    0≤quadratic Q (Sum.elim v (fun i=>shifted (centers i) (v i))) := by
  have hgain : ∀ i, ∃ d : ℝ, 0≤d ∧ d≤1 ∧ shifted (centers i) (v i)=d*v i := by
    intro i
    obtain ⟨d,hd0,hd1,hd⟩ :=
      (actual_every_shifted_channel_vanishes_and_has_own_valid_sector (centers i)).2.1 (v i) 0
    refine ⟨d,hd0,hd1,?_⟩
    simpa [shifted] using hd
  choose d hd0 hd1 he using hgain
  simpa only [←he] using hQ d (fun i=>⟨hd0 i,hd1 i⟩)

theorem actual_bias_free_tanh_two_layer_network_has_all_zero_equilibrium_preactivations
    {nx nu n1 n2 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (W2 : Matrix (Fin nu) (Fin n2) ℝ) :
    CompleteModulesNNTwoLayerLFT23.v1 W0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.w1 Real.tanh W0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.v2 Real.tanh W0 W1 0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.w2 Real.tanh W0 W1 0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.controller Real.tanh W0 W1 W2 0 0 0 (0 : Fin nx→ℝ)=0 := by
  simp [CompleteModulesNNTwoLayerLFT23.v1,CompleteModulesNNTwoLayerLFT23.w1,
    CompleteModulesNNTwoLayerLFT23.v2,CompleteModulesNNTwoLayerLFT23.w2,
    CompleteModulesNNTwoLayerLFT23.controller,CompleteModulesNNTwoLayerLFT23.activation,
    Function.comp_def]

end SafeLearning.CompleteModulesNNTanhOffset24
